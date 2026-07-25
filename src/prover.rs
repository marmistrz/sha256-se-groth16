use crate::{r1cs_to_qap::R1CStoQAP, Proof, ProvingKey};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{Field, PrimeField, UniformRand, Zero, One};
use ark_std::ops::Mul;
use ark_poly::GeneralEvaluationDomain;
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, OptimizationGoal, Result as R1CSResult,
    SynthesisMode,
};
use ark_serialize::CanonicalSerialize;
use ark_std::rand::Rng;
use ark_std::{cfg_into_iter, cfg_iter, vec::Vec};

use blake2::{Blake2b512, Digest};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Fiat–Shamir challenge from (A, B, δ').
pub(crate) fn fiat_shamir_challenge<E: Pairing>(
    a: &E::G1Affine,
    b: &E::G2Affine,
    delta_prime: &E::G2Affine,
) -> E::ScalarField {
    let mut hasher = Blake2b512::new();
    let mut bytes = Vec::new();
    a.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);
    bytes.clear();
    b.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);
    bytes.clear();
    delta_prime.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);
    E::ScalarField::from_le_bytes_mod_order(&hasher.finalize())
}

/// Create a proof that is zero-knowledge.
/// This method samples randomness for zero knowledges via `rng`.
#[inline]
pub fn create_random_proof<E, C, R>(
    circuit: C,
    pk: &ProvingKey<E>,
    rng: &mut R,
) -> R1CSResult<Proof<E>>
where
    E: Pairing,
    C: ConstraintSynthesizer<E::ScalarField>,
    R: Rng,
{
    let r = E::ScalarField::rand(rng);
    let s = E::ScalarField::rand(rng);
    let mut zeta = E::ScalarField::zero();
    while zeta.is_zero() {
        zeta = E::ScalarField::rand(rng);
    }

    create_proof::<E, C>(circuit, pk, r, s, zeta)
}

/// Create a proof that is *not* zero-knowledge.
#[inline]
pub fn create_proof_no_zk<E, C>(circuit: C, pk: &ProvingKey<E>) -> R1CSResult<Proof<E>>
where
    E: Pairing,
    C: ConstraintSynthesizer<E::ScalarField>,
{
    create_proof::<E, C>(
        circuit,
        pk,
        E::ScalarField::zero(),
        E::ScalarField::zero(),
        E::ScalarField::one(),
    )
}

/// Create a proof using randomness `r`, `s`, and `zeta`.
#[inline]
pub fn create_proof<E, C>(
    circuit: C,
    pk: &ProvingKey<E>,
    r: E::ScalarField,
    s: E::ScalarField,
    zeta: E::ScalarField,
) -> R1CSResult<Proof<E>>
where
    E: Pairing,
    C: ConstraintSynthesizer<E::ScalarField>,
{
    type D<F> = GeneralEvaluationDomain<F>;

    let prover_time = start_timer!(|| "BPR20::Prover");
    let cs = ConstraintSystem::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    cs.set_mode(SynthesisMode::Prove {
        construct_matrices: true,
        generate_lc_assignments: false,
    });

    let synthesis_time = start_timer!(|| "Constraint synthesis");
    circuit.generate_constraints(cs.clone())?;
    end_timer!(synthesis_time);

    let lc_time = start_timer!(|| "Inlining LCs");
    cs.finalize();
    end_timer!(lc_time);

    debug_assert!(cs.is_satisfied().unwrap());

    let witness_map_time = start_timer!(|| "R1CS to QAP witness map");
    let h = R1CStoQAP::witness_map::<E::ScalarField, D<E::ScalarField>>(cs.clone())?;
    end_timer!(witness_map_time);

    let c_acc_time = start_timer!(|| "Compute C");
    let prover = cs.borrow().unwrap();
    let witness_assignment = prover.witness_assignment().unwrap();
    let instance_assignment = prover.instance_assignment().unwrap();

    let aux_assignment = cfg_iter!(witness_assignment)
        .map(|s| s.into_bigint())
        .collect::<Vec<_>>();

    let delta_prime_g1 = pk.delta_g1.mul(zeta).into_affine();
    let delta_prime_g2 = pk.vk.delta_g2.mul(zeta).into_affine();

    let r_s_delta_g1 = delta_prime_g1.mul(r * s);
    end_timer!(c_acc_time);

    let input_assignment = instance_assignment[1..]
        .iter()
        .map(|s| s.into_bigint())
        .collect::<Vec<_>>();

    let assignment = [&input_assignment[..], &aux_assignment[..]].concat();
    drop(aux_assignment);

    let a_acc_time = start_timer!(|| "Compute A");
    let r_g1 = delta_prime_g1.mul(r);
    let g_a = calculate_coeff(r_g1, &pk.a_query, pk.vk.alpha_g1, &assignment);
    let s_g_a = g_a * &s;
    end_timer!(a_acc_time);

    let g1_b = if !r.is_zero() {
        let b_g1_acc_time = start_timer!(|| "Compute B in G1");
        let s_g1 = delta_prime_g1.mul(s);
        let g1_b = calculate_coeff(s_g1, &pk.b_g1_query, pk.beta_g1, &assignment);
        end_timer!(b_g1_acc_time);
        g1_b
    } else {
        E::G1::zero()
    };

    let b_g2_acc_time = start_timer!(|| "Compute B in G2");
    let s_g2 = delta_prime_g2.mul(s);
    let g2_b = calculate_coeff(s_g2, &pk.b_g2_query, pk.vk.beta_g2, &assignment);
    let r_g1_b = g1_b * &r;
    drop(assignment);
    end_timer!(b_g2_acc_time);

    let c_time = start_timer!(|| "Finish C");
    let a_affine = g_a.into_affine();
    let b_affine = g2_b.into_affine();
    let m_fr = fiat_shamir_challenge::<E>(&a_affine, &b_affine, &delta_prime_g2);
    let factor = zeta * (zeta + m_fr).inverse().unwrap();
    let zeta_m_inv = (zeta + m_fr).inverse().unwrap();

    let h_assignment = cfg_into_iter!(h)
        .map(|s| (s * zeta_m_inv).into_bigint())
        .collect::<Vec<_>>();
    let h_acc = E::G1::msm_bigint(&pk.h_query, &h_assignment);
    let aux_assignment_unscaled = cfg_iter!(witness_assignment)
        .map(|s| (*s * zeta_m_inv).into_bigint())
        .collect::<Vec<_>>();
    let l_aux_acc = E::G1::msm_bigint(&pk.l_query, &aux_assignment_unscaled);

    let mut g_c = s_g_a * &factor;
    g_c += &(r_g1_b * &factor);
    g_c -= &(r_s_delta_g1 * &factor);
    g_c += &l_aux_acc;
    g_c += &h_acc;
    end_timer!(c_time);

    end_timer!(prover_time);

    Ok(Proof {
        a: a_affine,
        b: b_affine,
        c: g_c.into_affine(),
        delta_prime: delta_prime_g2,
    })
}

fn calculate_coeff<G: AffineRepr>(
    initial: G::Group,
    query: &[G],
    vk_param: G,
    assignment: &[<G::ScalarField as PrimeField>::BigInt],
) -> G::Group
where
    G::Group: VariableBaseMSM,
{
    let el = query[0];
    let acc = G::Group::msm_bigint(&query[1..], assignment);

    let mut res = initial;
    res += &el;
    res += &acc;
    res += &vk_param;

    res
}
