use ark_ec::{pairing::Pairing, scalar_mul::BatchMulPreprocessing, AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_std::ops::Mul;

use super::{PreparedVerifyingKey, Proof, VerifyingKey};
use crate::prover::fiat_shamir_challenge;

use ark_relations::gr1cs::{Result as R1CSResult, SynthesisError};

use ark_std::vec::Vec;
use core::ops::{AddAssign, Neg};

/// Prepare the verifying key `vk` for use in proof verification.
pub fn prepare_verifying_key<E: Pairing>(vk: &VerifyingKey<E>) -> PreparedVerifyingKey<E> {
    PreparedVerifyingKey {
        vk: vk.clone(),
        gamma_g2_neg_pc: vk.gamma_g2.into_group().neg().into_affine().into(),
    }
}

/// Prepare proof inputs for use with [`verify_proof_with_prepared_inputs`].
pub fn prepare_inputs<E: Pairing>(
    pvk: &PreparedVerifyingKey<E>,
    public_inputs: &[E::ScalarField],
) -> R1CSResult<E::G1> {
    if (public_inputs.len() + 1) != pvk.vk.gamma_abc_g1.len() {
        return Err(SynthesisError::Unsatisfiable);
    }

    let mut g_ic = pvk.vk.gamma_abc_g1[0].into_group();
    for (i, b) in public_inputs.iter().zip(pvk.vk.gamma_abc_g1.iter().skip(1)) {
        g_ic.add_assign(&b.mul_bigint(i.into_bigint()));
    }

    Ok(g_ic)
}

/// Verify a proof against the prepared verification key and prepared public inputs.
pub fn verify_proof_with_prepared_inputs<E: Pairing>(
    pvk: &PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    prepared_inputs: &E::G1,
) -> R1CSResult<bool> {
    let m_fr = fiat_shamir_challenge::<E>(&proof.a, &proof.b, &proof.delta_prime);

    let mut delta_prime_delta_m = pvk.vk.delta_g2.mul(m_fr);
    delta_prime_delta_m += &proof.delta_prime;

    let qap = E::multi_miller_loop(
        [
            <E::G1Affine as Into<E::G1Prepared>>::into(proof.a),
            prepared_inputs.into_affine().into(),
            proof.c.into(),
        ],
        [
            proof.b.into(),
            pvk.gamma_g2_neg_pc.clone(),
            delta_prime_delta_m.neg().into_affine().into(),
        ],
    );

    let test = E::final_exponentiation(qap).unwrap();

    Ok(test.0 == pvk.vk.alpha_g1_beta_g2)
}

/// Verify a proof against the prepared verification key and public inputs.
pub fn verify_proof<E: Pairing>(
    pvk: &PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::ScalarField],
) -> R1CSResult<bool> {
    let prepared_inputs = prepare_inputs(pvk, public_inputs)?;
    verify_proof_with_prepared_inputs(pvk, proof, &prepared_inputs)
}

/// Verify a vector of proofs against prepared inputs.
pub fn vec_verify_proof_with_prepared_inputs<E: Pairing>(
    pvk: &PreparedVerifyingKey<E>,
    proofs: &Vec<Proof<E>>,
    prepared_inputs: &Vec<E::G1>,
) -> R1CSResult<bool> {
    let num_proofs = proofs.len();
    let mut m_fr: Vec<E::ScalarField> = Vec::with_capacity(num_proofs);

    let start = ark_std::time::Instant::now();
    for proof in proofs.iter() {
        m_fr.push(fiat_shamir_challenge::<E>(
            &proof.a,
            &proof.b,
            &proof.delta_prime,
        ));
    }

    let table = BatchMulPreprocessing::new(pvk.vk.delta_g2.into_group(), num_proofs);
    let elem_g2 = table.batch_mul(&m_fr);

    println!(
        "Hashing + Exponentiation (G2) time is {}ns per proof doing {} exponentiations",
        start.elapsed().as_nanos() / num_proofs as u128,
        num_proofs
    );

    let mut bool_results: Vec<_> = Vec::new();
    for ((x, y), z) in elem_g2
        .iter()
        .zip(proofs.iter())
        .zip(prepared_inputs.iter())
    {
        let delta_term = (x.into_group() + y.delta_prime.into_group())
            .neg()
            .into_affine();
        let tmp1 = E::final_exponentiation(E::multi_miller_loop(
            [
                <E::G1Affine as Into<E::G1Prepared>>::into(y.a),
                z.into_affine().into(),
                y.c.into(),
            ],
            [y.b.into(), pvk.gamma_g2_neg_pc.clone(), delta_term.into()],
        ))
        .unwrap();
        let tmp = tmp1.0 == pvk.vk.alpha_g1_beta_g2;
        bool_results.push(tmp);
    }

    let result = bool_results.iter().fold(true, |total, next| total && *next);
    Ok(result)
}

/// Verify a vector of proofs against public inputs.
pub fn vec_verify_proof<E: Pairing>(
    vk: &VerifyingKey<E>,
    proofs: &Vec<Proof<E>>,
    public_inputs: &Vec<Vec<E::ScalarField>>,
) -> R1CSResult<bool> {
    let mut prepared_inputs: Vec<_> = Vec::new();
    for pub_input in public_inputs.iter() {
        let pvk = prepare_verifying_key(vk);
        prepared_inputs.push(prepare_inputs(&pvk, pub_input)?);
    }
    let pvk = prepare_verifying_key(vk);
    vec_verify_proof_with_prepared_inputs(&pvk, proofs, &prepared_inputs)
}
