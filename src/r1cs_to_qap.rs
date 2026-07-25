use ark_ff::PrimeField;
use ark_poly::EvaluationDomain;
use ark_std::{cfg_iter_mut, vec};

use crate::Vec;
use ark_relations::gr1cs::{
    ConstraintSystemRef, Result as R1CSResult, SynthesisError, R1CS_PREDICATE_LABEL,
};
use core::ops::Deref;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[inline]
fn evaluate_constraint<F: PrimeField>(terms: &[(F, usize)], assignment: &[F]) -> F {
    #[cfg(feature = "parallel")]
    if terms.len() < 100 {
        serial_evaluate_constraint(terms, assignment)
    } else {
        terms
            .par_iter()
            .map(|(coeff, index)| {
                let val = assignment[*index];
                if coeff.is_one() {
                    val
                } else {
                    val * coeff
                }
            })
            .sum()
    }
    #[cfg(not(feature = "parallel"))]
    serial_evaluate_constraint(terms, assignment)
}

fn serial_evaluate_constraint<F: PrimeField>(terms: &[(F, usize)], assignment: &[F]) -> F {
    let mut sum = F::zero();
    for chunk in terms.chunks(4) {
        let chunk_sum = chunk
            .iter()
            .map(|(coeff, index)| {
                let val = assignment[*index];
                if coeff.is_one() {
                    val
                } else {
                    val * coeff
                }
            })
            .sum::<F>();
        sum += chunk_sum;
    }
    sum
}

pub(crate) struct R1CStoQAP;

impl R1CStoQAP {
    #[inline]
    #[allow(clippy::type_complexity)]
    pub(crate) fn instance_map_with_evaluation<F: PrimeField, D: EvaluationDomain<F>>(
        cs: ConstraintSystemRef<F>,
        t: &F,
    ) -> R1CSResult<(Vec<F>, Vec<F>, Vec<F>, F, usize, usize)> {
        let matrices = &cs.to_matrices().unwrap()[R1CS_PREDICATE_LABEL];
        let domain_size = cs.num_constraints() + cs.num_instance_variables();
        let domain = D::new(domain_size).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_size = domain.size();

        let zt = domain.evaluate_vanishing_polynomial(*t);

        let coefficients_time = start_timer!(|| "Evaluate Lagrange coefficients");
        let u = domain.evaluate_all_lagrange_coefficients(*t);
        end_timer!(coefficients_time);

        let qap_num_variables = (cs.num_instance_variables() - 1) + cs.num_witness_variables();

        let mut a = vec![F::zero(); qap_num_variables + 1];
        let mut b = vec![F::zero(); qap_num_variables + 1];
        let mut c = vec![F::zero(); qap_num_variables + 1];

        {
            let start = 0;
            let end = cs.num_instance_variables();
            let num_constraints = cs.num_constraints();
            a[start..end].copy_from_slice(&u[(start + num_constraints)..(end + num_constraints)]);
        }

        for (i, u_i) in u.iter().enumerate().take(cs.num_constraints()) {
            for &(ref coeff, index) in &matrices[0][i] {
                a[index] += &(*u_i * coeff);
            }
            for &(ref coeff, index) in &matrices[1][i] {
                b[index] += &(*u_i * coeff);
            }
            for &(ref coeff, index) in &matrices[2][i] {
                c[index] += &(*u_i * coeff);
            }
        }

        Ok((a, b, c, zt, qap_num_variables, domain_size))
    }

    #[inline]
    pub(crate) fn witness_map<F: PrimeField, D: EvaluationDomain<F>>(
        prover: ConstraintSystemRef<F>,
    ) -> R1CSResult<Vec<F>> {
        let matrices = &prover.to_matrices().unwrap()[R1CS_PREDICATE_LABEL];
        let num_inputs = prover.num_instance_variables();
        let num_constraints = prover.num_constraints();
        let cs = prover.borrow().unwrap();
        let prover = cs.deref();

        let full_assignment = [
            prover.instance_assignment().unwrap(),
            prover.witness_assignment().unwrap(),
        ]
        .concat();

        let domain =
            D::new(num_constraints + num_inputs).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_size = domain.size();
        let zero = F::zero();

        let mut a = vec![zero; domain_size];
        let mut b = vec![zero; domain_size];

        cfg_iter_mut!(a[..num_constraints])
            .zip(&mut b[..num_constraints])
            .zip(&matrices[0])
            .zip(&matrices[1])
            .for_each(|(((a, b), at_i), bt_i)| {
                *a = evaluate_constraint(&at_i, &full_assignment);
                *b = evaluate_constraint(&bt_i, &full_assignment);
            });

        {
            let start = num_constraints;
            let end = start + num_inputs;
            a[start..end].clone_from_slice(&full_assignment[..num_inputs]);
        }

        domain.ifft_in_place(&mut a);
        domain.ifft_in_place(&mut b);

        let coset_domain = domain.get_coset(F::GENERATOR).unwrap();

        coset_domain.fft_in_place(&mut a);
        coset_domain.fft_in_place(&mut b);

        let mut ab = domain.mul_polynomials_in_evaluation_domain(&a, &b);
        drop(a);
        drop(b);

        let mut c = vec![zero; domain_size];
        cfg_iter_mut!(c[..num_constraints])
            .enumerate()
            .for_each(|(i, c)| {
                *c = evaluate_constraint(&matrices[2][i], &full_assignment);
            });

        domain.ifft_in_place(&mut c);
        coset_domain.fft_in_place(&mut c);

        let vanishing_polynomial_over_coset = domain
            .evaluate_vanishing_polynomial(F::GENERATOR)
            .inverse()
            .unwrap();
        cfg_iter_mut!(ab).zip(c).for_each(|(ab_i, c_i)| {
            *ab_i -= &c_i;
            *ab_i *= &vanishing_polynomial_over_coset;
        });

        coset_domain.ifft_in_place(&mut ab);

        Ok(ab)
    }
}
