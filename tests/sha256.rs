//! Prove knowledge of `R` such that `SHA256(R || puz) = Y`.
//!
//! - `R`   — **witness** (secret)
//! - `puz` — **public** puzzle bytes
//! - `Y`   — **public** SHA-256 digest
//!
//! # How to run
//!
//! ```bash
//! RUSTFLAGS="-C target-cpu=native" cargo test --release --test sha256 -- --nocapture
//! ```
//!
//! Benchmarks the same circuit on BLS12-381, BLS12-377, and BN254.
//!
//! # Public-input order
//!
//! `verify_proof` receives packed field elements in the **same order** the
//! circuit allocates them with `new_input` / `new_input_vec`:
//! first `puz`, then `Y`. Outside the circuit:
//!
//! ```text
//! public_inputs = puz.to_field_elements() || Y.to_field_elements()
//! ```

use ark_bls12_377::Bls12_377;
use ark_bls12_381::Bls12_381;
use ark_bn254::Bn254;
use ark_bpr20::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
};
use ark_crypto_primitives::crh::sha256::constraints::Sha256Gadget;
use ark_ec::pairing::Pairing;
use ark_ff::{PrimeField, ToConstraintField, Zero};
use ark_r1cs_std::prelude::*;
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError,
};
use ark_std::rand::Rng;
use ark_std::test_rng;
use sha2::{Digest, Sha256};
use std::thread;
use std::time::{Duration, Instant};

/// Fixed lengths ⇒ fixed circuit shape (one setup for all instances).
/// 16 + 16 = 32 bytes → one SHA-256 block after padding (quick stand-in for a
/// single compression; a real compression API would avoid the padding block).
const R_LEN: usize = 16;
const PUZ_LEN: usize = 16;
const SAMPLES: u32 = 15;
/// Pause between curves so the CPU can cool down before the next benchmark.
const COOLDOWN: Duration = Duration::from_secs(10);

/// Native SHA-256 of `R || puz` (used only to build concrete instances).
fn sha256_r_concat_puz(r: &[u8], puz: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(r);
    hasher.update(puz);
    let result = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&result);
    out
}

/// Pack public bytes the same way `UInt8::new_input_vec` does inside the circuit.
fn pack_public_inputs<F: PrimeField>(puz: &[u8], y: &[u8]) -> Vec<F> {
    let mut inputs: Vec<F> = puz.to_field_elements().unwrap();
    let y_fe: Vec<F> = y.to_field_elements().unwrap();
    inputs.extend(y_fe);
    inputs
}

/// Statement: knowledge of `R` s.t. SHA256(R || puz) = Y.
struct Sha256PuzzleCircuit {
    /// Secret randomness / preimage prefix. `None` during setup.
    r: Option<[u8; R_LEN]>,
    /// Public puzzle.
    puz: [u8; PUZ_LEN],
    /// Public digest Y = SHA256(R || puz).
    y: [u8; 32],
}

impl<F: PrimeField> ConstraintSynthesizer<F> for Sha256PuzzleCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        // 1. Secret R (witness only).
        //
        // Sha256Gadget::digest only takes `&[UInt8<_>]` — allocation is not in
        // its docs. Use `UInt8::new_witness_vec`, which wants one `Option<u8>`
        // per byte: `Some` when proving, `None` during setup (shape only).
        let r_vals: [Option<u8>; R_LEN] =
            self.r.map(|bytes| bytes.map(Some)).unwrap_or([None; R_LEN]);
        let r_vars = UInt8::new_witness_vec(cs.clone(), &r_vals)?;

        // 2. Public puz, then public Y (allocation order = verify order).
        let puz_vars = UInt8::new_input_vec(cs.clone(), &self.puz)?;
        let y_vars = UInt8::new_input_vec(cs.clone(), &self.y)?;

        // 3. Hash the concatenation R || puz and enforce equality with Y.
        let mut message = r_vars;
        message.extend(puz_vars);
        let hash = Sha256Gadget::digest(&message)?;
        hash.0.enforce_equal(&y_vars)?;

        Ok(())
    }
}

fn bench_sha256_curve<E: Pairing>(curve_name: &str) {
    let rng = &mut test_rng();

    let mut r = [0u8; R_LEN];
    let mut puz = [0u8; PUZ_LEN];
    rng.fill(&mut r);
    rng.fill(&mut puz);
    let y = sha256_r_concat_puz(&r, &puz);

    println!("\n========== {curve_name} ==========");
    println!("R   (secret, first 8) = {:02x?}", &r[..8]);
    println!("puz (public, first 8) = {:02x?}", &puz[..8]);
    println!("Y   (public digest)   = {:02x?}", &y[..]);

    let public_inputs = pack_public_inputs::<E::ScalarField>(&puz, &y);
    println!(
        "packed public inputs: {} Fr element(s) (puz then Y)",
        public_inputs.len()
    );

    {
        let cs = ConstraintSystem::<E::ScalarField>::new_ref();
        Sha256PuzzleCircuit { r: Some(r), puz, y }
            .generate_constraints(cs.clone())
            .unwrap();
        cs.finalize();
        println!("R1CS constraints: {}", cs.num_constraints());
        println!("instance vars:    {}", cs.num_instance_variables());
        println!("witness vars:     {}", cs.num_witness_variables());
        println!(
            "message length:   {} bytes (R || puz) → {} SHA-256 block(s) after padding",
            R_LEN + PUZ_LEN,
            // 64-byte message needs padding → two 64-byte blocks
            ((R_LEN + PUZ_LEN) + 9 + 63) / 64
        );
    }

    println!("\nSetup...");
    let setup_start = Instant::now();
    let params =
        generate_random_parameters::<E, _, _>(Sha256PuzzleCircuit { r: None, puz, y }, rng)
            .expect("setup");
    let setup_time = setup_start.elapsed();
    println!("setup time: {setup_time:?}");

    let pvk = prepare_verifying_key(&params.vk);

    let mut total_proving = Duration::ZERO;
    let mut total_verifying = Duration::ZERO;

    println!("\nProving ({SAMPLES} samples)...");
    for sample in 0..SAMPLES {
        let mut r = [0u8; R_LEN];
        let mut puz = [0u8; PUZ_LEN];
        rng.fill(&mut r);
        rng.fill(&mut puz);
        let y = sha256_r_concat_puz(&r, &puz);
        let public_inputs = pack_public_inputs::<E::ScalarField>(&puz, &y);

        let start = Instant::now();
        let proof = create_random_proof(Sha256PuzzleCircuit { r: Some(r), puz, y }, &params, rng)
            .expect("prove");
        let prove_dt = start.elapsed();
        total_proving += prove_dt;

        let start = Instant::now();
        assert!(
            verify_proof(&pvk, &proof, &public_inputs).unwrap(),
            "honest proof must verify"
        );
        let verify_dt = start.elapsed();
        total_verifying += verify_dt;

        println!("  sample {sample}: prove={prove_dt:?}, verify={verify_dt:?}");
    }

    // Reject wrong Y.
    {
        let mut r = [0u8; R_LEN];
        let mut puz = [0u8; PUZ_LEN];
        rng.fill(&mut r);
        rng.fill(&mut puz);
        let y = sha256_r_concat_puz(&r, &puz);
        let proof =
            create_random_proof(Sha256PuzzleCircuit { r: Some(r), puz, y }, &params, rng).unwrap();
        let mut bad = pack_public_inputs::<E::ScalarField>(&puz, &y);
        bad[0] = E::ScalarField::zero();
        assert!(!verify_proof(&pvk, &proof, &bad).unwrap());
        println!("reject on tampered public inputs ✓");
    }

    // Reject wrong puz (same R/Y would not match H(R||puz')).
    {
        let mut r = [0u8; R_LEN];
        let mut puz = [0u8; PUZ_LEN];
        rng.fill(&mut r);
        rng.fill(&mut puz);
        let y = sha256_r_concat_puz(&r, &puz);
        let proof =
            create_random_proof(Sha256PuzzleCircuit { r: Some(r), puz, y }, &params, rng).unwrap();
        let mut wrong_puz = puz;
        wrong_puz[0] ^= 1;
        let bad = pack_public_inputs::<E::ScalarField>(&wrong_puz, &y);
        assert!(!verify_proof(&pvk, &proof, &bad).unwrap());
        println!("reject on wrong puz ✓");
    }

    let proving_avg = total_proving / SAMPLES;
    let verifying_avg = total_verifying / SAMPLES;
    println!("\n=== SHA256(R || puz) = Y (BPR20 / {curve_name}) ===");
    println!("|R|={R_LEN}, |puz|={PUZ_LEN}");
    println!("setup:              {setup_time:?}");
    println!("avg prove ({SAMPLES}x):   {proving_avg:?}");
    println!("avg verify ({SAMPLES}x): {verifying_avg:?}");
}

#[test]
fn test_sha256_r_concat_puz_prove_time() {
    bench_sha256_curve::<Bls12_381>("BLS12-381");

    println!("\nCooling down for {COOLDOWN:?} before next curve...");
    thread::sleep(COOLDOWN);

    bench_sha256_curve::<Bls12_377>("BLS12-377");

    println!("\nCooling down for {COOLDOWN:?} before next curve...");
    thread::sleep(COOLDOWN);

    bench_sha256_curve::<Bn254>("BN254");
}
