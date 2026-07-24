//! Minimal SHA-256 preimage proof with BPR20, plus timing.
//!
//! # What you are proving
//!
//! Knowledge of a secret `preimage` such that
//! `SHA256(preimage) = digest`, where `digest` is public.
//!
//! # How to run (release + print timings)
//!
//! ```bash
//! cargo test --release --features "std r1cs" --test sha256 -- --nocapture
//! ```
//!
//! # Pipeline (read top-to-bottom with the code below)
//!
//! 1. **ConstraintSynthesizer** — describe the statement as R1CS equations.
//! 2. **Setup** — `generate_random_parameters` builds keys from the circuit *shape*.
//! 3. **Prove** — `create_random_proof` with a filled-in witness.
//! 4. **Verify** — `verify_proof` with packed public field elements only.
//!
//! A SNARK does not “run SHA256 like normal Rust.” It proves that a system of
//! equations has a solution. Gadgets (`UInt8`, `Sha256Gadget`) build those
//! equations for you.

use ark_bls12_377::{Bls12_377, Fr};
use ark_bpr20::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
};
use ark_crypto_primitives::crh::sha256::constraints::Sha256Gadget;
use ark_ff::{ToConstraintField, Zero};
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError,
};
use ark_std::rand::Rng;
use ark_std::test_rng;
use sha2::{Digest, Sha256};
use std::time::{Duration, Instant};

/// Fixed preimage length ⇒ fixed circuit shape (required for one-time setup).
const PREIMAGE_LEN: usize = 32;

/// Native SHA-256 used only to build a concrete instance outside the circuit.
fn sha256_hash(preimage: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(preimage);
    let result = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&result);
    out
}

/// The circuit / statement.
///
/// - `preimage`: **witness** (secret). `None` during setup, `Some` when proving.
/// - `digest`: **public input**. Verifier knows this; prover must match it.
///
/// Implementing `ConstraintSynthesizer` means: given a constraint system `cs`,
/// allocate variables and enforce equations. Setup and prove both call this.
struct Sha256PreimageCircuit {
    preimage: Option<[u8; PREIMAGE_LEN]>,
    digest: [u8; 32],
}

impl ConstraintSynthesizer<Fr> for Sha256PreimageCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // ------------------------------------------------------------------
        // 1. Allocate the SECRET preimage as witness variables.
        //    These never appear in verify_proof's public_inputs slice.
        // ------------------------------------------------------------------
        let preimage_slots: [Option<u8>; PREIMAGE_LEN] = match self.preimage {
            Some(bytes) => {
                let mut slots = [None; PREIMAGE_LEN];
                for (slot, b) in slots.iter_mut().zip(bytes.iter()) {
                    *slot = Some(*b);
                }
                slots
            }
            // Setup path: no assignment yet; shape of the circuit still exists.
            None => [None; PREIMAGE_LEN],
        };
        let preimage_vars = UInt8::new_witness_vec(cs.clone(), &preimage_slots)?;

        // ------------------------------------------------------------------
        // 2. Allocate the PUBLIC digest.
        //    `new_input_vec` packs bytes into field elements (not 1 Fr per byte).
        //    That packing is exactly what verify_proof must receive later.
        // ------------------------------------------------------------------
        let digest_vars = UInt8::new_input_vec(cs.clone(), &self.digest)?;

        // ------------------------------------------------------------------
        // 3. Enforce SHA256(preimage) == digest inside R1CS.
        //    Sha256Gadget adds ~tens of thousands of constraints for one block.
        // ------------------------------------------------------------------
        let hash = Sha256Gadget::digest(&preimage_vars)?;
        hash.0.enforce_equal(&digest_vars)?;

        Ok(())
    }
}

#[test]
fn test_sha256_preimage_prove_time() {
    let rng = &mut test_rng();

    // Concrete instance: pick a secret, hash it in plain Rust.
    let mut preimage = [0u8; PREIMAGE_LEN];
    rng.fill(&mut preimage);
    let digest = sha256_hash(&preimage);

    println!("preimage (secret, first 8 bytes) = {:02x?}", &preimage[..8]);
    println!("digest   (public)                = {:02x?}", &digest[..]);

    // ----------------------------------------------------------------------
    // Public inputs for the verifier.
    //
    // Because we used UInt8::new_input_vec, public inputs are *packed* Frs.
    // On BLS12-377, CAPACITY/8 = 31, so 32 digest bytes → 2 field elements.
    // Passing one Fr per byte (or raw bytes) would make verification fail.
    // ----------------------------------------------------------------------
    let public_inputs: Vec<Fr> = digest.to_field_elements().unwrap();
    println!(
        "packed public inputs: {} Fr element(s)",
        public_inputs.len()
    );
    for (i, fe) in public_inputs.iter().enumerate() {
        println!("  public_inputs[{i}] = {fe}");
    }

    // Constraint count (dry synthesize with a real witness).
    {
        let cs = ConstraintSystem::<Fr>::new_ref();
        Sha256PreimageCircuit {
            preimage: Some(preimage),
            digest,
        }
        .generate_constraints(cs.clone())
        .unwrap();
        cs.finalize();
        println!("R1CS constraints: {}", cs.num_constraints());
        println!("instance vars:    {}", cs.num_instance_variables());
        println!("witness vars:     {}", cs.num_witness_variables());
    }

    // ----------------------------------------------------------------------
    // SETUP — circuit shape only (`preimage: None`). Produces proving key + VK.
    // Expensive; do once per circuit shape and reuse.
    // ----------------------------------------------------------------------
    println!("\nSetup...");
    let setup_start = Instant::now();
    let params = generate_random_parameters::<Bls12_377, _, _>(
        Sha256PreimageCircuit {
            preimage: None,
            digest,
        },
        rng,
    )
    .expect("setup");
    let setup_time = setup_start.elapsed();
    println!("setup time: {setup_time:?}");

    let pvk = prepare_verifying_key(&params.vk);

    // ----------------------------------------------------------------------
    // PROVE / VERIFY loop — time the prove path (what we care about).
    // SHA-256 circuits are heavy; keep sample count small.
    // ----------------------------------------------------------------------
    const SAMPLES: u32 = 5;
    let mut total_proving = Duration::ZERO;
    let mut total_verifying = Duration::ZERO;

    println!("\nProving ({SAMPLES} samples)...");
    for sample in 0..SAMPLES {
        // Fresh random preimage each sample (same circuit shape).
        let mut preimage = [0u8; PREIMAGE_LEN];
        rng.fill(&mut preimage);
        let digest = sha256_hash(&preimage);
        let public_inputs: Vec<Fr> = digest.to_field_elements().unwrap();

        let start = Instant::now();
        let proof = create_random_proof(
            Sha256PreimageCircuit {
                preimage: Some(preimage),
                digest,
            },
            &params,
            rng,
        )
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

    // Sanity: wrong public input must reject.
    {
        let mut preimage = [0u8; PREIMAGE_LEN];
        rng.fill(&mut preimage);
        let digest = sha256_hash(&preimage);
        let proof = create_random_proof(
            Sha256PreimageCircuit {
                preimage: Some(preimage),
                digest,
            },
            &params,
            rng,
        )
        .unwrap();
        let mut bad = digest.to_field_elements().unwrap();
        bad[0] = Fr::zero();
        assert!(!verify_proof(&pvk, &proof, &bad).unwrap());
        println!("reject on tampered public inputs ✓");
    }

    let proving_avg = total_proving / SAMPLES;
    let verifying_avg = total_verifying / SAMPLES;
    println!("\n=== SHA256 preimage (BPR20 / BLS12-377) ===");
    println!("setup:              {setup_time:?}");
    println!("avg prove ({SAMPLES}x):   {proving_avg:?}");
    println!("avg verify ({SAMPLES}x): {verifying_avg:?}");
}
