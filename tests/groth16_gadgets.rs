use ark_ff::PrimeField;
use ark_groth16::{Groth16, ProvingKey, VerifyingKey};
use proptest::prelude::*;

use ark_r1cs_std::{
    prelude::{AllocVar, CurveVar, EqGadget},
    uint8::UInt8,
    ToBitsGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ToConstraintField};
use ark_snark::SNARK;
use decaf377::{
    basepoint,
    r1cs::{ElementVar, FqVar},
    Bls12_377, Element, Fq, Fr,
};
use rand_core::OsRng;

struct DiscreteLogCircuit {
    // Witness
    scalar: [u8; 32],

    // Public input
    pub public: Element,
}

impl ConstraintSynthesizer<Fq> for DiscreteLogCircuit {
    fn generate_constraints(
        self,
        cs: ark_relations::r1cs::ConstraintSystemRef<Fq>,
    ) -> ark_relations::r1cs::Result<()> {
        // 1. Add witness variable
        let witness_vars = UInt8::new_witness_vec(cs.clone(), &self.scalar)?;

        // 2. Add public input variable
        let public_var = ElementVar::new_input(cs.clone(), || Ok(self.public))?;
        let basepoint_var = ElementVar::new_constant(cs, basepoint())?;
        // 3. Add constraint that scalar * Basepoint = public
        let test_public = basepoint_var.scalar_mul_le(witness_vars.to_bits_le()?.iter())?;
        public_var.enforce_equal(&test_public)?;

        Ok(())
    }
}

impl DiscreteLogCircuit {
    fn generate_test_parameters() -> (ProvingKey<Bls12_377>, VerifyingKey<Bls12_377>) {
        let scalar = [0u8; 32];
        let public = Element::default();
        let circuit = DiscreteLogCircuit { scalar, public };
        let (pk, vk) = Groth16::circuit_specific_setup(circuit, &mut OsRng)
            .expect("can perform circuit specific setup");
        (pk, vk)
    }
}

fn scalar_strategy_random() -> BoxedStrategy<[u8; 32]> {
    any::<[u8; 32]>().prop_map(|x| x).boxed()
}

proptest! {
#![proptest_config(ProptestConfig::with_cases(5))]
#[test]
fn groth16_dl_proof_happy_path(scalar_arr in scalar_strategy_random()) {
        let (pk, vk) = DiscreteLogCircuit::generate_test_parameters();
        let mut rng = OsRng;

        let scalar = scalar_arr;
        let public = Fr::from_le_bytes_mod_order(&scalar_arr[..]) * basepoint();

        // Prover POV
        let circuit = DiscreteLogCircuit { scalar, public };
        let proof = Groth16::prove(&pk, circuit, &mut rng)
            .map_err(|_| anyhow::anyhow!("invalid proof"))
            .expect("can generate proof");

        // Verifier POV
        let processed_pvk = Groth16::process_vk(&vk).expect("can process verifying key");
        let public_inputs = public.to_field_elements().unwrap();
        let proof_result =
            Groth16::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

        assert!(proof_result);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(5))]
    #[test]
    fn groth16_dl_proof_unhappy_path(scalar_arr in scalar_strategy_random()) {
        let (pk, vk) = DiscreteLogCircuit::generate_test_parameters();
        let mut rng = OsRng;

        let scalar = scalar_arr;
        let public = Fr::from_le_bytes_mod_order(&scalar_arr[..]) * basepoint();

        let wrong_public = Fr::from(666) * basepoint();

        // Prover POV
        let circuit = DiscreteLogCircuit { scalar, public };
        let proof = Groth16::prove(&pk, circuit, &mut rng)
            .map_err(|_| anyhow::anyhow!("invalid proof"))
            .expect("can generate proof");

        // Verifier POV
        let processed_pvk = Groth16::process_vk(&vk).expect("can process verifying key");
        let public_inputs = wrong_public.to_field_elements().unwrap();
        let proof_result =
            Groth16::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

        assert!(!proof_result);
    }
}

struct CompressionCircuit {
    // Witness
    point: Element,

    // Public input
    pub field_element: Fq,
}

impl ConstraintSynthesizer<Fq> for CompressionCircuit {
    fn generate_constraints(
        self,
        cs: ark_relations::r1cs::ConstraintSystemRef<Fq>,
    ) -> ark_relations::r1cs::Result<()> {
        // 1. Add witness variable
        let witness_var = ElementVar::new_witness(cs.clone(), || Ok(self.point))?;

        // 2. Add public input variable
        let public_var = FqVar::new_input(cs, || Ok(self.field_element))?;

        // 3. Add compression constraints
        let test_public = witness_var.compress_to_field(self.point)?;
        public_var.enforce_equal(&test_public)?;

        Ok(())
    }
}

impl CompressionCircuit {
    fn generate_test_parameters() -> (ProvingKey<Bls12_377>, VerifyingKey<Bls12_377>) {
        //let point = Fr::from(100) * decaf377::basepoint();
        let point = Fr::from(2) * decaf377::basepoint();
        //let point = Element::default();
        let field_element = point.vartime_compress_to_field();
        let circuit = CompressionCircuit {
            point,
            field_element,
        };
        let (pk, vk) = Groth16::circuit_specific_setup(circuit, &mut OsRng)
            .expect("can perform circuit specific setup");
        (pk, vk)
    }
}

proptest! {
#![proptest_config(ProptestConfig::with_cases(10))]
#[test]
    fn groth16_compression_proof_happy_path(scalar in (1..65536)) {
        let (pk, vk) = CompressionCircuit::generate_test_parameters();
        let mut rng = OsRng;

        // Prover POV
        let point = Fr::from(scalar) * decaf377::basepoint();
        let field_element = point.vartime_compress_to_field();
        let circuit = CompressionCircuit {
            point,
            field_element,
        };
        let proof = Groth16::prove(&pk, circuit, &mut rng)
            .map_err(|_| anyhow::anyhow!("invalid proof"))
            .expect("can generate proof");

        // Verifier POV
        let processed_pvk = Groth16::process_vk(&vk).expect("can process verifying key");
        let public_inputs = field_element.to_field_elements().unwrap();
        let proof_result =
            Groth16::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

        assert!(proof_result);
    }
}

proptest! {
#![proptest_config(ProptestConfig::with_cases(10))]
#[test]
    fn groth16_compression_proof_unhappy_path(scalar in (1..65536)) {
        let (pk, vk) = CompressionCircuit::generate_test_parameters();
        let mut rng = OsRng;

        // Prover POV
        let point = Fr::from(scalar) * decaf377::basepoint();
        let field_element = point.vartime_compress_to_field();
        let circuit = CompressionCircuit {
            point,
            field_element,
        };
        let proof = Groth16::prove(&pk, circuit, &mut rng)
            .map_err(|_| anyhow::anyhow!("invalid proof"))
            .expect("can generate proof");

        // Verifier POV
        let processed_pvk = Groth16::process_vk(&vk).expect("can process verifying key");
        let wrong_scalar = scalar + 1;
        let public_inputs = (Fq::from(wrong_scalar)).to_field_elements().unwrap();
        let proof_result =
            Groth16::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

        assert!(!proof_result);
    }
}

struct DecompressionCircuit {
    // Witness
    field_element: Fq,

    // Public input
    pub point: Element,
}

impl ConstraintSynthesizer<Fq> for DecompressionCircuit {
    fn generate_constraints(
        self,
        cs: ark_relations::r1cs::ConstraintSystemRef<Fq>,
    ) -> ark_relations::r1cs::Result<()> {
        // 1. Add witness variable
        let witness_var = FqVar::new_witness(cs.clone(), || Ok(self.field_element))?;

        // 2. Add public input variable
        let public_var = ElementVar::new_input(cs, || Ok(self.point))?;

        // 3. Add decompression constraints
        let test_public = ElementVar::decompress_from_field(witness_var, self.field_element)?;
        public_var.enforce_equal(&test_public)?;

        Ok(())
    }
}

impl DecompressionCircuit {
    fn generate_test_parameters() -> (ProvingKey<Bls12_377>, VerifyingKey<Bls12_377>) {
        let point = Fr::from(100) * decaf377::basepoint();
        let field_element = point.vartime_compress_to_field();
        let circuit = DecompressionCircuit {
            point,
            field_element,
        };
        let (pk, vk) = Groth16::circuit_specific_setup(circuit, &mut OsRng)
            .expect("can perform circuit specific setup");
        (pk, vk)
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]
    #[test]
        fn groth16_decompression_proof_happy_path(scalar in (1..65536)) {
            let (pk, vk) = DecompressionCircuit::generate_test_parameters();
            let mut rng = OsRng;

            // Prover POV
            let point = Fr::from(scalar) * decaf377::basepoint();
    let field_element = point.vartime_compress_to_field();
    let circuit = DecompressionCircuit {
        point,
        field_element,
    };
    let proof = Groth16::prove(&pk, circuit, &mut rng)
        .map_err(|_| anyhow::anyhow!("invalid proof"))
        .expect("can generate proof");

    // Verifier POV
    let processed_pvk = Groth16::process_vk(&vk).expect("can process verifying key");
    let public_inputs = point.to_field_elements().unwrap();
    let proof_result =
        Groth16::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

    assert!(proof_result);
}
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]
    #[test]
        fn groth16_decompression_proof_unhappy_path(scalar in (1..65536)) {
            let (pk, vk) = DecompressionCircuit::generate_test_parameters();
            let mut rng = OsRng;

            // Prover POV
            let point = Fr::from(scalar) * decaf377::basepoint();
    let field_element = point.vartime_compress_to_field();
    let circuit = DecompressionCircuit {
        point,
        field_element,
    };
    let proof = Groth16::prove(&pk, circuit, &mut rng)
        .map_err(|_| anyhow::anyhow!("invalid proof"))
        .expect("can generate proof");

    // Verifier POV
    let processed_pvk = Groth16::process_vk(&vk).expect("can process verifying key");
    let public_inputs = (Fr::from(600) * decaf377::basepoint()).to_field_elements().unwrap();
    let proof_result =
        Groth16::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

    assert!(!proof_result);
}
}
