use ark_ff::One;
use ark_groth16::{Groth16, ProvingKey, VerifyingKey};

use ark_r1cs_std::{
    prelude::{AllocVar, CurveVar, EqGadget},
    uint8::UInt8,
    R1CSVar, ToBitsGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ToConstraintField};
use ark_snark::SNARK;
use decaf377::{
    basepoint,
    r1cs::{ElementVar, FqVar},
    Bls12_377, Element, FieldExt, Fq, Fr,
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

#[test]
fn groth16_dl_proof_happy_path() {
    let (pk, vk) = DiscreteLogCircuit::generate_test_parameters();
    let mut rng = OsRng;

    let mut scalar = [0u8; 32];
    scalar[0] = 2;
    let public = Fr::from(2) * basepoint();

    // Prover POV
    let circuit = DiscreteLogCircuit { scalar, public };
    let proof = Groth16::prove(&pk, circuit, &mut rng)
        .map_err(|_| anyhow::anyhow!("invalid proof"))
        .expect("can generate proof");

    // Verifier POV
    let processed_pvk = Groth16::process_vk(&vk).expect("can process verifying key");
    let public_inputs = public.to_field_elements().unwrap();
    dbg!(public_inputs.len());
    let proof_result =
        Groth16::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

    assert!(proof_result);
}

#[test]
fn groth16_dl_proof_unhappy_path() {
    let (pk, vk) = DiscreteLogCircuit::generate_test_parameters();
    let mut rng = OsRng;

    let mut scalar = [0u8; 32];
    scalar[0] = 2;
    let public = Fr::from(2) * basepoint();

    let wrong_public = Fr::from(666) * basepoint();

    // Prover POV
    let circuit = DiscreteLogCircuit { scalar, public };
    let proof = Groth16::prove(&pk, circuit, &mut rng)
        .map_err(|_| anyhow::anyhow!("invalid proof"))
        .expect("can generate proof");

    // Verifier POV
    let processed_pvk = Groth16::process_vk(&vk).expect("can process verifying key");
    let public_inputs = wrong_public.to_field_elements().unwrap();
    dbg!(public_inputs.len());
    let proof_result =
        Groth16::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

    assert!(!proof_result);
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

        dbg!(public_var.value().unwrap_or_default());

        // 3. Add constraint that the compressed witness variable equals the public_var
        let test_public = witness_var.compress_to_field(self.point)?;
        dbg!(test_public.clone().value().unwrap_or_default());
        test_public.enforce_equal(&public_var)?;

        Ok(())
    }
}

impl CompressionCircuit {
    fn generate_test_parameters() -> (ProvingKey<Bls12_377>, VerifyingKey<Bls12_377>) {
        let point = Fr::from(100) * decaf377::basepoint();
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

#[test]
fn groth16_compression_proof_happy_path() {
    let (pk, vk) = CompressionCircuit::generate_test_parameters();
    let mut rng = OsRng;

    // Prover POV
    let point = Fr::from(666) * decaf377::basepoint();
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
    dbg!(public_inputs.len());
    let proof_result =
        Groth16::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

    dbg!(field_element);
    // TODO: Mystery test failure here... final field element computed in R1CS is for sure correct
    // based on the debug statements. However, the equality constraints causes a proof verification
    // failure. Why?
    assert!(proof_result);
}

#[test]
fn groth16_compression_proof_unhappy_path() {
    let (pk, vk) = CompressionCircuit::generate_test_parameters();
    let mut rng = OsRng;

    // Prover POV
    let point = Fr::from(666) * decaf377::basepoint();
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
    let public_inputs = (Fq::one()).to_field_elements().unwrap();
    let proof_result =
        Groth16::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

    assert!(!proof_result);
}
