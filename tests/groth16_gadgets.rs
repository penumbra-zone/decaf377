use ark_groth16::{Groth16, Proof, ProvingKey, VerifyingKey};

use ark_r1cs_std::{
    prelude::{AllocVar, CurveVar, EqGadget},
    uint8::UInt8,
    ToBitsGadget,
};
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_snark::SNARK;
use decaf377::{basepoint, r1cs::Decaf377ElementVar, Bls12_377, Element, Fq};
use rand_core::OsRng;

struct DiscreteLogCircuit {
    // Witness
    scalar: [u8; 32],

    // Public input
    public: Element,
}

impl ConstraintSynthesizer<Fq> for DiscreteLogCircuit {
    fn generate_constraints(
        self,
        cs: ark_relations::r1cs::ConstraintSystemRef<Fq>,
    ) -> ark_relations::r1cs::Result<()> {
        // 1. Add witness variable
        let witness_vars = UInt8::new_witness_vec(cs.clone(), &self.scalar)?;

        // 2. Add public input variable
        let public_var = Decaf377ElementVar::new_input(cs.clone(), || Ok(self.public))?;

        let basepoint_var = Decaf377ElementVar::new_constant(cs, basepoint())?;
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
fn proof_test() {
    let (pk, vk) = DiscreteLogCircuit::generate_test_parameters();
}
