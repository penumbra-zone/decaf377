use ark_groth16::{r1cs_to_qap::LibsnarkReduction, Groth16, Proof, ProvingKey, VerifyingKey};
use proptest::prelude::*;

use ark_r1cs_std::{
    prelude::{AllocVar, CurveVar, EqGadget, ToBitsGadget},
    uint8::UInt8,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ToConstraintField};
use ark_snark::SNARK;
use decaf377::{
    r1cs::{CountConstraints, ElementVar, FqVar},
    Bls12_377, Element, Fq, Fr,
};
use rand_core::OsRng;

fn element_strategy() -> BoxedStrategy<Element> {
    any::<[u8; 32]>()
        .prop_map(|bytes| Fq::from_le_bytes_mod_order(&bytes[..]))
        .prop_map(|r| Element::encode_to_curve(&r))
        .boxed()
}

#[derive(Clone)]
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
        let compressed_public = self.public.vartime_compress_to_field();
        let public_var: ElementVar = AllocVar::new_input(cs.clone(), || Ok(compressed_public))?;
        let basepoint_var = ElementVar::new_constant(cs, Element::GENERATOR)?;
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
        let (pk, vk) =
            Groth16::<Bls12_377, LibsnarkReduction>::circuit_specific_setup(circuit, &mut OsRng)
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
        let public = Fr::from_le_bytes_mod_order(&scalar_arr[..]) * Element::GENERATOR;

        // Prover POV
        let circuit = DiscreteLogCircuit { scalar, public };
        let proof = Groth16::<Bls12_377, LibsnarkReduction>::prove(&pk, circuit, &mut rng)
            .map_err(|_| anyhow::anyhow!("invalid proof"))
            .expect("can generate proof");

        // Verifier POV
        let processed_pvk = Groth16::<Bls12_377, LibsnarkReduction>::process_vk(&vk).expect("can process verifying key");
        let public_inputs = public.to_field_elements().unwrap();
        let proof_result =
            Groth16::<Bls12_377, LibsnarkReduction>::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

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
        let public = Fr::from_le_bytes_mod_order(&scalar_arr[..]) * Element::GENERATOR;

        let wrong_public = Fr::from(666u64) * Element::GENERATOR;

        // Prover POV
        let circuit = DiscreteLogCircuit { scalar, public };
        let proof = Groth16::<Bls12_377, LibsnarkReduction>::prove(&pk, circuit, &mut rng)
            .map_err(|_| anyhow::anyhow!("invalid proof"))
            .expect("can generate proof");

        // Verifier POV
        let processed_pvk = Groth16::<Bls12_377, LibsnarkReduction>::process_vk(&vk).expect("can process verifying key");
        let public_inputs = wrong_public.to_field_elements().unwrap();
        let proof_result =
            Groth16::<Bls12_377, LibsnarkReduction>::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

        assert!(!proof_result);
    }
}

#[derive(Clone)]
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
        let test_public = witness_var.compress_to_field()?;
        public_var.enforce_equal(&test_public)?;

        Ok(())
    }
}

impl CompressionCircuit {
    fn generate_test_parameters() -> (ProvingKey<Bls12_377>, VerifyingKey<Bls12_377>) {
        //let point = Fr::from(100) * Element::GENERATOR;
        let point = Fr::from(2u64) * Element::GENERATOR;
        //let point = Element::default();
        let field_element = point.vartime_compress_to_field();
        let circuit = CompressionCircuit {
            point,
            field_element,
        };
        let (pk, vk) =
            Groth16::<Bls12_377, LibsnarkReduction>::circuit_specific_setup(circuit, &mut OsRng)
                .expect("can perform circuit specific setup");
        (pk, vk)
    }
}

fn fr_strategy() -> BoxedStrategy<Fr> {
    any::<[u8; 32]>()
        .prop_map(|bytes| Fr::from_le_bytes_mod_order(&bytes[..]))
        .boxed()
}

proptest! {
#![proptest_config(ProptestConfig::with_cases(10))]
#[test]
    fn groth16_compression_proof_happy_path(scalar in fr_strategy()) {
        let (pk, vk) = CompressionCircuit::generate_test_parameters();
        let mut rng = OsRng;

        // Prover POV
        let point = scalar * Element::GENERATOR;
        let field_element = point.vartime_compress_to_field();
        let circuit = CompressionCircuit {
            point,
            field_element,
        };
        dbg!(circuit.clone().num_constraints_and_instance_variables());

        let proof = Groth16::<Bls12_377, LibsnarkReduction>::prove(&pk, circuit, &mut rng)
            .map_err(|_| anyhow::anyhow!("invalid proof"))
            .expect("can generate proof");

        // Verifier POV
        let processed_pvk = Groth16::<Bls12_377, LibsnarkReduction>::process_vk(&vk).expect("can process verifying key");
        let public_inputs = field_element.to_field_elements().unwrap();
        let proof_result =
            Groth16::<Bls12_377, LibsnarkReduction>::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

        assert!(proof_result);
    }
}

proptest! {
#![proptest_config(ProptestConfig::with_cases(10))]
#[test]
    fn groth16_compression_proof_unhappy_path(scalar in fr_strategy()) {
        let (pk, vk) = CompressionCircuit::generate_test_parameters();
        let mut rng = OsRng;

        // Prover POV
        let point = scalar * Element::GENERATOR;
        let field_element = point.vartime_compress_to_field();
        let circuit = CompressionCircuit {
            point,
            field_element,
        };
        let proof = Groth16::<Bls12_377, LibsnarkReduction>::prove(&pk, circuit, &mut rng)
            .map_err(|_| anyhow::anyhow!("invalid proof"))
            .expect("can generate proof");

        // Verifier POV
        let processed_pvk = Groth16::<Bls12_377, LibsnarkReduction>::process_vk(&vk).expect("can process verifying key");
        let wrong_public_input = Fq::rand(&mut rng);
        let public_inputs = (wrong_public_input).to_field_elements().unwrap();
        let proof_result =
            Groth16::<Bls12_377, LibsnarkReduction>::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

        assert!(!proof_result);
    }
}

#[derive(Clone)]
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
        let compressed_public = self.point.vartime_compress_to_field();
        let public_var: ElementVar = AllocVar::new_input(cs, || Ok(compressed_public))?;

        // 3. Add decompression constraints
        let test_public = ElementVar::decompress_from_field(witness_var)?;
        public_var.enforce_equal(&test_public)?;

        Ok(())
    }
}

impl DecompressionCircuit {
    fn generate_test_parameters() -> (ProvingKey<Bls12_377>, VerifyingKey<Bls12_377>) {
        let point = Fr::from(100u64) * Element::GENERATOR;
        let field_element = point.vartime_compress_to_field();
        let circuit = DecompressionCircuit {
            point,
            field_element,
        };
        let (pk, vk) =
            Groth16::<Bls12_377, LibsnarkReduction>::circuit_specific_setup(circuit, &mut OsRng)
                .expect("can perform circuit specific setup");
        (pk, vk)
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]
    #[test]
        fn groth16_decompression_proof_happy_path(scalar in fr_strategy()) {
            let (pk, vk) = DecompressionCircuit::generate_test_parameters();
            let mut rng = OsRng;

            // Prover POV
            let point = scalar * Element::GENERATOR;
    let field_element = point.vartime_compress_to_field();
    let circuit = DecompressionCircuit {
        point,
        field_element,
    };
    dbg!(circuit.clone().num_constraints_and_instance_variables());

    let proof = Groth16::<Bls12_377, LibsnarkReduction>::prove(&pk, circuit, &mut rng)
        .map_err(|_| anyhow::anyhow!("invalid proof"))
        .expect("can generate proof");

    // Verifier POV
    let processed_pvk = Groth16::<Bls12_377, LibsnarkReduction>::process_vk(&vk).expect("can process verifying key");
    let public_inputs = point.to_field_elements().unwrap();
    let proof_result =
        Groth16::<Bls12_377, LibsnarkReduction>::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

    assert!(proof_result);
}
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]
    #[test]
        fn groth16_decompression_proof_unhappy_path(scalar in fr_strategy()) {
            let (pk, vk) = DecompressionCircuit::generate_test_parameters();
            let mut rng = OsRng;

            // Prover POV
            let point = scalar * Element::GENERATOR;
    let field_element = point.vartime_compress_to_field();
    let circuit = DecompressionCircuit {
        point,
        field_element,
    };
    let proof = Groth16::<Bls12_377, LibsnarkReduction>::prove(&pk, circuit, &mut rng)
        .map_err(|_| anyhow::anyhow!("invalid proof"))
        .expect("can generate proof");

    // Verifier POV
    let processed_pvk = Groth16::<Bls12_377, LibsnarkReduction>::process_vk(&vk).expect("can process verifying key");
    let public_inputs = (Fr::from(600u64) * Element::GENERATOR).to_field_elements().unwrap();
    let proof_result =
        Groth16::<Bls12_377, LibsnarkReduction>::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

    assert!(!proof_result);
}
}

#[derive(Clone)]
struct ElligatorCircuit {
    // Witness
    field_element: Fq,

    // Public input
    pub point: Element,
}

impl ConstraintSynthesizer<Fq> for ElligatorCircuit {
    fn generate_constraints(
        self,
        cs: ark_relations::r1cs::ConstraintSystemRef<Fq>,
    ) -> ark_relations::r1cs::Result<()> {
        // 1. Add witness variable
        let witness_var = FqVar::new_witness(cs.clone(), || Ok(self.field_element))?;

        // 2. Add public input variable
        let public_var: ElementVar = AllocVar::new_input(cs, || Ok(self.point))?;

        // 3. Add elligator constraints
        let test_public = ElementVar::encode_to_curve(&witness_var)?;
        public_var.enforce_equal(&test_public)?;

        Ok(())
    }
}

impl ElligatorCircuit {
    fn generate_test_parameters() -> (ProvingKey<Bls12_377>, VerifyingKey<Bls12_377>) {
        let field_element = Fq::from(100u64);
        let point = Element::encode_to_curve(&field_element);
        let circuit = ElligatorCircuit {
            point,
            field_element,
        };
        let (pk, vk) =
            Groth16::<Bls12_377, LibsnarkReduction>::circuit_specific_setup(circuit, &mut OsRng)
                .expect("can perform circuit specific setup");
        (pk, vk)
    }
}

fn fq_strategy() -> BoxedStrategy<Fq> {
    any::<[u8; 32]>()
        .prop_map(|bytes| Fq::from_le_bytes_mod_order(&bytes[..]))
        .boxed()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]
#[test]
fn groth16_elligator_proof_happy_path(field_element in fq_strategy()) {
    let (pk, vk) = ElligatorCircuit::generate_test_parameters();
    let mut rng = OsRng;

    // Prover POV
    let point = Element::encode_to_curve(&field_element);
    let circuit = ElligatorCircuit {
        point,
        field_element,
    };
    dbg!(circuit.clone().num_constraints_and_instance_variables());

    let proof = Groth16::<Bls12_377, LibsnarkReduction>::prove(&pk, circuit, &mut rng)
        .map_err(|_| anyhow::anyhow!("invalid proof"))
        .expect("can generate proof");

    // Verifier POV
    let processed_pvk = Groth16::<Bls12_377, LibsnarkReduction>::process_vk(&vk).expect("can process verifying key");
    let public_inputs = point.to_field_elements().unwrap();
    let proof_result =
        Groth16::<Bls12_377, LibsnarkReduction>::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

    assert!(proof_result);
}
        }

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]
#[test]
fn groth16_elligator_proof_unhappy_path(field_element in fq_strategy()) {
    let (pk, vk) = ElligatorCircuit::generate_test_parameters();
    let mut rng = OsRng;

    // Prover POV
    let point = Element::encode_to_curve(&field_element);
    let circuit = ElligatorCircuit {
        point,
        field_element,
    };
    let proof = Groth16::<Bls12_377, LibsnarkReduction>::prove(&pk, circuit, &mut rng)
        .map_err(|_| anyhow::anyhow!("invalid proof"))
        .expect("can generate proof");

    // Verifier POV
    let wrong_point = Fr::rand(&mut rng) * Element::GENERATOR;
    let processed_pvk = Groth16::<Bls12_377, LibsnarkReduction>::process_vk(&vk).expect("can process verifying key");
    let public_inputs = wrong_point.to_field_elements().unwrap();
    let proof_result =
        Groth16::<Bls12_377, LibsnarkReduction>::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

    assert!(!proof_result);
}
}

#[derive(Clone, Debug)]
struct PublicElementInput {
    pub point: Element,
}

impl ConstraintSynthesizer<Fq> for PublicElementInput {
    fn generate_constraints(
        self,
        cs: ark_relations::r1cs::ConstraintSystemRef<Fq>,
    ) -> ark_relations::r1cs::Result<()> {
        // 1. Add public input variable
        let _public_var: ElementVar = AllocVar::new_input(cs, || Ok(self.point))?;

        Ok(())
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]
#[test]
fn groth16_public_input(point in element_strategy()) {
    let test_circuit = PublicElementInput {
        point: Element::GENERATOR,
    };
    let (pk, vk) = Groth16::<Bls12_377, LibsnarkReduction>::circuit_specific_setup(test_circuit, &mut OsRng)
        .expect("can perform circuit specific setup");
    let mut rng = OsRng;

    // Prover POV
    let circuit = PublicElementInput { point };
    let proof: Proof<Bls12_377> = Groth16::<Bls12_377, LibsnarkReduction>::prove(&pk, circuit, &mut rng)
        .map_err(|_| anyhow::anyhow!("invalid proof"))
        .expect("can generate proof");

    // Verifier POV
    let processed_pvk = Groth16::<Bls12_377, LibsnarkReduction>::process_vk(&vk).expect("can process verifying key");
    let public_inputs = point.to_field_elements().unwrap();
    let proof_result =
        Groth16::<Bls12_377, LibsnarkReduction>::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

    assert!(proof_result);
}
}

#[derive(Clone)]
struct NegationCircuit {
    // Witness
    pos: Element,

    // Public input
    pub public_neg: Element,
}

impl ConstraintSynthesizer<Fq> for NegationCircuit {
    fn generate_constraints(
        self,
        cs: ark_relations::r1cs::ConstraintSystemRef<Fq>,
    ) -> ark_relations::r1cs::Result<()> {
        // 1. Add witness variable
        let pos = ElementVar::new_witness(cs.clone(), || Ok(self.pos))?;

        // 2. Add public input variables
        // This is derived from calling Point.negate() OOC
        let public_neg = ElementVar::new_input(cs, || Ok(self.public_neg))?;

        let neg: ElementVar = pos.negate()?;
        neg.enforce_equal(&public_neg)?;

        Ok(())
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]
#[test]
fn groth16_negation(point in element_strategy()) {
    let test_circuit = NegationCircuit {
        pos: Element::GENERATOR,
        public_neg: point.negate(),
    };
    let (pk, vk) = Groth16::<Bls12_377, LibsnarkReduction>::circuit_specific_setup(test_circuit, &mut OsRng)
        .expect("can perform circuit specific setup");
    let mut rng = OsRng;

    // Prover POV
    let public_neg = point.negate();
    let circuit = NegationCircuit {
        pos: point,
        public_neg,
    };
    let proof: Proof<Bls12_377> = Groth16::<Bls12_377, LibsnarkReduction>::prove(&pk, circuit, &mut rng)
        .map_err(|_| anyhow::anyhow!("invalid proof"))
        .expect("can generate proof");

    // Verifier POV
    let processed_pvk = Groth16::<Bls12_377, LibsnarkReduction>::process_vk(&vk).expect("can process verifying key");
    let public_inputs = public_neg.to_field_elements().unwrap();
    let proof_result =
        Groth16::<Bls12_377, LibsnarkReduction>::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

    assert!(proof_result);
}
}

#[derive(Clone)]
struct AddAssignAddCircuit {
    // Witness
    a: Element,
    b: Element,

    pub c: Element,
    pub d: Element,
}

impl ConstraintSynthesizer<Fq> for AddAssignAddCircuit {
    fn generate_constraints(
        self,
        cs: ark_relations::r1cs::ConstraintSystemRef<Fq>,
    ) -> ark_relations::r1cs::Result<()> {
        let a = ElementVar::new_witness(cs.clone(), || Ok(self.a))?;
        let b = ElementVar::new_witness(cs.clone(), || Ok(self.b))?;

        let c_pub = ElementVar::new_input(cs.clone(), || Ok(self.c))?;
        let c_add = a.clone() + b.clone();
        let mut c_add_assign = a.clone();
        c_add_assign += b.clone();

        c_add.enforce_equal(&c_pub)?;
        c_add_assign.enforce_equal(&c_pub)?;

        let d_pub = ElementVar::new_input(cs, || Ok(self.d))?;
        let d_sub = a.clone() - b.clone();
        let mut d_sub_assign = a.clone();
        d_sub_assign -= b;

        d_sub.enforce_equal(&d_pub)?;
        d_sub_assign.enforce_equal(&d_pub)?;

        Ok(())
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]
#[test]
fn groth16_add_addassign(a in element_strategy(), b in element_strategy()) {
    let test_a = Element::GENERATOR;
    let test_b = Element::GENERATOR * Fr::from(2u64);
    let test_circuit = AddAssignAddCircuit {
        a: test_a,
        b: test_b,
        c: test_a + test_b,
        d: test_a - test_b,
    };
    let (pk, vk) = Groth16::<Bls12_377, LibsnarkReduction>::circuit_specific_setup(test_circuit, &mut OsRng)
        .expect("can perform circuit specific setup");
    let mut rng = OsRng;

    // Prover POV
    let circuit = AddAssignAddCircuit {
        a,
        b,
        c: a + b,
        d: a - b,
    };

    let proof: Proof<Bls12_377> = Groth16::<Bls12_377, LibsnarkReduction>::prove(&pk, circuit, &mut rng)
        .map_err(|_| anyhow::anyhow!("invalid proof"))
        .expect("can generate proof");

    // Verifier POV
    let processed_pvk = Groth16::<Bls12_377, LibsnarkReduction>::process_vk(&vk).expect("can process verifying key");
    let mut public_inputs = (a + b).to_field_elements().unwrap();
    public_inputs.extend_from_slice(&(a - b).to_field_elements().unwrap());
    let proof_result =
        Groth16::<Bls12_377, LibsnarkReduction>::verify_with_processed_vk(&processed_pvk, &public_inputs, &proof).unwrap();

    assert!(proof_result);
}
}
