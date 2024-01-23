fn main() {
    #[cfg(feature = "r1cs")]
    {
        use decaf377::r1cs::TestCircuit;
        use rand_core::OsRng;

        let (pk, _) = TestCircuit::generate_test_parameters();
        // let mut rng = OsRng;
        // let test_circuit = TestCircuit {
        //     encoding: Element::default().vartime_compress_to_field(),
        // };
        // Groth16::<Bls12_377, LibsnarkReduction>::prove(&pk, test_circuit, &mut rng)
        //     .expect("can generate proof");
    }
}
