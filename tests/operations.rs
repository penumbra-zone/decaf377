#![allow(non_snake_case)]

use ark_ff::PrimeField;
use decaf377::{Element, Fq, Fr};
use proptest::prelude::*;

fn element_strategy() -> BoxedStrategy<Element> {
    any::<[u8; 32]>()
        .prop_map(|bytes| Fq::from_le_bytes_mod_order(&bytes[..]))
        .prop_map(|r| Element::encode_to_curve(&r))
        .boxed()
}

fn fr_strategy() -> BoxedStrategy<Fr> {
    any::<[u8; 32]>()
        .prop_map(|bytes| Fr::from_le_bytes_mod_order(&bytes[..]))
        .boxed()
}

proptest! {
    #[test]
    fn scalar_mul_commutes_with_addition(
        a in fr_strategy(),
        b in fr_strategy(),
        P in element_strategy(),
    ) {
        assert_eq!(
            (a * P) + (b * P),
            (a + b) * P
        );
    }

    #[test]
    fn scalar_mul_is_associative_and_commutative(
        a in fr_strategy(),
        b in fr_strategy(),
        P in element_strategy(),
    ) {
        assert_eq!(
            b * (a * P),
            (a * b) * P
        );
    }

    #[test]
    fn vartime_multiscalar_mul_matches_scalar_mul(
        a in fr_strategy(),
        b in fr_strategy(),
        c in fr_strategy(),
        P in element_strategy(),
        Q in element_strategy(),
        R in element_strategy(),
    ) {
        assert_eq!(
            (a * P) + (b * Q) + (c * R),
            Element::vartime_multiscalar_mul(
                &[a, b, c],
                &[P, Q, R],
            )
        );
    }
}
