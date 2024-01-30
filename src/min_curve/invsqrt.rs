use subtle::{ConditionallySelectable, ConstantTimeEq};

use crate::{fields::fq::arkworks_constants::*, Fq};

use crate::min_curve::constants::ZETA;

impl Fq {
    /// For square elements, calculate their square root, otherwise return an undefined element.
    ///
    /// Based on https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-10.html#name-constant-time-tonelli-shanks
    fn our_sqrt(&self) -> Self {
        // Constants c1,...,c5 used for square root computation as defined in the above Appendix:
        // c1 = TWO_ADICITY
        // c2 is not directly used in the computation, it's used to compute c3
        // c3 = TRACE_MINUS_ONE_DIV_TWO_LIMBS;
        // c4 is not directly used in the computation, but should match ZETA-
        // c5 = c4 ^ c2
        // c5 = QUADRATIC_NON_RESIDUE_TO_TRACE

        // Step 1: z = x^c3
        let mut z = self.pow_le_limbs(&TRACE_MINUS_ONE_DIV_TWO_LIMBS);

        // Step 2: t = z * z * x
        let mut t = z * z * self;

        // Step 3: z = z * x;
        z = z * self;

        // Step 4:  b = t
        let mut b = t;

        // Step 5: c = c5
        let mut c = QUADRATIC_NON_RESIDUE_TO_TRACE;

        // Step 6: for i in (c1, c1 - 1, ..., 2):
        for i in (2..=TWO_ADICITY).rev() {
            // Step 7: for j in (1, 2, ..., i - 2):
            for _j in 1..=i - 2 {
                // Step 8: b = b * b
                b = b * b;
            }

            // Step 9: z = CMOV(z, z * c, b != 1)
            z = Fq::conditional_select(&z, &(z * c), !b.ct_eq(&Self::one()));

            // Step 10: c = c * c
            c = c * c;

            // Step 11: t = CMOV(t, t * c, b != 1)
            t = Fq::conditional_select(&t, &(t * c), !b.ct_eq(&Self::one()));

            // Step 12: b = t
            b = t;
        }

        // Step 13: return z
        z
    }

    fn pow_le_limbs(&self, limbs: &[u64]) -> Self {
        let mut acc = Self::one();
        let mut insert = *self;
        for limb in limbs {
            for i in 0..64 {
                if (limb >> i) & 1 == 1 {
                    acc *= insert;
                }
                insert *= insert;
            }
        }
        acc
    }

    /// Computes the square root of a ratio of field elements, returning:
    ///
    /// - `(true, sqrt(num/den))` if `num` and `den` are both nonzero and `num/den` is square;
    /// - `(true, 0)` if `num` is zero;
    /// - `(false, 0)` if `den` is zero;
    /// - `(false, sqrt(zeta*num/den))` if `num` and `den` are both nonzero and `num/den` is nonsquare;
    pub fn non_arkworks_sqrt_ratio_zeta(num: &Self, den: &Self) -> (bool, Self) {
        if num == &Fq::zero() {
            return (true, *num);
        }
        if den == &Fq::zero() {
            return (false, *den);
        }
        let x = *num / *den;
        // Because num was not zero, this will only be 1 or -1
        let symbol = x.pow_le_limbs(&MODULUS_MINUS_ONE_DIV_TWO_LIMBS);
        if symbol == Self::one() {
            (true, x.our_sqrt())
        } else {
            (false, (ZETA * x).our_sqrt())
        }
    }
}

#[cfg(all(test, feature = "arkworks"))]
mod tests {
    use super::*;
    use ark_ff::Field;
    use ark_ff::PrimeField;
    use proptest::prelude::*;

    fn fq_strategy() -> impl Strategy<Value = Fq> {
        any::<[u8; 32]>()
            .prop_map(|bytes| Fq::from_le_bytes_mod_order(&bytes[..]))
            .boxed()
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(10000))]
        #[test]
        fn sqrt_ratio_zeta(u in fq_strategy(), v in fq_strategy()) {
            if u == Fq::zero() {
                assert_eq!(Fq::non_arkworks_sqrt_ratio_zeta(&u, &v), (true, u));
            } else if v == Fq::zero() {
                assert_eq!(Fq::non_arkworks_sqrt_ratio_zeta(&u, &v), (false, v));
            } else {
                let (was_square, sqrt_zeta_uv) = Fq::non_arkworks_sqrt_ratio_zeta(&u, &v);
                let zeta_uv = sqrt_zeta_uv * sqrt_zeta_uv;
                if was_square {
                    // check zeta_uv = u/v
                    assert_eq!(u, v * zeta_uv);
                } else {
                    // check zeta_uv = zeta * u / v
                    assert_eq!(ZETA * u, v * zeta_uv);
                }
            }
        }
    }

    #[test]
    fn sqrt_ratio_edge_cases() {
        // u = 0
        assert_eq!(
            Fq::non_arkworks_sqrt_ratio_zeta(&Fq::zero(), &Fq::one()),
            (true, Fq::zero())
        );

        // v = 0
        assert_eq!(
            Fq::non_arkworks_sqrt_ratio_zeta(&Fq::one(), &Fq::zero()),
            (false, Fq::zero())
        );
    }

    proptest! {
        #[test]
        fn sqrt_matches_arkworks(x in fq_strategy()) {
            let arkworks_sqrt = x.sqrt();
            let our_sqrt = x.our_sqrt();
            if arkworks_sqrt.is_some() {
                assert_eq!(arkworks_sqrt.unwrap(), our_sqrt);
            }
        }
    }
}
