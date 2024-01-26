use crate::Fq;

pub trait SqrtRatioZeta: Sized {
    /// Computes the square root of a ratio of field elements, returning:
    ///
    /// - `(true, sqrt(num/den))` if `num` and `den` are both nonzero and `num/den` is square;
    /// - `(true, 0)` if `num` is zero;
    /// - `(false, 0)` if `den` is zero;
    /// - `(false, sqrt(zeta*num/den))` if `num` and `den` are both nonzero and `num/den` is nonsquare;
    fn sqrt_ratio_zeta(num: &Self, den: &Self) -> (bool, Self);
}

impl SqrtRatioZeta for Fq {
    fn sqrt_ratio_zeta(num: &Self, den: &Self) -> (bool, Self) {
        if num == &Fq::zero() {
            return (true, *num);
        }
        if den == &Fq::zero() {
            return (false, *den);
        }
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::ZETA;

    use ark_ff::PrimeField;
    use proptest::prelude::*;

    fn fq_strategy() -> BoxedStrategy<Fq> {
        any::<[u8; 32]>()
            .prop_map(|bytes| Fq::from_le_bytes_mod_order(&bytes[..]))
            .boxed()
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(10000))]
        #[test]
        fn sqrt_ratio_zeta(u in fq_strategy(), v in fq_strategy()) {
            if u == Fq::zero() {
                assert_eq!(Fq::sqrt_ratio_zeta(&u, &v), (true, u));
            } else if v == Fq::zero() {
                assert_eq!(Fq::sqrt_ratio_zeta(&u, &v), (false, v));
            } else {
                let (was_square, sqrt_zeta_uv) = Fq::sqrt_ratio_zeta(&u, &v);
                let zeta_uv = sqrt_zeta_uv * sqrt_zeta_uv;
                if was_square {
                    // check zeta_uv = u/v
                    assert_eq!(u, v * zeta_uv);
                } else {
                    // check zeta_uv = zeta * u / v
                    assert_eq!(*ZETA * u, v * zeta_uv);
                }
            }
        }
    }

    #[test]
    fn sqrt_ratio_edge_cases() {
        // u = 0
        assert_eq!(
            Fq::sqrt_ratio_zeta(&Fq::zero(), &Fq::one()),
            (true, Fq::zero())
        );

        // v = 0
        assert_eq!(
            Fq::sqrt_ratio_zeta(&Fq::one(), &Fq::zero()),
            (false, Fq::zero())
        );
    }
}
