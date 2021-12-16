use ark_ed_on_bls12_377::Fq;
use ark_ff::{Field, SquareRootField, Zero};

use crate::constants::{ONE, ZETA, ZETA_INVERSE};

pub trait SqrtRatioZeta: Sized {
    /// Computes the square root of a ratio of field elements, returning:
    ///
    /// - `(true, sqrt(u/v))` if `u` and `v` are both nonzero and `u/v` is square;
    /// - `(true, 0)` if `u` is zero;
    /// - `(false, 0)` if `v` is zero;
    /// - `(false, sqrt(zeta*u/v))` if `u` and `v` are both nonzero and `u/v` is nonsquare;
    ///
    fn sqrt_ratio_zeta(u: &Self, v: &Self) -> (bool, Self);
}

impl SqrtRatioZeta for Fq {
    fn sqrt_ratio_zeta(u: &Self, v: &Self) -> (bool, Self) {
        // TODO: optimized implementation
        if u.is_zero() {
            return (true, *u);
        }
        if v.is_zero() {
            return (false, *v);
        }

        let uv = v.inverse().expect("nonzero") * u;
        if let Some(sqrt_uv) = uv.sqrt() {
            return (true, sqrt_uv);
        } else {
            let sqrt_zeta_uv = (*ZETA * uv)
                .sqrt()
                .expect("must be square if u/v nonsquare");
            return (false, sqrt_zeta_uv);
        }
    }
}

pub trait InverseSqrtZeta: Sized {
    /// Computes the inverse square root of a field element, returning:
    ///
    /// - `(true, 0)` if `x` is zero;
    /// - `(true, 1/sqrt(x))` if `x` is nonzero and `x` is square;
    /// - `(false, 1/sqrt(zeta*x))` if `x` is nonzero and `x` is nonsquare;
    ///
    fn isqrt_zeta(x: &Self) -> (bool, Self);
}

impl InverseSqrtZeta for Fq {
    fn isqrt_zeta(x: &Self) -> (bool, Self) {
        // Corresponds to isqrt_i in Sage specification
        let (iss, isri) = Fq::sqrt_ratio_zeta(&ONE, &x);

        if isri == Fq::zero() {
            return (true, isri);
        } else if isri != Fq::zero() && iss == false {
            // The result `isri` of sqrt_ratio_zeta in this case is `sqrt(zeta*1/x)`
            // whereas we want `1/sqrt(zeta*x)`. So we multiply `isri` by `1/zeta`.
            return (iss, *ZETA_INVERSE * isri);
        } else {
            return (iss, isri);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use ark_ff::PrimeField;
    use proptest::prelude::*;

    fn fq_strategy() -> BoxedStrategy<Fq> {
        any::<[u8; 32]>()
            .prop_map(|bytes| Fq::from_le_bytes_mod_order(&bytes[..]))
            .boxed()
    }

    proptest! {
        #[test]
        fn sqrt_ratio_zeta(u in fq_strategy(), v in fq_strategy()) {
            if u.is_zero() {
                assert_eq!(Fq::sqrt_ratio_zeta(&u, &v), (true, u));
            } else if v.is_zero() {
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
}
