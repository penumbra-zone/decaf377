use std::collections::HashMap;
use std::convert::TryInto;

use ark_ed_on_bls12_377::Fq;
use ark_ff::{BigInteger256, BigInteger64, Field, Zero};
use once_cell::sync::Lazy;

use crate::constants::{
    G, M_MINUS_ONE_DIV_TWO, N, ONE, SQRT_W, ZETA_INVERSE, ZETA_TO_ONE_MINUS_M_DIV_TWO,
};

pub trait SqrtRatioZeta: Sized {
    /// Computes the square root of a ratio of field elements, returning:
    ///
    /// - `(true, sqrt(num/den))` if `num` and `den` are both nonzero and `num/den` is square;
    /// - `(true, 0)` if `num` is zero;
    /// - `(false, 0)` if `den` is zero;
    /// - `(false, sqrt(zeta*num/den))` if `num` and `den` are both nonzero and `num/den` is nonsquare;
    ///
    fn sqrt_ratio_zeta(u: &Self, den: &Self) -> (bool, Self);
}

struct SquareRootTables {
    pub s_lookup: HashMap<Fq, u64>,
    pub g0: Box<[Fq; 256]>,
    pub g7: Box<[Fq; 256]>,
    pub g8: Box<[Fq; 256]>,
    pub g15: Box<[Fq; 256]>,
    pub g16: Box<[Fq; 256]>,
    pub g23: Box<[Fq; 256]>,
    pub g24: Box<[Fq; 256]>,
    pub g31: Box<[Fq; 256]>,
    pub g32: Box<[Fq; 256]>,
    pub g40: Box<[Fq; 256]>,
}

impl SquareRootTables {
    fn new() -> Self {
        let mut s_lookup = HashMap::new();
        for nu in 0..256 {
            // These entries should be g**(-1 * nu * 2**(n-w)) so:
            // 1. We compute g**(nu * 2**(n-w))
            // 2. Then take the inverse of the quantity from step 1
            let exp: BigInteger256 = (nu * 2u64.pow(N - SQRT_W)).into();
            let g_inv = G.pow(exp);
            s_lookup.insert(
                g_inv.inverse().expect("inverse exists for these elements"),
                nu,
            );
        }

        let powers_of_two = [0, 7, 8, 15, 16, 23, 24, 31, 32, 40];
        let mut gtab = Vec::new();
        for power_of_two in powers_of_two {
            let mut gtab_i = Vec::<Fq>::new();
            for nu in 0..256 {
                let exp: BigInteger256 = (nu * 2u64.pow(power_of_two)).into();
                gtab_i.push(G.pow(exp))
            }
            gtab.push(gtab_i);
        }

        Self {
            s_lookup,
            g40: gtab.pop().unwrap().into_boxed_slice().try_into().unwrap(),
            g32: gtab.pop().unwrap().into_boxed_slice().try_into().unwrap(),
            g31: gtab.pop().unwrap().into_boxed_slice().try_into().unwrap(),
            g24: gtab.pop().unwrap().into_boxed_slice().try_into().unwrap(),
            g23: gtab.pop().unwrap().into_boxed_slice().try_into().unwrap(),
            g16: gtab.pop().unwrap().into_boxed_slice().try_into().unwrap(),
            g15: gtab.pop().unwrap().into_boxed_slice().try_into().unwrap(),
            g8: gtab.pop().unwrap().into_boxed_slice().try_into().unwrap(),
            g7: gtab.pop().unwrap().into_boxed_slice().try_into().unwrap(),
            g0: gtab.pop().unwrap().into_boxed_slice().try_into().unwrap(),
        }
    }
}

static SQRT_LOOKUP_TABLES: Lazy<SquareRootTables> = Lazy::new(|| SquareRootTables::new());

impl SqrtRatioZeta for Fq {
    fn sqrt_ratio_zeta(num: &Self, den: &Self) -> (bool, Self) {
        // This square root method is based on:
        // * [Sarkar2020](https://eprint.iacr.org/2020/1407)
        // * [Zcash Pasta](https://github.com/zcash/pasta_curves)
        //
        // See the Penumbra protocol specification for details.
        if num.is_zero() {
            return (true, *num);
        }
        if den.is_zero() {
            return (false, *den);
        }

        let u = den.inverse().expect("nonzero") * num;
        let v = u.pow(*M_MINUS_ONE_DIV_TWO);
        let uv = u * v;

        // x = u * v^2 = x5
        let x5 = uv * v;
        let pow2_8: BigInteger64 = 2u64.pow(8).into();

        // x4 = x5^{2^8}
        let x4 = x5.pow(pow2_8);
        // x3 = x4^{2^8}
        let x3 = x4.pow(pow2_8);
        // x2 = x3^{2^8}
        let x2 = x3.pow(pow2_8);
        // x1 = x2^{2^8}
        let x1 = x2.pow(pow2_8);
        let pow2_7: BigInteger64 = 2u64.pow(7).into();
        // x0 = x1^{2^7}
        let x0 = x1.pow(pow2_7);

        // i = 0
        let q0_prime = SQRT_LOOKUP_TABLES.s_lookup[&x0] as usize;
        let mut t = q0_prime;

        // i = 1
        let alpha_1 = x1 * SQRT_LOOKUP_TABLES.g32[q0_prime];
        let q1_prime = SQRT_LOOKUP_TABLES.s_lookup[&alpha_1] as usize;
        t += q1_prime << 7;

        // i = 2
        let alpha_2 = x2 * SQRT_LOOKUP_TABLES.g24[q0_prime] * SQRT_LOOKUP_TABLES.g31[q1_prime];
        let q2 = SQRT_LOOKUP_TABLES.s_lookup[&alpha_2] as usize;
        t += q2 << 15;

        // i = 3
        let alpha_3 = x3
            * SQRT_LOOKUP_TABLES.g16[q0_prime]
            * SQRT_LOOKUP_TABLES.g23[q1_prime]
            * SQRT_LOOKUP_TABLES.g31[q2];
        let q3 = SQRT_LOOKUP_TABLES.s_lookup[&alpha_3] as usize;
        t += q3 << 23;

        // i = 4
        let alpha_4 = x4
            * SQRT_LOOKUP_TABLES.g8[q0_prime]
            * SQRT_LOOKUP_TABLES.g15[q1_prime]
            * SQRT_LOOKUP_TABLES.g23[q2]
            * SQRT_LOOKUP_TABLES.g31[q3];
        let q4 = SQRT_LOOKUP_TABLES.s_lookup[&alpha_4] as usize;
        t += q4 << 31;

        // i = 5
        let alpha_5 = x5
            * SQRT_LOOKUP_TABLES.g0[q0_prime]
            * SQRT_LOOKUP_TABLES.g7[q1_prime]
            * SQRT_LOOKUP_TABLES.g15[q2]
            * SQRT_LOOKUP_TABLES.g23[q3]
            * SQRT_LOOKUP_TABLES.g31[q4];
        let q5 = SQRT_LOOKUP_TABLES.s_lookup[&alpha_5] as usize;
        t += q5 << 39;

        t = (t + 1) >> 1;
        let mut res: Fq = uv
            * SQRT_LOOKUP_TABLES.g0[t & 0xFF]
            * SQRT_LOOKUP_TABLES.g8[(t >> 8) & 0xFF]
            * SQRT_LOOKUP_TABLES.g16[(t >> 16) & 0xFF]
            * SQRT_LOOKUP_TABLES.g24[(t >> 24) & 0xFF]
            * SQRT_LOOKUP_TABLES.g32[(t >> 32) & 0xFF]
            * SQRT_LOOKUP_TABLES.g40[(t >> 40) & 0xFF];

        if q0_prime % 2 != 0 {
            res *= *ZETA_TO_ONE_MINUS_M_DIV_TWO
        }

        let square = res.square() * den;
        let is_square = (square - num) == Fq::zero();

        (is_square, res)
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
        let (iss, isri) = Fq::sqrt_ratio_zeta(&ONE, x);

        if isri == Fq::zero() {
            (true, isri)
        } else if isri != Fq::zero() && !iss {
            // The result `isri` of sqrt_ratio_zeta in this case is `sqrt(zeta*1/x)`
            // whereas we want `1/sqrt(zeta*x)`. So we multiply `isri` by `1/zeta`.
            (iss, *ZETA_INVERSE * isri)
        } else {
            (iss, isri)
        }
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
