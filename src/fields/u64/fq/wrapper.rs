use super::fiat;
use core::ops::{Add, Mul, Neg, Sub};

const NUM_LIMBS: usize = 4;
const PRIME_ORDER: usize = 253;

#[derive(Copy, Clone)]
pub struct Fq(fiat::FqMontgomeryDomainFieldElement);

impl core::fmt::Debug for Fq {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let bytes = self.to_bytes();
        write!(f, "Fq(0x{})", hex::encode(bytes))
    }
}

impl PartialEq for Fq {
    fn eq(&self, other: &Fq) -> bool {
        let self_bytes = self.to_bytes();
        let other_bytes = other.to_bytes();
        self_bytes[..] == other_bytes[..]
    }
}

impl Eq for Fq {}

impl Fq {
    pub fn from_bytes(bytes: &[u8; 32]) -> Self {
        let mut x_non_montgomery = fiat::FqNonMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        let mut x = fiat::FqMontgomeryDomainFieldElement([0; NUM_LIMBS]);

        fiat::fq_from_bytes(&mut x_non_montgomery.0, &bytes);
        fiat::fq_to_montgomery(&mut x, &x_non_montgomery);

        Self(x)
    }

    pub fn to_bytes(&self) -> [u8; 32] {
        let mut x_non_montgomery = fiat::FqNonMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        let mut bytes = [0u8; 32];

        fiat::fq_from_montgomery(&mut x_non_montgomery, &self.0);
        fiat::fq_to_bytes(&mut bytes, &x_non_montgomery.0);

        bytes
    }

    pub fn zero() -> Self {
        Self(fiat::FqMontgomeryDomainFieldElement([0; NUM_LIMBS]))
    }

    pub fn one() -> Self {
        let mut one = Self::zero();
        fiat::fq_set_one(&mut one.0);
        one
    }

    pub fn square(&self) -> Self {
        let mut result = fiat::FqMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        fiat::fq_square(&mut result, &self.0);
        Self(result)
    }

    fn inverse(&self) -> Option<Fq> {
        if self == &Fq::zero() {
            return None;
        }

        const LEN_PRIME: usize = PRIME_ORDER;
        const ITERATIONS: usize = (49 * LEN_PRIME + 57) / 17;

        let mut a = fiat::FqNonMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        fiat::fq_from_montgomery(&mut a, &self.0);
        let mut d = 1;
        let mut f: [u64; NUM_LIMBS + 1] = [0u64; NUM_LIMBS + 1];
        fiat::fq_msat(&mut f);
        let mut g: [u64; NUM_LIMBS + 1] = [0u64; NUM_LIMBS + 1];
        let mut v: [u64; NUM_LIMBS] = [0u64; NUM_LIMBS];
        let mut r: [u64; NUM_LIMBS] = Fq::one().0 .0;
        let mut i = 0;
        let mut j = 0;

        while j < NUM_LIMBS {
            g[j] = a[j];
            j += 1;
        }

        let mut out1: u64 = 0;
        let mut out2: [u64; NUM_LIMBS + 1] = [0; NUM_LIMBS + 1];
        let mut out3: [u64; NUM_LIMBS + 1] = [0; NUM_LIMBS + 1];
        let mut out4: [u64; NUM_LIMBS] = [0; NUM_LIMBS];
        let mut out5: [u64; NUM_LIMBS] = [0; NUM_LIMBS];
        let mut out6: u64 = 0;
        let mut out7: [u64; NUM_LIMBS + 1] = [0; NUM_LIMBS + 1];
        let mut out8: [u64; NUM_LIMBS + 1] = [0; NUM_LIMBS + 1];
        let mut out9: [u64; NUM_LIMBS] = [0; NUM_LIMBS];
        let mut out10: [u64; NUM_LIMBS] = [0; NUM_LIMBS];

        while i < ITERATIONS - ITERATIONS % 2 {
            fiat::fq_divstep(
                &mut out1, &mut out2, &mut out3, &mut out4, &mut out5, d, &f, &g, &v, &r,
            );
            fiat::fq_divstep(
                &mut out6, &mut out7, &mut out8, &mut out9, &mut out10, out1, &out2, &out3, &out4,
                &out5,
            );
            d = out6;
            f = out7;
            g = out8;
            v = out9;
            r = out10;
            i += 2;
        }

        if ITERATIONS % 2 != 0 {
            fiat::fq_divstep(
                &mut out1, &mut out2, &mut out3, &mut out4, &mut out5, d, &f, &g, &v, &r,
            );
            v = out4;
            f = out2;
        }

        let s = ((f[f.len() - 1] >> 64 - 1) & 1) as u8;
        let mut neg = fiat::FqMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        fiat::fq_opp(&mut neg, &fiat::FqMontgomeryDomainFieldElement(v));

        let mut v_prime: [u64; NUM_LIMBS] = [0u64; NUM_LIMBS];
        fiat::fq_selectznz(&mut v_prime, s, &v, &neg.0);

        let mut pre_comp: [u64; NUM_LIMBS] = [0u64; NUM_LIMBS];
        fiat::fq_divstep_precomp(&mut pre_comp);

        let mut result = fiat::FqMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        fiat::fq_mul(
            &mut result,
            &fiat::FqMontgomeryDomainFieldElement(v_prime),
            &fiat::FqMontgomeryDomainFieldElement(pre_comp),
        );

        Some(Fq(result))
    }
}

impl Add<Fq> for Fq {
    type Output = Fq;

    fn add(self, other: Fq) -> Fq {
        let mut result = fiat::FqMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        fiat::fq_add(&mut result, &self.0, &other.0);
        Fq(result)
    }
}

impl Sub<Fq> for Fq {
    type Output = Fq;

    fn sub(self, other: Fq) -> Fq {
        let mut result = fiat::FqMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        fiat::fq_sub(&mut result, &self.0, &other.0);
        Fq(result)
    }
}

impl Mul<Fq> for Fq {
    type Output = Fq;

    fn mul(self, other: Fq) -> Fq {
        let mut result = fiat::FqMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        fiat::fq_mul(&mut result, &self.0, &other.0);
        Fq(result)
    }
}

impl Neg for Fq {
    type Output = Fq;

    fn neg(self) -> Fq {
        let mut result = fiat::FqMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        fiat::fq_opp(&mut result, &self.0);
        Fq(result)
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;
    use proptest::{
        arbitrary::any,
        strategy::{BoxedStrategy, Strategy},
    };

    use super::*;

    fn fp_strategy() -> BoxedStrategy<Fq> {
        any::<[u8; 32]>()
            .prop_map(|bytes| Fq::from_bytes(&bytes))
            .boxed()
    }

    proptest! {
        #[test]
        fn inversion_proptest(element in fp_strategy().prop_filter("Non-zero element", |e| e != &Fq::zero())) {
            let inverse = element.inverse().unwrap();
            assert_eq!(element.mul(inverse), Fq::one());
        }
    }
}
