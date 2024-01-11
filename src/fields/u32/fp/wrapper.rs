use super::fiat;
use core::ops::{Add, Mul, Neg, Sub};

const NUM_LIMBS: usize = 12;
const PRIME_ORDER: usize = 377;

#[derive(Copy, Clone)]
pub struct Fp(fiat::FpMontgomeryDomainFieldElement);

impl core::fmt::Debug for Fp {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let bytes = self.to_bytes();
        write!(f, "Fp(0x{})", hex::encode(bytes))
    }
}

impl PartialEq for Fp {
    fn eq(&self, other: &Fp) -> bool {
        let self_bytes = self.to_bytes();
        let other_bytes = other.to_bytes();
        self_bytes[..] == other_bytes[..]
    }
}

impl Eq for Fp {}

impl Fp {
    pub fn from_bytes(bytes: &[u8; 48]) -> Self {
        let mut x_non_montgomery = fiat::FpNonMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        let mut x = fiat::FpMontgomeryDomainFieldElement([0; NUM_LIMBS]);

        fiat::fp_from_bytes(&mut x_non_montgomery.0, &bytes);
        fiat::fp_to_montgomery(&mut x, &x_non_montgomery);

        Self(x)
    }

    pub fn to_bytes(&self) -> [u8; 48] {
        let mut x_non_montgomery = fiat::FpNonMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        let mut bytes = [0u8; 48];

        fiat::fp_from_montgomery(&mut x_non_montgomery, &self.0);
        fiat::fp_to_bytes(&mut bytes, &x_non_montgomery.0);

        bytes
    }

    pub fn zero() -> Self {
        Self(fiat::FpMontgomeryDomainFieldElement([0; NUM_LIMBS]))
    }

    pub fn one() -> Self {
        let mut one = Self::zero();
        fiat::fp_set_one(&mut one.0);
        one
    }

    pub fn square(&self) -> Self {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        fiat::fp_square(&mut result, &self.0);
        Self(result)
    }

    fn inverse(&self) -> Option<Fp> {
        if self == &Fp::zero() {
            return None;
        }

        const LEN_PRIME: usize = PRIME_ORDER;
        const ITERATIONS: usize = (49 * LEN_PRIME + 57) / 17;

        let mut a = fiat::FpNonMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        fiat::fp_from_montgomery(&mut a, &self.0);
        let mut d = 1;
        let mut f: [u32; NUM_LIMBS + 1] = [0u32; NUM_LIMBS + 1];
        fiat::fp_msat(&mut f);
        let mut g: [u32; NUM_LIMBS + 1] = [0u32; NUM_LIMBS + 1];
        let mut v: [u32; NUM_LIMBS] = [0u32; NUM_LIMBS];
        let mut r: [u32; NUM_LIMBS] = Fp::one().0 .0;
        let mut i = 0;
        let mut j = 0;

        while j < NUM_LIMBS {
            g[j] = a[j];
            j += 1;
        }

        let mut out1: u32 = 0;
        let mut out2: [u32; NUM_LIMBS + 1] = [0; NUM_LIMBS + 1];
        let mut out3: [u32; NUM_LIMBS + 1] = [0; NUM_LIMBS + 1];
        let mut out4: [u32; NUM_LIMBS] = [0; NUM_LIMBS];
        let mut out5: [u32; NUM_LIMBS] = [0; NUM_LIMBS];
        let mut out6: u32 = 0;
        let mut out7: [u32; NUM_LIMBS + 1] = [0; NUM_LIMBS + 1];
        let mut out8: [u32; NUM_LIMBS + 1] = [0; NUM_LIMBS + 1];
        let mut out9: [u32; NUM_LIMBS] = [0; NUM_LIMBS];
        let mut out10: [u32; NUM_LIMBS] = [0; NUM_LIMBS];

        while i < ITERATIONS - ITERATIONS % 2 {
            fiat::fp_divstep(
                &mut out1, &mut out2, &mut out3, &mut out4, &mut out5, d, &f, &g, &v, &r,
            );
            fiat::fp_divstep(
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
            fiat::fp_divstep(
                &mut out1, &mut out2, &mut out3, &mut out4, &mut out5, d, &f, &g, &v, &r,
            );
            v = out4;
            f = out2;
        }

        let s = ((f[f.len() - 1] >> 32 - 1) & 1) as u8;
        let mut neg = fiat::FpMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        fiat::fp_opp(&mut neg, &fiat::FpMontgomeryDomainFieldElement(v));

        let mut v_prime: [u32; NUM_LIMBS] = [0u32; NUM_LIMBS];
        fiat::fp_selectznz(&mut v_prime, s, &v, &neg.0);

        let mut pre_comp: [u32; NUM_LIMBS] = [0u32; NUM_LIMBS];
        fiat::fp_divstep_precomp(&mut pre_comp);

        let mut result = fiat::FpMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        fiat::fp_mul(
            &mut result,
            &fiat::FpMontgomeryDomainFieldElement(v_prime),
            &fiat::FpMontgomeryDomainFieldElement(pre_comp),
        );

        Some(Fp(result))
    }
}

impl Add<Fp> for Fp {
    type Output = Fp;

    fn add(self, other: Fp) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        fiat::fp_add(&mut result, &self.0, &other.0);
        Fp(result)
    }
}

impl Sub<Fp> for Fp {
    type Output = Fp;

    fn sub(self, other: Fp) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        fiat::fp_sub(&mut result, &self.0, &other.0);
        Fp(result)
    }
}

impl Mul<Fp> for Fp {
    type Output = Fp;

    fn mul(self, other: Fp) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        fiat::fp_mul(&mut result, &self.0, &other.0);
        Fp(result)
    }
}

impl Neg for Fp {
    type Output = Fp;

    fn neg(self) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; NUM_LIMBS]);
        fiat::fp_opp(&mut result, &self.0);
        Fp(result)
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

    fn fp_strategy() -> BoxedStrategy<Fp> {
        any::<[u8; 48]>()
            .prop_map(|bytes| Fp::from_bytes(&bytes))
            .boxed()
    }

    proptest! {
        #[test]
        fn inversion_proptest(element in fp_strategy().prop_filter("Non-zero element", |e| e != &Fp::zero())) {
            let inverse = element.inverse().unwrap();
            assert_eq!(element.mul(inverse), Fp::one());
        }
    }
}
