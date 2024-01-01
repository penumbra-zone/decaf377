use super::fiat;
use core::ops::{Add, Mul, Neg, Sub};

#[derive(Copy, Clone)]
pub struct Fr(fiat::FrMontgomeryDomainFieldElement);

impl core::fmt::Debug for Fr {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let bytes = self.to_bytes();
        write!(f, "Fr(0x{})", hex::encode(bytes))
    }
}

impl PartialEq for Fr {
    fn eq(&self, other: &Fr) -> bool {
        let self_bytes = self.to_bytes();
        let other_bytes = other.to_bytes();
        self_bytes[..] == other_bytes[..]
    }
}

impl Eq for Fr {}

impl Fr {
    pub fn from_bytes(bytes: &[u8; 32]) -> Self {
        let mut x_non_montgomery = fiat::FrNonMontgomeryDomainFieldElement([0; 4]);
        let mut x = fiat::FrMontgomeryDomainFieldElement([0; 4]);

        fiat::fr_from_bytes(&mut x_non_montgomery.0, &bytes);
        fiat::fr_to_montgomery(&mut x, &x_non_montgomery);

        Self(x)
    }

    pub fn to_bytes(&self) -> [u8; 32] {
        let mut x_non_montgomery = fiat::FrNonMontgomeryDomainFieldElement([0; 4]);
        let mut bytes = [0u8; 32];

        fiat::fr_from_montgomery(&mut x_non_montgomery, &self.0);
        fiat::fr_to_bytes(&mut bytes, &x_non_montgomery.0);

        bytes
    }

    pub fn zero() -> Self {
        Self(fiat::FrMontgomeryDomainFieldElement([0; 4]))
    }

    pub fn one() -> Self {
        let mut one = Self::zero();
        fiat::fr_set_one(&mut one.0);
        one
    }

    pub fn square(&self) -> Self {
        let mut result = fiat::FrMontgomeryDomainFieldElement([0; 4]);
        fiat::fr_square(&mut result, &self.0);
        Self(result)
    }

    fn inverse(&self) -> Option<Fr> {
        if self == &Fr::zero() {
            return None;
        }

        const LEN_PRIME: usize = 251;
        const ITERATIONS: usize = (49 * LEN_PRIME + 57) / 17;

        let mut a = fiat::FrNonMontgomeryDomainFieldElement([0; 4]);
        fiat::fr_from_montgomery(&mut a, &self.0);
        let mut d = 1;
        let mut f: [u64; 5] = [0u64; 5];
        fiat::fr_msat(&mut f);
        let mut g = [0u64; 5];
        let mut v = [0u64; 4];
        let mut r: [u64; 4] = Fr::one().0 .0;
        let mut i = 0;
        let mut j = 0;

        while j < 4 {
            g[j] = a[j];
            j += 1;
        }

        let mut out1: u64 = 0;
        let mut out2: [u64; 5] = [0; 5];
        let mut out3: [u64; 5] = [0; 5];
        let mut out4: [u64; 4] = [0; 4];
        let mut out5: [u64; 4] = [0; 4];
        let mut out6: u64 = 0;
        let mut out7: [u64; 5] = [0; 5];
        let mut out8: [u64; 5] = [0; 5];
        let mut out9: [u64; 4] = [0; 4];
        let mut out10: [u64; 4] = [0; 4];

        while i < ITERATIONS - ITERATIONS % 2 {
            fiat::fr_divstep(
                &mut out1, &mut out2, &mut out3, &mut out4, &mut out5, d, &f, &g, &v, &r,
            );
            fiat::fr_divstep(
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
            fiat::fr_divstep(
                &mut out1, &mut out2, &mut out3, &mut out4, &mut out5, d, &f, &g, &v, &r,
            );
            v = out4;
            f = out2;
        }

        let s = ((f[f.len() - 1] >> 64 - 1) & 1) as u8;
        let mut neg = fiat::FrMontgomeryDomainFieldElement([0; 4]);
        fiat::fr_opp(&mut neg, &fiat::FrMontgomeryDomainFieldElement(v));

        let mut v_prime: [u64; 4] = [0u64; 4];
        fiat::fr_selectznz(&mut v_prime, s, &v, &neg.0);

        let mut pre_comp: [u64; 4] = [0u64; 4];
        fiat::fr_divstep_precomp(&mut pre_comp);

        let mut result = fiat::FrMontgomeryDomainFieldElement([0; 4]);
        fiat::fr_mul(
            &mut result,
            &fiat::FrMontgomeryDomainFieldElement(v_prime),
            &fiat::FrMontgomeryDomainFieldElement(pre_comp),
        );

        Some(Fr(result))
    }
}

impl Add<Fr> for Fr {
    type Output = Fr;

    fn add(self, other: Fr) -> Fr {
        let mut result = fiat::FrMontgomeryDomainFieldElement([0; 4]);
        fiat::fr_add(&mut result, &self.0, &other.0);
        Fr(result)
    }
}

impl Sub<Fr> for Fr {
    type Output = Fr;

    fn sub(self, other: Fr) -> Fr {
        let mut result = fiat::FrMontgomeryDomainFieldElement([0; 4]);
        fiat::fr_sub(&mut result, &self.0, &other.0);
        Fr(result)
    }
}

impl Mul<Fr> for Fr {
    type Output = Fr;

    fn mul(self, other: Fr) -> Fr {
        let mut result = fiat::FrMontgomeryDomainFieldElement([0; 4]);
        fiat::fr_mul(&mut result, &self.0, &other.0);
        Fr(result)
    }
}

impl Neg for Fr {
    type Output = Fr;

    fn neg(self) -> Fr {
        let mut result = fiat::FrMontgomeryDomainFieldElement([0; 4]);
        fiat::fr_opp(&mut result, &self.0);
        Fr(result)
    }
}

mod tests {
    use super::*;

    #[test]
    fn inversion_test() {
        let one = Fr::one();
        let one_invert = one.inverse().unwrap();
        assert_eq!(one_invert, one);

        let three = Fr::one().add(Fr::one().add(Fr::one()));
        let three_invert = three.inverse().unwrap();
        assert_eq!(three.mul(three_invert), Fr::one());
    }
}
