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
        let mut x_non_montgomery = fiat::FrNonMontgomeryDomainFieldElement([0; 8]);
        let mut x = fiat::FrMontgomeryDomainFieldElement([0; 8]);

        fiat::fr_from_bytes(&mut x_non_montgomery.0, &bytes);
        fiat::fr_to_montgomery(&mut x, &x_non_montgomery);

        Self(x)
    }

    pub fn to_bytes(&self) -> [u8; 32] {
        let mut x_non_montgomery = fiat::FrNonMontgomeryDomainFieldElement([0; 8]);
        let mut bytes = [0u8; 32];

        fiat::fr_from_montgomery(&mut x_non_montgomery, &self.0);
        fiat::fr_to_bytes(&mut bytes, &x_non_montgomery.0);

        bytes
    }

    pub fn zero() -> Self {
        Self(fiat::FrMontgomeryDomainFieldElement([0; 8]))
    }

    pub fn one() -> Self {
        let mut one = Self::zero();
        fiat::fr_set_one(&mut one.0);
        one
    }

    pub fn square(&self) -> Self {
        let mut result = fiat::FrMontgomeryDomainFieldElement([0; 8]);
        fiat::fr_square(&mut result, &self.0);
        Self(result)
    }

    fn div(&self) -> Fr {
        const LEN_PRIME: usize = 251;
        const ITERATIONS: usize = (49 * LEN_PRIME + 57) / 17;

        let mut a = fiat::FrNonMontgomeryDomainFieldElement([0; 8]);
        fiat::fr_from_montgomery(&mut a, &self.0);
        let mut d = 1;
        let mut f: [u32; 9] = [0u32; 9];
        fiat::fr_msat(&mut f);
        let mut g = [0u32; 9];
        let mut v = [0u32; 8];
        let mut r: [u32; 8] = Fr::one().0 .0;
        let mut i = 0;
        let mut j = 0;

        while j < 8 {
            g[j] = a[j];
            j += 1;
        }

        while i < ITERATIONS - ITERATIONS % 2 {
            let (out1, out2, out3, out4, out5) = fiat::fr_divstep(d, &f, &g, &v, &r);
            let (out1, out2, out3, out4, out5) = fiat::fr_divstep(out1, &out2, &out3, &out4, &out5);
            d = out1;
            f = out2;
            g = out3;
            v = out4;
            r = out5;
            i += 2;
        }

        if ITERATIONS % 2 != 0 {
            let (_out1, out2, _out3, out4, _out5) = fiat::fr_divstep(d, &f, &g, &v, &r);
            v = out4;
            f = out2;
        }

        let s = ((f[f.len() - 1] >> 32 - 1) & 1) as u8;
        let mut neg = fiat::FrMontgomeryDomainFieldElement([0; 8]);
        fiat::fr_opp(&mut neg, &fiat::FrMontgomeryDomainFieldElement(v));

        let mut v_prime: [u32; 8] = [0u32; 8];
        fiat::fr_selectznz(&mut v_prime, s, &v, &neg.0);

        let mut pre_comp: [u32; 8] = [0u32; 8];
        fiat::fr_divstep_precomp(&mut pre_comp);

        let mut result = fiat::FrMontgomeryDomainFieldElement([0; 8]);
        fiat::fr_mul(
            &mut result,
            &fiat::FrMontgomeryDomainFieldElement(v_prime),
            &fiat::FrMontgomeryDomainFieldElement(pre_comp),
        );

        Fr(result)
    }
}

impl Add<Fr> for Fr {
    type Output = Fr;

    fn add(self, other: Fr) -> Fr {
        let mut result = fiat::FrMontgomeryDomainFieldElement([0; 8]);
        fiat::fr_add(&mut result, &self.0, &other.0);
        Fr(result)
    }
}

impl Sub<Fr> for Fr {
    type Output = Fr;

    fn sub(self, other: Fr) -> Fr {
        let mut result = fiat::FrMontgomeryDomainFieldElement([0; 8]);
        fiat::fr_sub(&mut result, &self.0, &other.0);
        Fr(result)
    }
}

impl Mul<Fr> for Fr {
    type Output = Fr;

    fn mul(self, other: Fr) -> Fr {
        let mut result = fiat::FrMontgomeryDomainFieldElement([0; 8]);
        fiat::fr_mul(&mut result, &self.0, &other.0);
        Fr(result)
    }
}

impl Neg for Fr {
    type Output = Fr;

    fn neg(self) -> Fr {
        let mut result = fiat::FrMontgomeryDomainFieldElement([0; 8]);
        fiat::fr_opp(&mut result, &self.0);
        Fr(result)
    }
}

mod tests {
    use super::*;

    #[test]
    fn inversion_test() {
        let one = Fr::one();
        let one_invert = one.div();
        assert_eq!(one_invert, one);

        let three = Fr::one().add(Fr::one().add(Fr::one()));
        let three_invert = three.div();
        assert_eq!(three.mul(three_invert), Fr::one());
    }
}
