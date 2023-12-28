use core::ops::{Add, Mul, Neg, Sub};

use super::fiat;

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
        let mut x_non_montgomery = fiat::FpNonMontgomeryDomainFieldElement([0; 12]);
        let mut x = fiat::FpMontgomeryDomainFieldElement([0; 12]);

        fiat::fp_from_bytes(&mut x_non_montgomery.0, &bytes);
        fiat::fp_to_montgomery(&mut x, &x_non_montgomery);

        Self(x)
    }

    pub fn to_bytes(&self) -> [u8; 48] {
        let mut x_non_montgomery = fiat::FpNonMontgomeryDomainFieldElement([0; 12]);
        let mut bytes = [0u8; 48];

        fiat::fp_from_montgomery(&mut x_non_montgomery, &self.0);
        fiat::fp_to_bytes(&mut bytes, &x_non_montgomery.0);

        bytes
    }

    pub fn zero() -> Self {
        Self(fiat::FpMontgomeryDomainFieldElement([0; 12]))
    }

    pub fn one() -> Self {
        let mut one = Self::zero();
        fiat::fp_set_one(&mut one.0);
        one
    }

    pub fn square(&self) -> Self {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; 12]);
        fiat::fp_square(&mut result, &self.0);
        Self(result)
    }

    fn div(&self) -> Fp {
        const LEN_PRIME: usize = 377;
        const ITERATIONS: usize = (49 * LEN_PRIME + 57) / 17;

        let mut a = fiat::FpNonMontgomeryDomainFieldElement([0; 12]);
        fiat::fp_from_montgomery(&mut a, &self.0);       
        let mut d = 1;
        let mut f: [u32; 13] = [0u32; 13];
        fiat::fp_msat(&mut f);
        let mut g = [0u32; 13]; 
        let mut v = [0u32; 12];
        let mut r: [u32; 12] = Fp::one().0.0;
        let mut i = 0;
        let mut j = 0;

        while j < 6 { 
            g[j] = a[j];
            j += 1;
        }

        while i < ITERATIONS - ITERATIONS % 2 {
            let (out1, out2, out3, out4, out5) = fiat::fp_divstep(d, &f, &g, &v, &r);
            let (out1, out2, out3, out4, out5) = fiat::fp_divstep(out1, &out2, &out3, &out4, &out5);
            d = out1;
            f = out2;
            g = out3;
            v = out4;
            r = out5;
            i += 2;
        }

        if ITERATIONS % 2 != 0 {
            let (_out1, out2, _out3, out4, _out5) = fiat::fp_divstep(d, &f, &g, &v, &r);
            v = out4;
            f = out2;
        }

        let s = ((f[f.len() - 1] >> 32 - 1) & 1) as u8;
        let mut neg = fiat::FpMontgomeryDomainFieldElement([0; 12]);
        fiat::fp_opp(&mut neg, &fiat::FpMontgomeryDomainFieldElement(v));

        let mut v_prime: [u32; 12] = [0u32; 12]; 
        fiat::fp_selectznz(&mut v_prime, s, &v, &neg.0);

        let mut pre_comp: [u32; 12] = [0u32; 12]; 
        fiat::fp_divstep_precomp(&mut pre_comp);

        let mut result = fiat::FpMontgomeryDomainFieldElement([0; 12]);
        fiat::fp_mul(&mut result, &fiat::FpMontgomeryDomainFieldElement(v_prime), &fiat::FpMontgomeryDomainFieldElement(pre_comp));
        
        Fp(result)
    }
}

impl Add<Fp> for Fp {
    type Output = Fp;

    fn add(self, other: Fp) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; 12]);
        fiat::fp_add(&mut result, &self.0, &other.0);
        Fp(result)
    }
}

impl Sub<Fp> for Fp {
    type Output = Fp;

    fn sub(self, other: Fp) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; 12]);
        fiat::fp_sub(&mut result, &self.0, &other.0);
        Fp(result)
    }
}

impl Mul<Fp> for Fp {
    type Output = Fp;

    fn mul(self, other: Fp) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; 12]);
        fiat::fp_mul(&mut result, &self.0, &other.0);
        Fp(result)
    }
}

impl Neg for Fp {
    type Output = Fp;

    fn neg(self) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; 12]);
        fiat::fp_opp(&mut result, &self.0);
        Fp(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::println;

    #[test]
    fn inversion_test() {
        let one = Fp::one();
        let one_invert = one.div();
        assert_eq!(one_invert, one);

        let three = Fp::one().add(Fp::one().add(Fp::one()));
        let three_invert = three.div();
        assert_eq!(three.mul(three_invert), Fp::one());
    }
}