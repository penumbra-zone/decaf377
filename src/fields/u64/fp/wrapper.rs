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
        let mut x_non_montgomery = fiat::FpNonMontgomeryDomainFieldElement([0; 6]);
        let mut x = fiat::FpMontgomeryDomainFieldElement([0; 6]);

        fiat::fp_from_bytes(&mut x_non_montgomery.0, &bytes);
        fiat::fp_to_montgomery(&mut x, &x_non_montgomery);

        Self(x)
    }

    pub fn to_bytes(&self) -> [u8; 48] {
        let mut x_non_montgomery = fiat::FpNonMontgomeryDomainFieldElement([0; 6]);
        let mut bytes = [0u8; 48];

        fiat::fp_from_montgomery(&mut x_non_montgomery, &self.0);
        fiat::fp_to_bytes(&mut bytes, &x_non_montgomery.0);

        bytes
    }

    pub fn zero() -> Self {
        Self(fiat::FpMontgomeryDomainFieldElement([0; 6]))
    }

    pub fn one() -> Self {
        let mut one = Self::zero();
        fiat::fp_set_one(&mut one.0);
        one
    }

    pub fn square(&self) -> Self {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; 6]);
        fiat::fp_square(&mut result, &self.0);
        Self(result)
    }
}

impl Add<Fp> for Fp {
    type Output = Fp;

    fn add(self, other: Fp) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; 6]);
        fiat::fp_add(&mut result, &self.0, &other.0);
        Fp(result)
    }
}

impl Sub<Fp> for Fp {
    type Output = Fp;

    fn sub(self, other: Fp) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; 6]);
        fiat::fp_sub(&mut result, &self.0, &other.0);
        Fp(result)
    }
}

impl Mul<Fp> for Fp {
    type Output = Fp;

    fn mul(self, other: Fp) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; 6]);
        fiat::fp_mul(&mut result, &self.0, &other.0);
        Fp(result)
    }
}

impl Neg for Fp {
    type Output = Fp;

    fn neg(self) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; 6]);
        fiat::fp_opp(&mut result, &self.0);
        Fp(result)
    }
}
