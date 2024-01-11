use core::ops::{Add, Mul, Neg, Sub};

use super::fiat;

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
