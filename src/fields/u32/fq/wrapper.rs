use core::ops::{Add, Mul, Neg, Sub};

use super::fiat;

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
        let mut x_non_montgomery = fiat::FqNonMontgomeryDomainFieldElement([0; 8]);
        let mut x = fiat::FqMontgomeryDomainFieldElement([0; 8]);

        fiat::fq_from_bytes(&mut x_non_montgomery.0, &bytes);
        fiat::fq_to_montgomery(&mut x, &x_non_montgomery);

        Self(x)
    }

    pub fn to_bytes(&self) -> [u8; 32] {
        let mut x_non_montgomery = fiat::FqNonMontgomeryDomainFieldElement([0; 8]);
        let mut bytes = [0u8; 32];

        fiat::fq_from_montgomery(&mut x_non_montgomery, &self.0);
        fiat::fq_to_bytes(&mut bytes, &x_non_montgomery.0);

        bytes
    }

    pub fn zero() -> Self {
        Self(fiat::FqMontgomeryDomainFieldElement([0; 8]))
    }

    pub fn one() -> Self {
        let mut one = Self::zero();
        fiat::fq_set_one(&mut one.0);
        one
    }

    pub fn square(&self) -> Self {
        let mut result = fiat::FqMontgomeryDomainFieldElement([0; 8]);
        fiat::fq_square(&mut result, &self.0);
        Self(result)
    }
}

impl Add<Fq> for Fq {
    type Output = Fq;

    fn add(self, other: Fq) -> Fq {
        let mut result = fiat::FqMontgomeryDomainFieldElement([0; 8]);
        fiat::fq_add(&mut result, &self.0, &other.0);
        Fq(result)
    }
}

impl Sub<Fq> for Fq {
    type Output = Fq;

    fn sub(self, other: Fq) -> Fq {
        let mut result = fiat::FqMontgomeryDomainFieldElement([0; 8]);
        fiat::fq_sub(&mut result, &self.0, &other.0);
        Fq(result)
    }
}

impl Mul<Fq> for Fq {
    type Output = Fq;

    fn mul(self, other: Fq) -> Fq {
        let mut result = fiat::FqMontgomeryDomainFieldElement([0; 8]);
        fiat::fq_mul(&mut result, &self.0, &other.0);
        Fq(result)
    }
}

impl Neg for Fq {
    type Output = Fq;

    fn neg(self) -> Fq {
        let mut result = fiat::FqMontgomeryDomainFieldElement([0; 8]);
        fiat::fq_opp(&mut result, &self.0);
        Fq(result)
    }
}
