use ark_ed_on_bls12_377::Fq as ArkworksFq;
use ark_ff::{Field, One, Zero};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

use super::super::{B, N_64, N_8};

const N: usize = N_64;

#[derive(Copy, Clone)]
pub struct Fq(ArkworksFq);

impl PartialEq for Fq {
    fn eq(&self, other: &Self) -> bool {
        match (self.is_sentinel(), other.is_sentinel()) {
            (true, true) => true,
            (true, false) => false,
            (false, true) => false,
            (false, false) => self.0 == other.0,
        }
    }
}

impl Eq for Fq {}

impl zeroize::Zeroize for Fq {
    fn zeroize(&mut self) {
        self.0 .0.zeroize()
    }
}

impl Fq {
    pub(crate) fn from_le_limbs(limbs: [u64; N_64]) -> Fq {
        let x_non_monty = fiat::FqNonMontgomeryDomainFieldElement(limbs);
        let mut x = fiat::FqMontgomeryDomainFieldElement([0; N]);
        fiat::fq_to_montgomery(&mut x, &x_non_monty);
        Self(x)
    }

    pub(crate) fn from_raw_bytes(bytes: &[u8; N_8]) -> Fq {
        let mut x_non_montgomery = fiat::FqNonMontgomeryDomainFieldElement([0; N]);
        let mut x = fiat::FqMontgomeryDomainFieldElement([0; N]);

        fiat::fq_from_bytes(&mut x_non_montgomery.0, &bytes);
        fiat::fq_to_montgomery(&mut x, &x_non_montgomery);

        Self(x)
    }

    pub(crate) fn to_le_limbs(&self) -> [u64; N_64] {
        debug_assert!(!self.is_sentinel());

        let mut x_non_montgomery = fiat::FqNonMontgomeryDomainFieldElement([0; N]);
        fiat::fq_from_montgomery(&mut x_non_montgomery, &self.0);
        x_non_montgomery.0
    }

    pub fn to_bytes_le(&self) -> [u8; N_8] {
        debug_assert!(!self.is_sentinel());

        let mut bytes = [0u8; N_8];
        let mut x_non_montgomery = fiat::FqNonMontgomeryDomainFieldElement([0; N]);
        fiat::fq_from_montgomery(&mut x_non_montgomery, &self.0);
        fiat::fq_to_bytes(&mut bytes, &x_non_montgomery.0);
        bytes
    }

    /// Instantiate a constant field element from its montgomery limbs.
    ///
    /// This should only be used if you are familiar with the internals of the library.
    pub const fn from_montgomery_limbs(limbs: [u64; N]) -> Fq {
        Self(fiat::FqMontgomeryDomainFieldElement(limbs))
    }

    pub const ZERO: Self = Self(ArkworksFq::zero());

    pub const ONE: Self = Self(ArkworksFq::one());

    /// A sentinel value which exists only to not be equal to any other field element.
    ///
    /// Operations involving this element are undefined.
    pub const SENTINEL: Self = Self::from_montgomery_limbs([u64::MAX; N_64]);

    fn is_sentinel(&self) -> bool {
        self.0 .0 == Self::SENTINEL.0 .0
    }

    pub fn square(&self) -> Fq {
        debug_assert!(!self.is_sentinel());
        Fq(self.0.square())
    }

    pub fn inverse(&self) -> Option<Fq> {
        debug_assert!(!self.is_sentinel());

        if self == &Fq::ZERO {
            return None;
        }

        Some(Fq(self.0.inverse()?))
    }

    pub fn add(self, other: &Fq) -> Fq {
        debug_assert!(!self.is_sentinel() && !other.is_sentinel());
        Fq(self.0 + other.0)
    }

    pub fn sub(self, other: &Fq) -> Fq {
        debug_assert!(!self.is_sentinel() && !other.is_sentinel());
        Fq(self.0 - other.0)
    }

    pub fn mul(self, other: &Fq) -> Fq {
        debug_assert!(!self.is_sentinel() && !other.is_sentinel());
        Fq(self.0 * other.0)
    }

    pub fn neg(self) -> Fq {
        debug_assert!(!self.is_sentinel());
        Fq(-self.0)
    }
}

impl ConditionallySelectable for Fq {
    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        let mut out = [0u64; 4];
        for i in 0..4 {
            out[i] = u64::conditional_select(&a.0 .0[i], &b.0 .0[i], choice);
        }
        Self(fiat::FqMontgomeryDomainFieldElement(out))
    }
}

impl ConstantTimeEq for Fq {
    fn ct_eq(&self, other: &Fq) -> Choice {
        self.0.ct_eq(&other.0)
    }
}
