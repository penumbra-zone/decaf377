use ark_ed_on_bls12_377::Fr as ArkworksFr;
use ark_ff::{biginteger::BigInt, Field, PrimeField, UniformRand};
use ark_serialize::CanonicalSerialize;
use ark_std::rand::Rng;
use rand_core::CryptoRngCore;

use super::super::{N_64, N_8};

const N: usize = N_64;

#[derive(Copy, Clone)]
pub struct Fr(ArkworksFr);

impl PartialEq for Fr {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for Fr {}

impl zeroize::Zeroize for Fr {
    fn zeroize(&mut self) {
        self.0 .0.zeroize()
    }
}

impl Fr {
    /// Converts `Fr` to `ArkworksFr`
    pub fn as_inner(&self) -> &ArkworksFr {
        &self.0
    }

    pub fn into_inner(self) -> ArkworksFr {
        self.0
    }

    pub fn rand<R: CryptoRngCore + Rng>(rng: &mut R) -> Self {
        Self(UniformRand::rand(rng))
    }

    pub fn from_le_bytes_mod_order(bytes: &[u8]) -> Self {
        Self(ArkworksFr::from_le_bytes_mod_order(bytes))
    }

    pub(crate) fn from_le_limbs(limbs: [u64; N_64]) -> Fr {
        Self(
            ArkworksFr::from_bigint(ark_ff::BigInt(limbs))
                .expect("Invalid field element: out of range"),
        )
    }

    pub(crate) fn to_le_limbs(&self) -> [u64; N_64] {
        self.0.into_bigint().0
    }

    pub fn to_bytes_le(&self) -> [u8; N_8] {
        let mut bytes = [0u8; 32];
        self.0
            .serialize_compressed(&mut bytes[..])
            .expect("serialization into array should be infallible");
        bytes
    }

    pub(crate) const fn from_montgomery_limbs(limbs: [u64; N]) -> Fr {
        Self(ArkworksFr::new_unchecked(BigInt::new(limbs)))
    }

    pub const ZERO: Self = Self(ArkworksFr::new(BigInt::new([0; N])));
    pub const ONE: Self = Self(ArkworksFr::new(BigInt::one()));

    pub fn square(&self) -> Fr {
        Fr(self.0.square())
    }

    pub fn inverse(&self) -> Option<Fr> {
        if self == &Self::ZERO {
            return None;
        }

        Some(Fr(self.0.inverse()?))
    }

    pub fn add(self, other: &Fr) -> Fr {
        Fr(self.0 + other.0)
    }

    pub fn sub(self, other: &Fr) -> Fr {
        Fr(self.0 - other.0)
    }

    pub fn mul(self, other: &Fr) -> Fr {
        Fr(self.0 * other.0)
    }

    pub fn neg(self) -> Fr {
        Fr(-self.0)
    }
}
