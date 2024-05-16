use ark_bls12_377::Fq as ArkworksFp;
use ark_ff::{BigInt, Field, PrimeField};
use ark_serialize::CanonicalSerialize;

use super::super::{N_64, N_8};

const N: usize = N_64;

#[derive(Copy, Clone)]
pub struct Fp(ArkworksFp);

impl PartialEq for Fp {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for Fp {}

impl zeroize::Zeroize for Fp {
    fn zeroize(&mut self) {
        self.0 .0.zeroize()
    }
}

impl Fp {
    pub(crate) fn from_le_limbs(limbs: [u64; N_64]) -> Fp {
        let mut bytes = [0u8; N_8];
        for i in 0..N_64 {
            let this_byte = limbs[i].to_le_bytes();
            for j in 0..8 {
                bytes[8 * i + j] = this_byte[j];
            }
        }

        Self::from_raw_bytes(&bytes)
    }

    pub(crate) fn from_raw_bytes(bytes: &[u8; N_8]) -> Fp {
        Self(ArkworksFp::from_le_bytes_mod_order(bytes))
    }

    pub(crate) fn to_le_limbs(&self) -> [u64; N_64] {
        let le_bytes = self.to_bytes_le();
        let mut out = [0u64; N_64];
        for i in 0..N_64 {
            out[i] = u64::from_le_bytes([
                le_bytes[8 * i],
                le_bytes[8 * i + 1],
                le_bytes[8 * i + 2],
                le_bytes[8 * i + 3],
                le_bytes[8 * i + 4],
                le_bytes[8 * i + 5],
                le_bytes[8 * i + 6],
                le_bytes[8 * i + 7],
            ]);
        }
        out
    }

    pub fn to_bytes_le(&self) -> [u8; N_8] {
        let mut bytes = [0u8; 48];
        self.0
            .serialize_compressed(&mut bytes[..])
            .expect("serialization into array should be infallible");
        bytes
    }

    pub(crate) const fn from_montgomery_limbs(limbs: [u64; N]) -> Fp {
        Self(ArkworksFp::new_unchecked(BigInt(limbs)))
    }

    pub const ZERO: Self = Self(ArkworksFp::new(BigInt::new([0; N])));
    pub const ONE: Self = Self(ArkworksFp::new(BigInt::one()));

    pub const MINUS_ONE: Self = Self::from_montgomery_limbs([
        9384023879812382873,
        14252412606051516495,
        9184438906438551565,
        11444845376683159689,
        8738795276227363922,
        81297770384137296,
    ]);

    pub const QUADRATIC_NON_RESIDUE: Self = Self::from_montgomery_limbs([
        18161750659790013178,
        10940260503947051403,
        2338003791965605956,
        14680817040264804354,
        841925479686732267,
        43193913801202386,
    ]);

    pub fn square(&self) -> Fp {
        Fp(self.0.square())
    }

    pub fn inverse(&self) -> Option<Self> {
        if self == &Self::ZERO {
            return None;
        }

        Some(Fp(self.0.inverse()?))
    }

    pub fn add(self, other: &Fp) -> Fp {
        Fp(self.0 + other.0)
    }

    pub fn sub(self, other: &Fp) -> Fp {
        Fp(self.0 - other.0)
    }

    pub fn mul(self, other: &Fp) -> Fp {
        Fp(self.0 * other.0)
    }

    pub fn neg(self) -> Fp {
        Fp(-self.0)
    }
}
