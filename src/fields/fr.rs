use cfg_if::cfg_if;
#[cfg(feature = "std")]
use rand_core::CryptoRngCore;

use crate::EncodingError;

#[cfg(feature = "arkworks")]
pub mod arkworks;
mod ops;
pub mod u32;
pub mod u64;

cfg_if! {
    if #[cfg(feature = "u32_backend")] {
        pub type Fr = u32::Fr;
    } else {
        pub type Fr = u64::Fr;
    }
}

const B: usize = 251;
const N_8: usize = (B + 7) / 8;
const N_32: usize = (B + 31) / 32;
const N_64: usize = (B + 63) / 64;

impl Fr {
    pub const MODULUS_LIMBS: [u64; N_64] = [
        13356249993388743167,
        5950279507993463550,
        10965441865914903552,
        336320092672043349,
    ];

    pub const MODULUS_MINUS_ONE_DIV_TWO_LIMBS: [u64; N_64] = [
        6678124996694371583,
        2975139753996731775,
        14706092969812227584,
        168160046336021674,
    ];

    pub const MODULUS_BIT_SIZE: u32 = 0xfb;

    pub const TRACE_LIMBS: [u64; N_64] = [
        4478124994494371583,
        2975139753994731775,
        14704092949812227584,
        148140044334021474,
    ];

    pub const TRACE_MINUS_ONE_DIV_TWO_LIMBS: [u64; N_64] = [
        12542434535201941599,
        1487549874998345887,
        7353044484904113792,
        84080023148010837,
    ];

    pub const TWO_ADICITY: u32 = 0x1;

    pub const MULTIPLICATIVE_GENERATOR: Self = Self::from_montgomery_limbs([
        11289572479485143824,
        11383437349941080925,
        2288212753973340071,
        82014974407880291,
    ]);

    pub const TWO_ADIC_ROOT_OF_UNITY: Self = Self::from_montgomery_limbs([
        15170730741708341141,
        13470723484578117817,
        12803492244414043445,
        50841023252832411,
    ]);

    pub const FIELD_SIZE_POWER_OF_TWO: Self = Self::from_montgomery_limbs([
        3987543627614508126,
        17742427666091596403,
        14557327917022607905,
        322810149704226881,
    ]);

    pub fn from_le_bytes_mod_order(bytes: &[u8]) -> Self {
        bytes
            .chunks(N_8)
            .map(|x| {
                let mut padded = [0u8; N_8];
                padded[..x.len()].copy_from_slice(x);
                Self::from_raw_bytes(&padded)
            }) // [X, 2^(256) * X, ...]
            .rev()
            .fold(Self::ZERO, |acc, x| {
                acc * (Self::FIELD_SIZE_POWER_OF_TWO) + x
            }) // let acc =
    }

    /// Convert bytes into an Fr element, returning None if these bytes are not already reduced.
    ///
    /// This means that values that cannot be produced by encoding a field element will return
    /// None, enforcing canonical serialization.
    pub fn from_bytes_checked(bytes: &[u8; N_8]) -> Result<Self, EncodingError> {
        let reduced = Self::from_raw_bytes(bytes);
        if reduced.to_bytes_le() == *bytes {
            Ok(reduced)
        } else {
            Err(EncodingError::InvalidEncoding)
        }
    }

    pub fn to_bytes(&self) -> [u8; N_8] {
        self.to_bytes_le()
    }

    #[cfg(feature = "std")]
    /// Sample a random field element uniformly.
    pub fn rand<R: CryptoRngCore>(rng: &mut R) -> Self {
        // Sample wide, reduce
        let bytes = {
            let mut out = [0u8; N_8 + 16];
            rng.fill_bytes(&mut out);
            out
        };
        Self::from_le_bytes_mod_order(&bytes)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_from_bytes_checked() {
        assert_eq!(Fr::from_bytes_checked(&[0; N_8]), Ok(Fr::ZERO));
        assert!(Fr::from_bytes_checked(&[0xFF; N_8]).is_err());
    }
}
