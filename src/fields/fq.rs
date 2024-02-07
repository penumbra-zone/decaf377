// Fiat-crypto generates some unused type aliases, but we don't want to edit the generated code at all.
#![allow(dead_code)]

use cfg_if::cfg_if;

use crate::EncodingError;

#[cfg(feature = "arkworks")]
pub mod arkworks;
mod ops;
mod u32;
mod u64;

cfg_if! {
    if #[cfg(feature = "u32_backend")] {
        pub type Fq = u32::Fq;
    } else {
        pub type Fq = u64::Fq;
    }
}

const B: usize = 253;
const N_8: usize = (B + 7) / 8;
const N_32: usize = (B + 31) / 32;
const N_64: usize = (B + 63) / 64;

impl Fq {
    pub const MODULUS_LIMBS: [u64; N_64] = [
        725501752471715841,
        6461107452199829505,
        6968279316240510977,
        1345280370688173398,
    ];

    pub const MODULUS_MINUS_ONE_DIV_TWO_LIMBS: [u64; N_64] = [
        9586122913090633728,
        12453925762954690560,
        3484139658120255488,
        672640185344086699,
    ];

    pub const MODULUS_BIT_SIZE: u32 = 0xfd;

    pub const TRACE_LIMBS: [u64; N_64] = [
        17149038877957297187,
        11113960768935211860,
        14608890324369326440,
        9558,
    ];

    pub const TRACE_MINUS_ONE_DIV_TWO_LIMBS: [u64; N_64] = [
        8574519438978648593,
        5556980384467605930,
        7304445162184663220,
        4779,
    ];

    // c1
    pub const TWO_ADICITY: u32 = 0x2f;

    pub const QUADRATIC_NON_RESIDUE_TO_TRACE: Self = Self::from_montgomery_limbs([
        4340692304772210610,
        11102725085307959083,
        15540458298643990566,
        944526744080888988,
    ]);

    pub const MULTIPLICATIVE_GENERATOR: Self = Self::from_montgomery_limbs([
        2984901390528151251,
        10561528701063790279,
        5476750214495080041,
        898978044469942640,
    ]);

    pub const TWO_ADIC_ROOT_OF_UNITY: Self = Self::from_montgomery_limbs([
        12646347781564978760,
        6783048705277173164,
        268534165941069093,
        1121515446318641358,
    ]);

    pub const FIELD_SIZE_POWER_OF_TWO: Self = Self::from_montgomery_limbs([
        2726216793283724667,
        14712177743343147295,
        12091039717619697043,
        81024008013859129,
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

    /// Convert bytes into an Fq element, returning None if these bytes are not already reduced.
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
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_from_bytes_checked() {
        assert_eq!(Fq::from_bytes_checked(&[0; N_8]), Ok(Fq::ZERO));
        assert!(Fq::from_bytes_checked(&[0xFF; N_8]).is_err());
    }
}
