use cfg_if::cfg_if;
use rand_core::CryptoRngCore;

use crate::EncodingError;

#[cfg(feature = "arkworks")]
pub mod arkworks;
mod ops;
mod u32;

#[cfg(not(feature = "u32_backend"))]
mod u64;

cfg_if! {
    if #[cfg(feature = "u32_backend")] {
        pub type Fp = u32::Fp;
    } else {
        pub type Fp = u64::Fp;
    }
}

const B: usize = 377;
const N_8: usize = (B + 7) / 8;
const N_32: usize = (B + 31) / 32;
const N_64: usize = (B + 63) / 64;

impl Fp {
    pub const MODULUS_LIMBS: [u64; N_64] = [
        9586122913090633729,
        1660523435060625408,
        2230234197602682880,
        1883307231910630287,
        14284016967150029115,
        121098312706494698,
    ];

    pub const MODULUS_MINUS_ONE_DIV_TWO_LIMBS: [u64; N_64] = [
        4793061456545316864,
        830261717530312704,
        10338489135656117248,
        10165025652810090951,
        7142008483575014557,
        60549156353247349,
    ];

    pub const MODULUS_BIT_SIZE: u32 = 0x179;

    pub const TRACE_LIMBS: [u64; N_64] = [
        8435453208297608227,
        9853568280881552429,
        7479357291536088013,
        1657802422768920715,
        16796279350917535980,
        1720,
    ];

    pub const TRACE_MINUS_ONE_DIV_TWO_LIMBS: [u64; N_64] = [
        13441098641003579921,
        14150156177295552022,
        12963050682622819814,
        828901211384460357,
        8398139675458767990,
        860,
    ];

    pub const TWO_ADICITY: u32 = 0x2e;

    pub const QUADRATIC_NON_RESIDUE_TO_TRACE: Self = Self::from_montgomery_limbs([
        7563926049028936178,
        2688164645460651601,
        12112688591437172399,
        3177973240564633687,
        14764383749841851163,
        52487407124055189,
    ]);

    pub const MULTIPLICATIVE_GENERATOR: Self = Self::from_montgomery_limbs([
        1580481994230331156,
        7393753505699199837,
        15893201093018099506,
        15064395564155502359,
        7595513421530309810,
        112614884009382239,
    ]);

    pub const TWO_ADIC_ROOT_OF_UNITY: Self = Self::from_montgomery_limbs([
        16125954451488549662,
        8217881455460992412,
        2710394594754331350,
        15576616684900113046,
        13256804877427073124,
        71394035925664393,
    ]);

    pub const FIELD_SIZE_POWER_OF_TWO: Self = Self::from_montgomery_limbs([
        13224372171368877346,
        227991066186625457,
        2496666625421784173,
        13825906835078366124,
        9475172226622360569,
        30958721782860680,
    ]);

    pub fn from_le_bytes_mod_order(bytes: &[u8]) -> Self {
        bytes
            .chunks(N_8)
            .map(|x| {
                let mut padded = [0u8; N_8];
                padded[..x.len()].copy_from_slice(x);
                Self::from_raw_bytes(&padded)
            }) // [X, 2^(384) * X, ...]
            .rev()
            .fold(Self::ZERO, |acc, x| {
                acc * (Self::FIELD_SIZE_POWER_OF_TWO) + x
            }) // let acc =
    }

    /// Convert bytes into an Fp element, returning None if these bytes are not already reduced.
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
        assert_eq!(Fp::from_bytes_checked(&[0; N_8]), Ok(Fp::ZERO));
        assert!(Fp::from_bytes_checked(&[0xFF; N_8]).is_err());
    }
}
