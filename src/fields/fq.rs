// Fiat-crypto generates some unused type aliases, but we don't want to edit the generated code at all.
#![allow(dead_code)]

use cfg_if::cfg_if;

use crate::EncodingError;

#[cfg(feature = "arkworks")]
pub mod arkworks;
mod ops;
pub mod u32;
pub mod u64;

cfg_if! {
    if #[cfg(feature = "u32_backend")] {
        pub type Fq = u32::Fq;

        pub mod arkworks_constants {
            pub use super::u32::arkworks_constants::*;
        }
    } else {
        pub type Fq = u64::Fq;

        pub mod arkworks_constants {
            pub use super::u64::arkworks_constants::*;
        }
    }
}

impl Fq {
    /// Convert bytes into an Fq element, returning None if these bytes are not already reduced.
    ///
    /// This means that values that cannot be produced by encoding a field element will return
    /// None, enforcing canonical serialization.
    pub fn from_bytes_checked(bytes: &[u8; 32]) -> Result<Self, EncodingError> {
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
        assert_eq!(Fq::from_bytes_checked(&[0; 32]), Ok(Fq::zero()));
        assert!(Fq::from_bytes_checked(&[0xFF; 32]).is_err());
    }
}
