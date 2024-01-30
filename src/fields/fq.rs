// Fiat-crypto generates some unused type aliases, but we don't want to edit the generated code at all.
#![allow(dead_code)]

use cfg_if::cfg_if;

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

<<<<<<< HEAD
impl Fq {
    /// Convert bytes into an Fq element, returning None if these bytes are not already reduced.
    ///
    /// This means that values that cannot be produced by encoding a field element will return
    /// None, enforcing canonical serialization.
    pub fn from_bytes_checked(bytes: &[u8; 32]) -> Option<Self> {
        let reduced = Self::from_raw_bytes(bytes);
        if reduced.to_bytes_le() == *bytes {
            Some(reduced)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_from_bytes_checked() {
        assert_eq!(Fq::from_bytes_checked(&[0; 32]), Some(Fq::zero()));
        assert_eq!(Fq::from_bytes_checked(&[0xFF; 32]), None);
=======
// TODO: Add method for checking the bytes are not larger than the field modulus,
// return None if not, and return Some(Fq) if they are.
impl Fq {
    pub fn from_bytes_check_order(bytes: &[u8; 32]) -> Option<Fq> {
        todo!()
>>>>>>> 1dd9977 (decompression)
    }
}
