use crate::{EncodingError, Fq, Fr};

/// An extension trait for easy conversion of [`Fr`] and [`Fq`] elements to and from bytes.
pub trait FieldExt: Sized {
    /// Serializes an element to 32 bytes.
    fn to_bytes(&self) -> [u8; 32];
    /// Deserializes an element from 32 bytes.
    fn from_bytes(bytes: [u8; 32]) -> Result<Self, EncodingError>;
}

impl FieldExt for Fr {
    fn to_bytes(&self) -> [u8; 32] {
        self.to_bytes_le()
    }

    fn from_bytes(bytes: [u8; 32]) -> Result<Self, EncodingError> {
        Fr::from_bytes_checked(&bytes)
    }
}

impl FieldExt for Fq {
    fn to_bytes(&self) -> [u8; 32] {
        let bytes = self.to_bytes_le();
        debug_assert!(bytes[31] >> 5 == 0u8);
        bytes
    }

    fn from_bytes(bytes: [u8; 32]) -> Result<Self, EncodingError> {
        Fq::from_bytes_checked(&bytes)
    }
}
