use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

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
        let mut bytes = [0u8; 32];
        debug_assert_eq!(self.serialized_size(), 32);
        self.serialize(&mut bytes[..])
            .expect("serialization into array should be infallible");
        bytes
    }

    fn from_bytes(bytes: [u8; 32]) -> Result<Self, EncodingError> {
        Self::deserialize(&bytes[..]).map_err(|_| EncodingError::InvalidEncoding)
    }
}

impl FieldExt for Fq {
    fn to_bytes(&self) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        debug_assert_eq!(self.serialized_size(), 32);
        self.serialize(&mut bytes[..])
            .expect("serialization into array should be infallible");
        debug_assert!(bytes[31] >> 5 == 0u8);

        bytes
    }

    fn from_bytes(bytes: [u8; 32]) -> Result<Self, EncodingError> {
        // Check the top three bits of the last byte as Arkworks
        // doesn't check them when deciding if an encoding is canonical.
        if bytes[31] >> 5 != 0u8 {
            return Err(EncodingError::InvalidEncoding);
        }

        Self::deserialize(&bytes[..]).map_err(|_| EncodingError::InvalidEncoding)
    }
}
