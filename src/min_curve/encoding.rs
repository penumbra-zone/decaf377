use crate::EncodingError;
use core::convert::TryFrom;

#[derive(Copy, Clone, Default, Eq, Ord, PartialOrd, PartialEq, Debug)]
pub struct Encoding(pub [u8; 32]);

impl TryFrom<&[u8]> for Encoding {
    type Error = EncodingError;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        if bytes.len() == 32 {
            let mut arr = [0u8; 32];
            arr.copy_from_slice(&bytes[0..32]);
            Ok(Encoding(arr))
        } else {
            Err(EncodingError::InvalidSliceLength)
        }
    }
}

impl From<[u8; 32]> for Encoding {
    fn from(bytes: [u8; 32]) -> Encoding {
        Encoding(bytes)
    }
}

impl From<Encoding> for [u8; 32] {
    fn from(enc: Encoding) -> [u8; 32] {
        enc.0
    }
}
