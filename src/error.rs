#[derive(Debug)]
pub enum EncodingError {
    InvalidEncoding,
    InvalidSliceLength,
}

impl core::fmt::Display for EncodingError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let msg = match self {
            Self::InvalidEncoding => "Invalid Decaf377 encoding",
            Self::InvalidSliceLength => "Invalid length bytes in encoded point",
        };

        msg.fmt(f)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for EncodingError {}
