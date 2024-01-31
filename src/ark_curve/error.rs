use ark_std::error::Error;

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

impl Error for EncodingError {}
