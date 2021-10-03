use thiserror::Error;

#[derive(Error, Debug)]
pub enum EncodingError {
    #[error("Invalid Decaf377 encoding")]
    InvalidEncoding,
    #[error("Invalid length bytes in encoded point")]
    InvalidSliceLength,
}
