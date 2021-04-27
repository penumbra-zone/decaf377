use thiserror::Error;

#[derive(Error, Debug)]
pub enum EncodingError {
    #[error("Invalid Decaf377 encoding")]
    InvalidEncoding,
}