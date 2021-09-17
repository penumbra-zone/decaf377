//! `decaf377` [instantiates Decaf over the BLS12-377 scalar
//! field](https://penumbra.zone/crypto/primitives/decaf377.html).

mod error;
mod group;
mod invsqrt;
mod sign;

pub use error::EncodingError;
pub use group::{Element, Encoding};

pub use ark_ed_on_bls12_377::Fr;
