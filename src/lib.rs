//! `decaf377` [instantiates Decaf over the BLS12-377 scalar
//! field](https://penumbra.zone/crypto/primitives/decaf377.html).

mod sign;
mod invsqrt;
mod error;
mod group;

pub use group::{Element, Encoding};
pub use error::EncodingError;

pub use ark_ed_on_bls12_377::Fr;