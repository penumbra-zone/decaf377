//! `decaf377` [instantiates Decaf over the BLS12-377 scalar
//! field](https://penumbra.zone/crypto/primitives/decaf377.html).

mod constants;
mod element;
mod elligator;
mod encoding;
mod error;
mod field_ext;
mod invsqrt;
mod on_curve;
mod ops;
mod sign;

pub use constants::ZETA;
pub use element::Element;
pub use encoding::Encoding;
pub use error::EncodingError;
pub use field_ext::FieldExt;

pub use ark_bls12_377::Bls12_377;
pub use ark_ed_on_bls12_377::{Fq, Fr};

pub use invsqrt::SqrtRatioZeta;
use on_curve::OnCurve;
use sign::Sign;

/// Return the conventional generator for `decaf377`.
pub fn basepoint() -> Element {
    let mut bytes = [0u8; 32];
    bytes[0] = 8;

    Encoding(bytes)
        .decompress()
        .expect("hardcoded basepoint bytes are valid")
}
