#![no_std]
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
pub mod rand;
pub mod serialize;
mod sign;

pub use constants::ZETA;
pub use element::{AffineElement, Element};
pub(crate) use element::{Decaf377EdwardsConfig, EdwardsProjective};
pub use encoding::Encoding;
pub use error::EncodingError;
pub use field_ext::FieldExt;

#[cfg(feature = "r1cs")]
pub mod r1cs;

pub use ark_bls12_377::Bls12_377;
pub use ark_ed_on_bls12_377::{Fq, Fr};

pub use invsqrt::SqrtRatioZeta;
use on_curve::OnCurve;
use sign::Sign;

/// Return the conventional generator for `decaf377`.
pub fn basepoint() -> Element {
    Element {
        inner: EdwardsProjective::new(
            *constants::B_X,
            *constants::B_Y,
            *constants::B_T,
            *constants::B_Z,
        ),
    }
}
