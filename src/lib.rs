//! `decaf377` [instantiates Decaf over the BLS12-377 scalar
//! field](https://penumbra.zone/crypto/primitives/decaf377.html).

mod constants;
mod element;
mod elligator;
mod encoding;
mod error;
mod invsqrt;
mod on_curve;
mod ops;
mod sign;

pub use element::Element;
pub use encoding::Encoding;
pub use error::EncodingError;

pub use ark_ed_on_bls12_377::{Fq, Fr};

use invsqrt::SqrtRatioZeta;
use on_curve::OnCurve;
use sign::Sign;
