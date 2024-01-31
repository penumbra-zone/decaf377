#![no_std]
//! `decaf377` [instantiates Decaf over the BLS12-377 scalar
//! field](https://penumbra.zone/crypto/primitives/decaf377.html).
//!
use cfg_if::cfg_if;

pub mod fields;
pub use fields::{fp::Fp, fq::Fq, fr::Fr};
mod field_ext;
pub use field_ext::FieldExt;
mod sign;

mod error;
pub use error::EncodingError;

cfg_if! {
    if #[cfg(feature = "arkworks")] {
        mod ark_curve;

        pub use ark_curve::Element;
        pub use ark_curve::Encoding;

        pub use ark_curve::basepoint;

        pub use ark_curve::bls12_377::Bls12_377;

        #[cfg(feature = "r1cs")]
        pub use ark_curve::r1cs;
    } else {
        mod min_curve;

        pub use min_curve::Element;
        pub use min_curve::Encoding;
    }
}
