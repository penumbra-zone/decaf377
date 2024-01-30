#![no_std]
//! `decaf377` [instantiates Decaf over the BLS12-377 scalar
//! field](https://penumbra.zone/crypto/primitives/decaf377.html).
//!
use cfg_if::cfg_if;

pub mod fields;
pub mod smol_curve;
pub use fields::{fp::Fp, fq::Fq, fr::Fr};

mod sign;

mod on_curve;
use on_curve::OnCurve;

cfg_if! {
    if #[cfg(feature = "arkworks")] {
        pub mod bls12_377;
        mod constants;
        mod element;
        mod elligator;
        mod encoding;
        mod error;
        mod field_ext;
        mod invsqrt;
        mod ops;
        pub mod rand;
        pub mod serialize;

        pub use constants::ZETA;
        pub use element::{AffineElement, Element};
        pub(crate) use element::{Decaf377EdwardsConfig, EdwardsProjective};
        pub use encoding::Encoding;
        pub use error::EncodingError;
        pub use field_ext::FieldExt;

        #[cfg(feature = "r1cs")]
        pub mod r1cs;

        pub use bls12_377::Bls12_377;


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
    } else {
    }
}
