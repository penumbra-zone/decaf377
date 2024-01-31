#![no_std]
//! `decaf377` [instantiates Decaf over the BLS12-377 scalar
//! field](https://penumbra.zone/crypto/primitives/decaf377.html).
//!
use cfg_if::cfg_if;

pub mod ark_curve;
pub mod fields;
pub mod min_curve;
pub use fields::{fp::Fp, fq::Fq, fr::Fr};

mod sign;

cfg_if! {
    if #[cfg(feature = "arkworks")] {

        pub use ark_curve::Element;
        pub use ark_curve::Encoding;

        // r1cs feature?
        //pub mod bls12_377;
        //pub use bls12_377::Bls12_377;

        pub use ark_curve::basepoint;
    } else {
        pub use min_curve::Element;
        pub use min_curve::Encoding;
    }
}
