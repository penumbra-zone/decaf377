pub mod bls12_377;
mod constants;
mod edwards;

mod element;
mod elligator;
mod encoding;
mod invsqrt;
mod ops;
pub mod rand;
pub mod serialize;

pub use constants::ZETA;
pub(crate) use edwards::{Decaf377EdwardsConfig, EdwardsProjective};
pub use element::{AffineElement, Element};
pub use encoding::Encoding;

mod on_curve;

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
