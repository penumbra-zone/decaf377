use ark_ed_on_bls12_377::Fq;
use ark_ff::{Field, SquareRootField, Zero};

pub trait InvSqrt: Sized {
    /// Given `self`, return `Some(1/sqrt(self))` if `self` is nonzero and
    /// square, `Some(0)` if `self` is `0`, or `None` if `self` is nonsquare.
    fn invsqrt(&self) -> Option<Self>;
}

impl InvSqrt for Fq {
    fn invsqrt(&self) -> Option<Self> {
        // ideally this would be a single operation
        self.inverse().unwrap_or_else(Zero::zero).sqrt()
    }
}
