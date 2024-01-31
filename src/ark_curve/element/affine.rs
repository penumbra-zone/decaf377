use core::hash::Hash;

use crate::ark_curve::element::EdwardsAffine;
use ark_std::fmt::{Display, Formatter, Result as FmtResult};
use ark_std::Zero;

use zeroize::Zeroize;

use crate::Element;

#[derive(Copy, Clone)]
pub struct AffinePoint {
    pub(crate) inner: EdwardsAffine,
}

impl Hash for AffinePoint {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.inner.hash(state);
    }
}

impl Default for AffinePoint {
    fn default() -> Self {
        Element::default().into()
    }
}

impl core::iter::Sum<AffinePoint> for Element {
    fn sum<I: Iterator<Item = AffinePoint>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

impl<'a> core::iter::Sum<&'a AffinePoint> for Element {
    fn sum<I: Iterator<Item = &'a AffinePoint>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

impl PartialEq for AffinePoint {
    fn eq(&self, other: &AffinePoint) -> bool {
        // Section 4.5 of Decaf paper
        self.inner.x * other.inner.y == self.inner.y * other.inner.x
    }
}

impl Eq for AffinePoint {}

impl core::fmt::Debug for AffinePoint {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let element: Element = self.into();
        f.write_fmt(format_args!(
            "decaf377::AffinePoint({})",
            hex::encode(&element.vartime_compress().0[..])
        ))
    }
}

impl Display for AffinePoint {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let element: Element = self.into();
        write!(
            f,
            "decaf377::AffinePoint({})",
            hex::encode(&element.vartime_compress().0[..])
        )
    }
}

impl Zeroize for AffinePoint {
    fn zeroize(&mut self) {
        self.inner.zeroize()
    }
}
