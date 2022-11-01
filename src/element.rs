use std::borrow::Borrow;

use ark_ec::{
    twisted_edwards_extended::{GroupAffine, GroupProjective},
    AffineCurve, ProjectiveCurve,
};
use ark_ed_on_bls12_377::{EdwardsParameters, EdwardsProjective};
use ark_ff::Zero;
use ark_std::fmt::{Display, Formatter, Result as FmtResult};

use zeroize::Zeroize;

use crate::{Fq, Fr};

#[derive(Copy, Clone, Hash)]
pub struct Element {
    pub(crate) inner: EdwardsProjective,
}

impl std::fmt::Debug for Element {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // This prints the hex of the encoding of self, rather than the
        // coordinates, because that's what's most useful to downstream
        // consumers of the library.
        f.write_fmt(format_args!(
            "decaf377::Element({})",
            hex::encode(&self.vartime_compress().0[..])
        ))
    }
}

impl Display for Element {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "decaf377::Element({})",
            hex::encode(&self.vartime_compress().0[..])
        )
    }
}

impl Default for Element {
    fn default() -> Self {
        Element {
            inner: EdwardsProjective::zero(),
        }
    }
}

impl PartialEq for Element {
    fn eq(&self, other: &Element) -> bool {
        // Section 4.5 of Decaf paper
        self.inner.x * other.inner.y == self.inner.y * other.inner.x
    }
}

impl Eq for Element {}

impl Zeroize for Element {
    fn zeroize(&mut self) {
        self.inner.zeroize()
    }
}

impl Element {
    /// Convenience method to make identity checks more readable.
    pub fn is_identity(&self) -> bool {
        // Section 4.5 of Decaf paper states for cofactor 4 curves we can
        // just check X = 0 to check equality with identity
        self.inner.x == Fq::zero()
    }

    /// Given an iterator of public scalars and an iterator of public points,
    /// compute
    /// $$
    /// Q = \[c\_1\] P\_1 + \cdots + \[c\_n\] P\_n,
    /// $$
    /// using variable-time operations.
    ///
    /// It is an error to call this function with two iterators of different
    /// lengths -- it would require `ExactSizeIterator`, but
    /// `ExactSizeIterator`s are not closed under chaining, and disallowing
    /// iterator chaining would destroy the utility of the function.
    pub fn vartime_multiscalar_mul<I, J>(scalars: I, points: J) -> Element
    where
        I: IntoIterator,
        I::Item: Borrow<Fr>,
        J: IntoIterator,
        J::Item: Borrow<Element>,
    {
        // XXX this is a stub implementation, try to use a real MSM later
        let scalars = scalars.into_iter();
        let points = points.into_iter();

        // XXX panic on length mismatches ? or error?

        scalars
            .zip(points)
            .fold(Element::default(), |acc, (scalar, point)| {
                acc + (scalar.borrow() * point.borrow())
            })
    }
}

impl Zero for Element {
    fn zero() -> Self {
        Self::default()
    }

    fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }
}

impl core::iter::Sum<Self> for Element {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

impl<'a> core::iter::Sum<&'a Element> for Element {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

impl ProjectiveCurve for Element {
    const COFACTOR: &'static [u64] = EdwardsProjective::COFACTOR;

    type ScalarField = Fr;

    type BaseField = Fq;

    //type Affine = GroupAffine<EdwardsParameters>;
    // TODO: Make affine variant of Element with Into impls?
    type Affine = Element;

    fn prime_subgroup_generator() -> Self {
        todo!()
    }

    fn batch_normalization(v: &mut [Self]) {
        todo!()
    }

    fn is_normalized(&self) -> bool {
        todo!()
    }

    fn double_in_place(&mut self) -> &mut Self {
        todo!()
    }

    fn add_assign_mixed(&mut self, other: &Self::Affine) {
        todo!()
    }
}
