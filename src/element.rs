use ark_ec::{AffineRepr, CurveGroup, Group};
use ark_ed_on_bls12_377::{EdwardsAffine, EdwardsConfig, EdwardsProjective};
use ark_serialize::Valid;

use crate::{Fq, Fr};

pub mod affine;
pub mod projective;

pub use affine::AffineElement;
pub use projective::Element;

impl Valid for Element {}

impl Group for Element {
    type ScalarField = Fr;

    fn double_in_place(&mut self) -> &mut Self {
        let inner = *self.inner.double_in_place();
        *self = Element { inner };
        self
    }

    fn generator() -> Self {
        crate::basepoint()
    }

    fn mul_bigint(&self, other: impl AsRef<[u64]>) -> Self {
        let inner = *self.inner.mul_bigint(other);
        Element { inner }
    }
}

impl CurveGroup for Element {
    // We implement `CurveGroup` as it is required by the `CurveVar`
    // trait used in the R1CS feature. The `ProjectiveCurve` trait requires
    // an affine representation of `Element` to be defined, and `AffineRepr`
    // to be implemented on that type.
    type Config = EdwardsConfig;

    type BaseField = Fq;

    type Affine = AffineElement;

    // This type is supposed to represent an element of the entire elliptic
    // curve group, not just the prime-order subgroup. Since this is decaf,
    // this is just an `Element` again.
    type FullGroup = Element;

    fn normalize_batch(v: &mut [Self]) {
        let mut v_inner = v.iter_mut().map(|g| g.inner).collect::<Vec<_>>();
        EdwardsProjective::normalize_batch(&mut v_inner[..]);
    }

    fn into_affine(self) -> Self::Affine {
        self.into()
    }
}

impl Valid for AffineElement {}

impl AffineRepr for AffineElement {
    type Config = EdwardsConfig;

    type ScalarField = Fr;

    type BaseField = Fq;

    //type Group = Element;

    fn xy(&self) -> (Self::BaseField, Self::BaseField) {
        self.inner.xy()
    }

    fn zero() -> Self {
        AffineElement {
            inner: EdwardsAffine::zero(),
        }
    }

    fn generator() -> Self {
        crate::basepoint().into()
    }

    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        EdwardsAffine::from_random_bytes(bytes).map(|inner| AffineElement { inner })
    }

    fn mul_bigint<S: Into<<Self::ScalarField as ark_ff::PrimeField>::BigInt>>(
        &self,
        other: S,
    ) -> Self::Group {
        Element {
            inner: self.inner.mul_bigint(other),
        }
    }

    fn clear_cofactor(&self) -> Self {
        // This is decaf so we're just returning the same point.
        self
    }

    fn mul_by_cofactor_to_group(&self) -> Self::Group {
        self.into()
    }
}

impl From<Element> for AffineElement {
    fn from(point: Element) -> Self {
        Self {
            inner: point.inner.into(),
        }
    }
}

impl From<AffineElement> for Element {
    fn from(point: AffineElement) -> Self {
        Self {
            inner: point.inner.into(),
        }
    }
}

impl From<&Element> for AffineElement {
    fn from(point: &Element) -> Self {
        Self {
            inner: point.inner.into(),
        }
    }
}

impl From<&AffineElement> for Element {
    fn from(point: &AffineElement) -> Self {
        Self {
            inner: point.inner.into(),
        }
    }
}
