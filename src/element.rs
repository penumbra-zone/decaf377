use ark_ec::{
    twisted_edwards::{Affine, MontCurveConfig, Projective, TECurveConfig},
    AffineRepr, CurveConfig, CurveGroup, Group, ScalarMul, VariableBaseMSM,
};
use ark_serialize::Valid;
use ark_std::vec::Vec;

use crate::{
    constants::{GENERATOR_X, GENERATOR_Y},
    Fq, Fr,
};

pub mod affine;
pub mod projective;

pub use affine::AffineElement;
pub use projective::Element;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Decaf377EdwardsConfig;

// These types should not be exported. They are similar to `EdwardsAffine` and
// `EdwardsProjective` from the `ark_ed_on_bls12_377` crate, except using our own
// `Decaf377Config` that has the cofactor set to 1. Consumers of this
// library should use the `AffineElement` and `Element` (projective)
// types.
pub(crate) type EdwardsAffine = Affine<Decaf377EdwardsConfig>;
pub(crate) type EdwardsProjective = Projective<Decaf377EdwardsConfig>;

impl CurveConfig for Decaf377EdwardsConfig {
    type BaseField = Fq;
    type ScalarField = Fr;

    const COFACTOR: &'static [u64] = &[1];

    const COFACTOR_INV: Fr = Fr::one();
}

impl TECurveConfig for Decaf377EdwardsConfig {
    /// COEFF_A = -1
    const COEFF_A: Fq = Fq::from_montgomery_limbs_64([
        10157024534604021774,
        16668528035959406606,
        5322190058819395602,
        387181115924875961,
    ]);

    /// COEFF_D = 3021
    const COEFF_D: Fq = Fq::from_montgomery_limbs_64([
        15008245758212136496,
        17341409599856531410,
        648869460136961410,
        719771289660577536,
    ]);

    const GENERATOR: EdwardsAffine = EdwardsAffine::new_unchecked(GENERATOR_X, GENERATOR_Y);

    type MontCurveConfig = Decaf377EdwardsConfig;

    /// Multiplication by `a` is just negation.
    #[inline(always)]
    fn mul_by_a(elem: Self::BaseField) -> Self::BaseField {
        -elem
    }

    fn is_in_correct_subgroup_assuming_on_curve(_: &Affine<Self>) -> bool {
        true
    }
}

impl MontCurveConfig for Decaf377EdwardsConfig {
    const COEFF_A: Fq = Fq::from_montgomery_limbs_64([
        13800168384327121454,
        6841573379969807446,
        12529593083398462246,
        853978956621483129,
    ]);

    const COEFF_B: Fq = Fq::from_montgomery_limbs_64([
        7239382437352637935,
        14509846070439283655,
        5083066350480839936,
        1265663645916442191,
    ]);

    type TECurveConfig = Decaf377EdwardsConfig;
}

impl Valid for Element {
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        Ok(())
    }
}

impl ScalarMul for Element {
    type MulBase = AffineElement;

    const NEGATION_IS_CHEAP: bool = true;

    fn batch_convert_to_mul_base(bases: &[Self]) -> Vec<Self::MulBase> {
        let bases_inner = bases.iter().map(|g| g.inner).collect::<Vec<_>>();
        let result = EdwardsProjective::batch_convert_to_mul_base(&bases_inner[..]);
        result
            .into_iter()
            .map(|g| AffineElement { inner: g })
            .collect::<Vec<_>>()
    }
}

impl VariableBaseMSM for Element {}

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
        let inner = self.inner.mul_bigint(other);
        Element { inner }
    }
}

impl CurveGroup for Element {
    // We implement `CurveGroup` as it is required by the `CurveVar`
    // trait used in the R1CS feature. The `ProjectiveCurve` trait requires
    // an affine representation of `Element` to be defined, and `AffineRepr`
    // to be implemented on that type.
    type Config = Decaf377EdwardsConfig;

    type BaseField = Fq;

    type Affine = AffineElement;

    // This type is supposed to represent an element of the entire elliptic
    // curve group, not just the prime-order subgroup. Since this is decaf,
    // this is just an `Element` again.
    type FullGroup = AffineElement;

    fn normalize_batch(v: &[Self]) -> Vec<AffineElement> {
        let v_inner = v.iter().map(|g| g.inner).collect::<Vec<_>>();
        let result = EdwardsProjective::normalize_batch(&v_inner[..]);
        result
            .into_iter()
            .map(|g| AffineElement { inner: g })
            .collect::<Vec<_>>()
    }

    fn into_affine(self) -> Self::Affine {
        self.into()
    }
}

impl Valid for AffineElement {
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        Ok(())
    }
}

impl AffineRepr for AffineElement {
    type Config = Decaf377EdwardsConfig;

    type ScalarField = Fr;

    type BaseField = Fq;

    type Group = Element;

    fn xy(&self) -> Option<(&Self::BaseField, &Self::BaseField)> {
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

    fn mul_bigint(&self, other: impl AsRef<[u64]>) -> Self::Group {
        Element {
            inner: self.inner.mul_bigint(other),
        }
    }

    fn clear_cofactor(&self) -> Self {
        // This is decaf so we're just returning the same point.
        *self
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
