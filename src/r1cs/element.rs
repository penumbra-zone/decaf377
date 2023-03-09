#![allow(non_snake_case)]
use std::borrow::Borrow;

use ark_ec::AffineCurve;
use ark_ed_on_bls12_377::{
    constraints::{EdwardsVar, FqVar},
    EdwardsAffine,
};
use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, prelude::*, R1CSVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use crate::r1cs::inner::ElementVar as InnerElementVar;
use crate::r1cs::lazy::LazyElementVar;
use crate::{AffineElement, Element, Fq};

#[derive(Clone, Debug)]
/// Represents the R1CS equivalent of a `decaf377::Element`
///
/// Generally the suffix -`Var` will indicate that the type or variable
/// represents in R1CS.
pub struct ElementVar {
    pub(crate) inner: LazyElementVar,
}

impl ElementVar {
    /// R1CS equivalent of `Element::vartime_compress_to_field`
    pub fn compress_to_field(&self) -> Result<FqVar, SynthesisError> {
        self.inner.encoding()
    }

    /// R1CS equivalent of `Encoding::vartime_decompress`
    pub fn decompress_from_field(s_var: FqVar) -> Result<ElementVar, SynthesisError> {
        let inner = LazyElementVar::new_from_encoding(s_var);
        // This enforces that the encoding is valid.
        inner.element()?;
        Ok(Self { inner })
    }

    /// R1CS equivalent of `Element::elligator_map`
    pub(crate) fn elligator_map(r_0_var: &FqVar) -> Result<ElementVar, SynthesisError> {
        let inner = InnerElementVar::elligator_map(r_0_var)?;
        Ok(Self {
            inner: LazyElementVar::new_from_element(inner),
        })
    }

    /// Maps a field element to a decaf377 `ElementVar` suitable for CDH challenges.
    pub fn encode_to_curve(r_var: &FqVar) -> Result<ElementVar, SynthesisError> {
        Self::elligator_map(r_var)
    }
}

impl EqGadget<Fq> for ElementVar {
    fn is_eq(&self, other: &Self) -> Result<Boolean<Fq>, SynthesisError> {
        self.inner.element()?.is_eq(&other.inner.element()?)
    }

    fn conditional_enforce_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<Fq>,
    ) -> Result<(), SynthesisError> {
        // should_enforce = true
        //      return self == other
        // should_enforce = false
        //      return true
        self.is_eq(other)?
            .conditional_enforce_equal(&Boolean::constant(true), should_enforce)
    }

    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<Fq>,
    ) -> Result<(), SynthesisError> {
        self.is_eq(other)?
            .conditional_enforce_equal(&Boolean::constant(false), should_enforce)
    }
}

impl R1CSVar<Fq> for ElementVar {
    type Value = Element;

    fn cs(&self) -> ConstraintSystemRef<Fq> {
        let inner = self
            .inner
            .element()
            .expect("element will exist if ElementVar is allocated");
        inner.cs()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        let inner_element = self.inner.element()?;
        let (x, y) = (
            inner_element.inner.x.value()?,
            inner_element.inner.y.value()?,
        );
        let result = EdwardsAffine::new(x, y);

        Ok(Element {
            inner: result.into(),
        })
    }
}

impl CondSelectGadget<Fq> for ElementVar {
    fn conditionally_select(
        cond: &Boolean<Fq>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let true_element = true_value.inner.element()?;
        let false_element = false_value.inner.element()?;
        let x = cond.select(&true_element.inner.x, &false_element.inner.x)?;
        let y = cond.select(&true_element.inner.y, &false_element.inner.y)?;

        let new_element = InnerElementVar {
            inner: EdwardsVar::new(x, y),
        };
        Ok(Self {
            inner: LazyElementVar::new_from_element(new_element),
        })
    }
}

// This lets us use `new_constant`, `new_input` (public), or `new_witness` to add
// decaf elements to an R1CS constraint system.
impl AllocVar<Element, Fq> for ElementVar {
    fn new_variable<T: std::borrow::Borrow<Element>>(
        cs: impl Into<ark_relations::r1cs::Namespace<Fq>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        match mode {
            AllocationMode::Input => {
                let value: Element = *f()?.borrow();
                dbg!(value.inner);
                let compressed = value.vartime_compress_to_field();
                Ok(Self::new_input(cs, || Ok(compressed))?)
            }
            _ => {
                let inner = InnerElementVar::new_variable(cs, f, mode)?;
                Ok(Self {
                    inner: LazyElementVar::new_from_element(inner),
                })
            }
        }
    }
}

impl AllocVar<AffineElement, Fq> for ElementVar {
    fn new_variable<T: Borrow<AffineElement>>(
        cs: impl Into<ark_relations::r1cs::Namespace<Fq>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        Self::new_variable(cs, || f().map(|b| b.borrow().into_projective()), mode)
    }
}

impl AllocVar<Fq, Fq> for ElementVar {
    fn new_variable<T: Borrow<Fq>>(
        cs: impl Into<ark_relations::r1cs::Namespace<Fq>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let compressed = FqVar::new_variable(cs, f, mode)?;
        dbg!(compressed.value());
        let element = Self {
            inner: LazyElementVar::new_from_encoding(compressed),
        };
        dbg!(element.value());
        Ok(element)
    }
}

impl ToBitsGadget<Fq> for ElementVar {
    fn to_bits_le(&self) -> Result<Vec<Boolean<Fq>>, SynthesisError> {
        let compressed_fq = self
            .inner
            .element()
            .expect("element will exist")
            .to_bits_le()?;
        let encoded_bits = compressed_fq.to_bits_le()?;
        Ok(encoded_bits)
    }
}

impl ToBytesGadget<Fq> for ElementVar {
    fn to_bytes(&self) -> Result<Vec<UInt8<Fq>>, SynthesisError> {
        let compressed_fq = self
            .inner
            .element()
            .expect("element will exist")
            .to_bytes()?;
        let encoded_bytes = compressed_fq.to_bytes()?;
        Ok(encoded_bytes)
    }
}

impl<'a> GroupOpsBounds<'a, Element, ElementVar> for ElementVar {}

impl CurveVar<Element, Fq> for ElementVar {
    fn zero() -> Self {
        let new_element = InnerElementVar::zero();
        Self {
            inner: LazyElementVar::new_from_element(new_element),
        }
    }

    fn constant(other: Element) -> Self {
        let new_element = InnerElementVar::constant(other);
        Self {
            inner: LazyElementVar::new_from_element(new_element),
        }
    }

    fn new_variable_omit_prime_order_check(
        cs: impl Into<ark_relations::r1cs::Namespace<Fq>>,
        f: impl FnOnce() -> Result<Element, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();

        match f() {
            Ok(ge) => {
                let new_element =
                    InnerElementVar::new_variable_omit_prime_order_check(cs, || Ok(ge), mode)?;
                Ok(Self {
                    inner: LazyElementVar::new_from_element(new_element),
                })
            }
            _ => Err(SynthesisError::AssignmentMissing),
        }
    }

    fn enforce_prime_order(&self) -> Result<(), SynthesisError> {
        // This is decaf
        Ok(())
    }

    fn double_in_place(&mut self) -> Result<(), SynthesisError> {
        let mut inner_element = self.inner.element().expect("element will exist");
        inner_element.double_in_place()?;
        *self = Self {
            inner: LazyElementVar::new_from_element(inner_element),
        };
        Ok(())
    }

    fn negate(&self) -> Result<Self, SynthesisError> {
        let negated = self.inner.element().expect("element will exist").negate()?;
        Ok(Self {
            inner: LazyElementVar::new_from_element(negated),
        })
    }
}
