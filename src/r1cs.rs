use std::ops::{Add, AddAssign, Sub, SubAssign};

use ark_ec::{twisted_edwards_extended::GroupProjective, TEModelParameters};
use ark_ed_on_bls12_377::{
    constraints::{EdwardsVar, FqVar},
    EdwardsParameters, EdwardsProjective,
};
use ark_r1cs_std::{
    alloc::AllocVar, eq::EqGadget, groups::curves::twisted_edwards::AffineVar, prelude::*, R1CSVar,
};
use ark_relations::ns;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use crate::{Element, Fq};

#[derive(Clone, Debug)]
/// Represents the R1CS equivalent of a `decaf377::Element`
pub struct Decaf377ElementVar {
    /// Inner type is an alias for `AffineVar<EdwardsParameters, FqVar>`
    pub(crate) inner: EdwardsVar,
}

impl Decaf377ElementVar {
    /// Add an existing `Element` to the constraint system.
    pub fn add_element(
        cs: ConstraintSystemRef<Fq>,
        decaf_element: Element,
        mode: AllocationMode,
    ) -> anyhow::Result<Self> {
        // Add affine coordinates to constraint system using the provided allocation mode
        let x = FqVar::new_variable(ns!(cs, "element_x"), || Ok(decaf_element.inner.x), mode)
            .map_err(|e| anyhow::anyhow!("couldn't add x to constraint system: {}", e))?;
        let y = FqVar::new_variable(ns!(cs, "element_y"), || Ok(decaf_element.inner.y), mode)
            .map_err(|e| anyhow::anyhow!("couldn't add y to constraint system: {}", e))?;
        let inner = EdwardsVar::new(x, y);
        Ok(Decaf377ElementVar { inner })
    }
}

impl Add for Decaf377ElementVar {
    type Output = Decaf377ElementVar;

    fn add(self, other: Decaf377ElementVar) -> Self::Output {
        Decaf377ElementVar {
            inner: self.inner.add(other.inner),
        }
    }
}

impl AddAssign for Decaf377ElementVar {
    fn add_assign(&mut self, rhs: Decaf377ElementVar) {
        self.inner.add_assign(rhs.inner)
    }
}

impl Sub for Decaf377ElementVar {
    type Output = Decaf377ElementVar;

    fn sub(self, other: Decaf377ElementVar) -> Self::Output {
        Decaf377ElementVar {
            inner: self.inner.sub(other.inner),
        }
    }
}

impl SubAssign for Decaf377ElementVar {
    fn sub_assign(&mut self, rhs: Decaf377ElementVar) {
        self.inner.sub_assign(rhs.inner)
    }
}

impl EqGadget<Fq> for Decaf377ElementVar {
    fn is_eq(&self, other: &Self) -> Result<Boolean<Fq>, SynthesisError> {
        // Could use formulae Section 4.5 of Decaf paper which uses projective
        // - but here the inner point is affine since there is only an `AffineVar`
        // (`EdwardsVar` is a type alias for `AffineVar`) in `ark-r1cs-std` for
        // twisted Edwards curves.
        let x_equal = self.inner.x.is_eq(&other.inner.x)?;
        let y_equal = self.inner.y.is_eq(&other.inner.y)?;
        x_equal.and(&y_equal)
    }

    fn conditional_enforce_equal(
        &self,
        other: &Self,
        condition: &Boolean<Fq>,
    ) -> Result<(), SynthesisError> {
        self.inner
            .x
            .conditional_enforce_equal(&other.inner.x, condition)?;
        self.inner
            .y
            .conditional_enforce_equal(&other.inner.y, condition)?;
        Ok(())
    }

    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        condition: &Boolean<Fq>,
    ) -> Result<(), SynthesisError> {
        self.is_eq(other)?
            .and(condition)?
            .enforce_equal(&Boolean::Constant(false))
    }
}

impl R1CSVar<Fq> for Decaf377ElementVar {
    type Value = EdwardsProjective;

    fn cs(&self) -> ConstraintSystemRef<Fq> {
        self.inner.cs()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        self.inner.value()
    }
}

impl CondSelectGadget<Fq> for Decaf377ElementVar {
    fn conditionally_select(
        cond: &Boolean<Fq>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let x = cond.select(&true_value.inner.x, &false_value.inner.x)?;
        let y = cond.select(&true_value.inner.y, &false_value.inner.y)?;

        Ok(Decaf377ElementVar {
            inner: EdwardsVar::new(x, y),
        })
    }
}

// This lets us use `new_constant`, `new_input` (public), or `new_witness` to add
// decaf elements to an R1CS constraint system.
impl AllocVar<EdwardsProjective, Fq> for Decaf377ElementVar {
    fn new_variable<T: std::borrow::Borrow<EdwardsProjective>>(
        cs: impl Into<ark_relations::r1cs::Namespace<Fq>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        // Since the closure here can only do operations that are allowed on the `Decaf377ElementVar`,
        // as the inner `EdwardsVar` is not exposed in the API, we do not need to check again
        // that the resulting point is valid.
        //
        // Compare this with the implementation of this trait for `EdwardsVar`, where they check that the
        // point is in the right subgroup prior to witnessing.
        Ok(Decaf377ElementVar {
            inner: AffineVar::<EdwardsParameters, FqVar>::new_variable(cs, f, mode)?,
        })
    }
}
