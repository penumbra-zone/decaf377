use ark_ed_on_bls12_377::constraints::{EdwardsVar, FqVar};
use ark_r1cs_std::{eq::EqGadget, prelude::*};
use ark_relations::ns;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use crate::{Element, Fq};

/// Represents the R1CS equivalent of a `decaf377::Element`
pub struct Decaf377ElementVar {
    pub(crate) inner: EdwardsVar,
}

impl Decaf377ElementVar {
    /// Add an existing `Element`
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

impl EqGadget<Fq> for Decaf377ElementVar {
    fn is_eq(&self, other: &Self) -> Result<Boolean<Fq>, SynthesisError> {
        // Could use formulae Section 4.5 of Decaf paper which uses projective
        // - but here the inner point is affine since there is only an `AffineVar`
        // in ark-r1cs-std for twisted Edwards curves.
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
