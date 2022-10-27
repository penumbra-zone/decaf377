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
        todo!()
    }

    fn is_neq(&self, other: &Self) -> Result<Boolean<Fq>, SynthesisError> {
        todo!()
    }

    fn conditional_enforce_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<Fq>,
    ) -> Result<(), SynthesisError> {
        todo!()
    }

    fn enforce_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        todo!()
    }

    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<Fq>,
    ) -> Result<(), SynthesisError> {
        todo!()
    }

    fn enforce_not_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        todo!()
    }
}
