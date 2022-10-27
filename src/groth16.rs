use ark_ed_on_bls12_377::constraints::{EdwardsVar, FqVar};
use ark_r1cs_std::prelude::*;
use ark_relations::ns;
use ark_relations::r1cs::ConstraintSystemRef;

use anyhow::Result;

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
    ) -> Result<Self> {
        // Add affine coordinates to constraint system using the provided allocation mode
        let x = FqVar::new_variable(ns!(cs, "element_x"), || Ok(decaf_element.inner.x), mode)
            .map_err(|e| anyhow::anyhow!("couldn't add x to constraint system: {}", e))?;
        let y = FqVar::new_variable(ns!(cs, "element_y"), || Ok(decaf_element.inner.y), mode)
            .map_err(|e| anyhow::anyhow!("couldn't add y to constraint system: {}", e))?;
        let inner = EdwardsVar::new(x, y);
        Ok(Decaf377ElementVar { inner })
    }
}
