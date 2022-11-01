#![allow(non_snake_case)]
use ark_ec::TEModelParameters;
use ark_ed_on_bls12_377::{
    constraints::{EdwardsVar, FqVar},
    EdwardsAffine, EdwardsParameters, EdwardsProjective,
};
use ark_r1cs_std::{
    alloc::AllocVar, eq::EqGadget, groups::curves::twisted_edwards::AffineVar, prelude::*, R1CSVar,
};
use ark_relations::ns;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use crate::{r1cs::fqvar_ext::FqVarExtension, Element, Fq};

#[derive(Clone, Debug)]
/// Represents the R1CS equivalent of a `decaf377::Element`
pub struct Decaf377ElementVar {
    /// Inner type is an alias for `AffineVar<EdwardsParameters, FqVar>`
    pub(crate) inner: EdwardsVar,
}

impl Decaf377ElementVar {
    /// Add an existing `Element` to the constraint system.
    /// Remove this method. If you want to construct Decaf377ElementVar, you first
    /// decode to bytes/field element.
    /// Replace this with decode
    /// Prover:
    /// * Witnesses the field element.
    /// * Add constraints / relations to show I know two other field elements x, y
    /// such that they are valid decodings of the field element that is witnessed.
    pub fn add_element(
        cs: ConstraintSystemRef<Fq>,
        decaf_element: Element,
        mode: AllocationMode,
    ) -> anyhow::Result<Self> {
        // Add affine coordinates to constraint system using the provided allocation mode
        // TODO: Decode
        // TODO: Encode
        // Problem: Expensive.
        let x = FqVar::new_variable(ns!(cs, "element_x"), || Ok(decaf_element.inner.x), mode)
            .map_err(|e| anyhow::anyhow!("couldn't add x to constraint system: {}", e))?;
        let y = FqVar::new_variable(ns!(cs, "element_y"), || Ok(decaf_element.inner.y), mode)
            .map_err(|e| anyhow::anyhow!("couldn't add y to constraint system: {}", e))?;
        let inner = EdwardsVar::new(x, y);
        Ok(Decaf377ElementVar { inner })
    }

    /// R1CS equivalent of `Element::vartime_compress_to_field`
    pub(crate) fn compress_to_field(&self) -> Result<FqVar, SynthesisError> {
        // We have affine x, y but our compression formulae are in projective.
        let affine_x = &self.inner.x;
        let affine_y = &self.inner.y;

        let X = affine_x;
        // We treat Z at a constant.
        let Z = FqVar::constant(Fq::one());
        let T = affine_x * affine_y;

        let A_MINUS_D = FqVar::constant(EdwardsParameters::COEFF_A - EdwardsParameters::COEFF_D);

        // 1.
        let u_1 = (X + T.clone()) * (X - T.clone());

        // 2.
        let den = u_1.clone() * A_MINUS_D.clone() * X.square()?;
        let one_over_den = den.inverse()?;
        // TODO. Use EqGadget to constrain v * v = one_over_den
        let v: FqVar = one_over_den.isqrt();

        // 3.
        let u_2: FqVar = (v.clone() * u_1).abs();

        // 4.
        let u_3 = u_2 * Z - T;

        // 5.
        let s = (A_MINUS_D * v * u_3 * X).abs();

        Ok(s)
    }
}

impl EqGadget<Fq> for Decaf377ElementVar {
    fn is_eq(&self, other: &Self) -> Result<Boolean<Fq>, SynthesisError> {
        // Section 4.5 of Decaf paper: X_1 * Y_2 = X_2 * Y_1
        // Note that x, y are affine here but projective X = x, Y = y
        let X_1 = &self.inner.x;
        let Y_1 = &self.inner.y;
        let X_2 = &other.inner.x;
        let Y_2 = &other.inner.y;
        let lhs = X_1 * Y_2;
        let rhs = X_2 * Y_1;
        lhs.is_eq(&rhs)
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
    // TODO: Shouldn't this be Element?
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

        // Way that is secure: Encode (out of circuit) to an Fq
        // Witness the encoded value
        // and then decode (in circuit)
        // The resulting variables is what we construct Decaf377ElementVar from

        // Q. What is cheaper? Need to work out formulae to prove this point is in the
        // image of the encoding map. This is stronger than what we need.
        // Can do by checking if the point is even (see section 1.2 Decaf paper)

        // P = output of f
        // Outside circuit, compute Q = 1/2 * P
        // Inside the circuit, witness Q. Add equality constraint that Q + Q = P

        // Future: Only do for witnessing?

        // The below value should be constructed from the decode method.
        // i.e. do NOT pass f into the AffineValue::new_variable()
        Ok(Decaf377ElementVar {
            inner: AffineVar::<EdwardsParameters, FqVar>::new_variable(cs, f, mode)?,
        })
        // Where is prime subgroup check done?
    }
}

impl AllocVar<EdwardsAffine, Fq> for Decaf377ElementVar {
    fn new_variable<T: std::borrow::Borrow<EdwardsAffine>>(
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

impl ToBitsGadget<Fq> for Decaf377ElementVar {
    fn to_bits_le(&self) -> Result<Vec<Boolean<Fq>>, SynthesisError> {
        let compressed_fq = self.compress_to_field()?;
        let encoded_bits = compressed_fq.to_bits_le()?;
        Ok(encoded_bits)
    }
}

impl ToBytesGadget<Fq> for Decaf377ElementVar {
    fn to_bytes(&self) -> Result<Vec<UInt8<Fq>>, SynthesisError> {
        let compressed_fq = self.compress_to_field()?;
        let encoded_bytes = compressed_fq.to_bytes()?;
        Ok(encoded_bytes)
    }
}

// Problem: This requires a bunch of arithmetic ops between Decaf377ElementVar and
// EdwardsProjective to be implemented, but we can't do that infallibly since
// EdwardsProjective may or may not be a valid decaf point.
//
// Solution (TODO): Implement all required traits on Element that we need from
// EdwardsProjective from ark-ec.
impl<'a> GroupOpsBounds<'a, Element, Decaf377ElementVar> for Decaf377ElementVar {}

impl CurveVar<Element, Fq> for Decaf377ElementVar {
    fn zero() -> Self {
        todo!()
    }

    fn constant(other: EdwardsProjective) -> Self {
        todo!()
    }

    fn new_variable_omit_prime_order_check(
        cs: impl Into<ark_relations::r1cs::Namespace<Fq>>,
        f: impl FnOnce() -> Result<Element, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        // Similar logic as AllocVar
        todo!()
    }

    fn enforce_prime_order(&self) -> Result<(), SynthesisError> {
        // This is decaf
        Ok(())
    }

    fn double_in_place(&mut self) -> Result<(), SynthesisError> {
        todo!()
    }

    fn negate(&self) -> Result<Self, SynthesisError> {
        todo!()
    }
}
