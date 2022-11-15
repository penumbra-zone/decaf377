#![allow(non_snake_case)]
use std::borrow::Borrow;

use ark_ec::{AffineCurve, TEModelParameters};
use ark_ed_on_bls12_377::{
    constraints::{EdwardsVar, FqVar},
    EdwardsAffine, EdwardsParameters,
};
use ark_ff::Field;
use ark_r1cs_std::{
    alloc::AllocVar, eq::EqGadget, groups::curves::twisted_edwards::AffineVar, prelude::*, R1CSVar,
};
use ark_relations::ns;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError, ToConstraintField};
use ark_std::One;

use crate::{
    constants::{ONE, TWO, ZETA},
    r1cs::fqvar_ext::FqVarExtension,
    sign::Sign,
    AffineElement, Element, Fq,
};

#[derive(Clone, Debug)]
/// Represents the R1CS equivalent of a `decaf377::Element`
///
/// Generally the suffix -`Var` will indicate that the type or variable
/// represents in R1CS.
pub struct ElementVar {
    /// Inner type is an alias for `AffineVar<EdwardsParameters, FqVar>`
    pub(crate) inner: EdwardsVar,
}

impl ElementVar {
    /// R1CS equivalent of `Element::vartime_compress_to_field`
    ///
    /// Requires the `Element` of the `ElementVar` to be passed to it.
    /// This is because during the setup phase, we cannot access assignments
    /// through `T::value()`.
    pub fn compress_to_field(&self, native: Element) -> Result<FqVar, SynthesisError> {
        // We have affine x, y but our compression formulae are in projective.
        let affine_x_var = &self.inner.x;
        let affine_y_var = &self.inner.y;
        let affine: AffineElement = native.into();

        let X_var = affine_x_var;
        // We treat Z at a constant.
        let Y_var = affine_y_var;
        let Z_var = FqVar::one();
        let T_var = X_var * Y_var;

        let X = affine.inner.x;
        let Y = affine.inner.y;
        let Z = Fq::one();
        let T = X * Y;

        let A_MINUS_D = EdwardsParameters::COEFF_A - EdwardsParameters::COEFF_D;
        let A_MINUS_D_VAR = FqVar::new_constant(self.cs(), A_MINUS_D)?;

        // 1.
        let u_1_var = (X_var.clone() + T_var.clone()) * (X_var.clone() - T_var.clone());
        let u_1 = (X + T) * (X - T);

        // 2.
        let den_var = u_1_var.clone() * A_MINUS_D_VAR.clone() * X_var.square()?;
        let den = u_1 * A_MINUS_D * X.square();
        let (_, v_var) = den_var.isqrt()?;
        // temp until we rework abs
        use crate::SqrtRatioZeta;
        let (_, v) = Fq::sqrt_ratio_zeta(&Fq::one(), &den);

        // 3.
        let u_2 = (v * u_1).abs();
        let u_2_var: FqVar = (v_var.clone() * u_1_var).abs()?;

        // 4.
        let u_3 = u_2 * Z - T;
        let _u_3_var = u_2_var * Z_var.clone() - T_var;

        // 5.
        let s_without_abs = A_MINUS_D * v * u_3 * X;
        let s = s_without_abs.abs();
        // let s_var = (A_MINUS_D_VAR * v_var * u_3_var * X_var).abs(s_without_abs)?;
        // We could do the above, instead here we just witness s (can improve efficiency here by removing
        // some of the R1CS steps above).
        let s_var = FqVar::new_witness(self.cs(), || Ok(s))?;

        Ok(s_var)
    }

    /// R1CS equivalent of `Encoding::vartime_decompress`
    pub fn decompress_from_field(s_var: FqVar, s: Fq) -> Result<ElementVar, SynthesisError> {
        let D4: Fq = EdwardsParameters::COEFF_D * Fq::from(4u32);
        let D4_VAR = FqVar::constant(D4);

        // 1. We do not check if canonically encoded here since we know FqVar is already
        // a valid Fq field element.

        // 2. Reject if negative.
        let is_nonnegative_var = s_var.is_nonnegative()?;
        let cs = s_var.cs();
        is_nonnegative_var.enforce_equal(&Boolean::TRUE)?;

        // 3. u_1 <- 1 - s^2
        let ss = s.square();
        let ss_var = s_var.square()?;
        let u_1 = Fq::one() - ss;
        let u_1_var = FqVar::one() - ss_var.clone();

        // 4. u_2 <- u_1^2 - 4d s^2
        let u_2 = u_1.square() - D4 * ss;
        let u_2_var = u_1_var.square()? - D4_VAR * ss_var.clone();

        // 5. sqrt
        let den_var = u_2_var.clone() * u_1_var.square()?;
        let den = u_2 * u_1.square();
        let (was_square_var, mut v_var) = den_var.isqrt()?;
        // temp until we rework abs
        use crate::SqrtRatioZeta;
        let (_, mut v) = Fq::sqrt_ratio_zeta(&Fq::one(), &den);
        was_square_var.enforce_equal(&Boolean::TRUE)?;

        // 6. Sign check
        let two_s_u_1 = Fq::from(2) * s * u_1;
        let check = two_s_u_1 * v;
        if check.is_negative() {
            v = -v;
        }
        let two_s_u_1_var = (FqVar::one() + FqVar::one()) * s_var * u_1_var.clone();
        // In `vartime_decompress`, we check if it's negative prior to taking
        // the negative, which is effectively the absolute value:
        v_var = v_var.abs()?;

        // 7. (Extended) Coordinates
        let x_var = two_s_u_1_var * v.square() * u_2_var;
        let y_var = (FqVar::one() + ss) * v_var * u_1_var;
        // let z = FqVar::one();
        // let t = x.clone() * y.clone();
        let x = two_s_u_1 * v.square() * u_2;
        let y = (Fq::one() + ss) * v * u_1;

        // Witness x, y
        let x_var = FqVar::new_witness(cs.clone(), || Ok(x))?;
        let y_var = FqVar::new_witness(cs, || Ok(y))?;

        // Note that the above are in extended, but we need affine coordinates
        // for forming `AffineVar` where x = X/Z, y = Y/Z. However Z is
        // hardcoded to be 1 above, so we can use x and y as is.
        Ok(ElementVar {
            inner: AffineVar::new(x_var, y_var),
        })
    }

    /// R1CS equivalent of `Element::elligator_map`
    pub(crate) fn elligator_map(r_0_var: &FqVar) -> Result<ElementVar, SynthesisError> {
        let cs = r_0_var.cs();

        let A_VAR = FqVar::new_constant(cs.clone(), EdwardsParameters::COEFF_A)?;
        let D_VAR = FqVar::new_constant(cs.clone(), EdwardsParameters::COEFF_D)?;
        let ZETA_VAR = FqVar::new_constant(cs.clone(), *ZETA)?;

        let r_var = ZETA_VAR * r_0_var.square()?;

        let den_var = (D_VAR.clone() * r_var.clone() - (D_VAR.clone() - A_VAR.clone()))
            * ((D_VAR.clone() - A_VAR.clone()) * r_var.clone() - D_VAR.clone());
        let num_var = (r_var.clone() + FqVar::one())
            * (A_VAR.clone() - (FqVar::one() + FqVar::one()) * D_VAR.clone());

        let x_var = num_var.clone() * den_var;
        let (iss_var, mut isri_var) = x_var.isqrt()?;

        // Case 1: iss is true, then sgn and twiddle are both 1
        // Case 2: iss is false, then sgn is -1 and twiddle is r_0
        let sgn_var =
            FqVar::conditionally_select(&iss_var, &FqVar::one(), &(FqVar::one()).negate()?)?;
        let twiddle_var = FqVar::conditionally_select(&iss_var, &FqVar::one(), &r_0_var)?;

        isri_var *= twiddle_var;

        let mut s_var = isri_var.clone() * num_var;
        let t_var = sgn_var.negate()?
            * isri_var
            * s_var.clone()
            * (r_var - FqVar::one())
            * (A_VAR.clone() - (FqVar::one() + FqVar::one()) * D_VAR).square()?
            - FqVar::one();

        let is_negative_var = s_var.is_negative()?;
        let cond_negate = is_negative_var.is_eq(&iss_var)?;
        // if s.is_negative() == iss { s = -s }
        s_var = FqVar::conditionally_select(&cond_negate, &s_var.negate()?, &s_var)?;

        // Convert to affine from Jacobi quartic
        // See commit cce38644d3343d9f7c46772dc2b945a9d17756d7
        let affine_x_num = (FqVar::one() + FqVar::one()) * s_var.clone();
        let affine_x_den = FqVar::one() + A_VAR.clone() * s_var.square()?;
        let affine_x_var = affine_x_num * affine_x_den.inverse()?;
        let affine_y_num = FqVar::one() - A_VAR * s_var.square()?;
        let affine_y_den = t_var;
        let affine_y_var = affine_y_num * affine_y_den.inverse()?;

        Ok(ElementVar {
            inner: AffineVar::new(affine_x_var, affine_y_var),
        })
    }

    /// Maps a field element to a decaf377 `ElementVar` suitable for CDH challenges.
    pub fn encode_to_curve(r_var: &FqVar) -> Result<ElementVar, SynthesisError> {
        ElementVar::elligator_map(r_var)
    }
}

impl EqGadget<Fq> for ElementVar {
    fn is_eq(&self, other: &Self) -> Result<Boolean<Fq>, SynthesisError> {
        // Section 4.5 of Decaf paper: X_1 * Y_2 = X_2 * Y_1
        // in extended coordinates, but note that x, y are affine here:
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
        self.inner.cs()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        let (x, y) = (self.inner.x.value()?, self.inner.y.value()?);
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
        let x = cond.select(&true_value.inner.x, &false_value.inner.x)?;
        let y = cond.select(&true_value.inner.y, &false_value.inner.y)?;

        Ok(ElementVar {
            inner: EdwardsVar::new(x, y),
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
        let f = || Ok(*f()?.borrow());
        let group_projective_point = f()?;

        // `new_variable` should *not* allocate any new variables or constraints in `cs` when
        // the mode is `AllocationMode::Constant` (see `AllocVar::new_constant`).
        //
        // Compare this with the implementation of this trait for `EdwardsVar`
        // where they check that the point is in the right subgroup prior to witnessing.
        match mode {
            AllocationMode::Constant => Ok(Self {
                inner: EdwardsVar::new_variable_omit_prime_order_check(
                    cs,
                    || Ok(group_projective_point.inner),
                    mode,
                )?,
            }),
            AllocationMode::Input => Ok(Self {
                inner: EdwardsVar::new_variable_omit_prime_order_check(
                    cs,
                    || Ok(group_projective_point.inner),
                    mode,
                )?,
            }),
            AllocationMode::Witness => {
                //let ge: EdwardsAffine = group_projective_point.inner.into();
                let P_var = AffineVar::new_variable_omit_prime_order_check(
                    ns!(cs, "P_affine"),
                    || Ok(group_projective_point.inner),
                    mode,
                )?;

                // At this point `P_var` might not be a valid representative of a decaf point.
                //
                // One way that is secure but provides stronger constraints than we need:
                //
                // 1. Encode (out of circuit) to an Fq
                let field_element = group_projective_point.vartime_compress_to_field();

                // 2. Witness the encoded value
                let compressed_P_var = FqVar::new_witness(cs, || Ok(field_element))?;

                // 3. Decode (in circuit)
                let decoded_var =
                    ElementVar::decompress_from_field(compressed_P_var, field_element)?;

                let P_element_var = Self { inner: P_var };
                decoded_var.enforce_equal(&P_element_var)?;

                Ok(P_element_var)
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

impl ToBitsGadget<Fq> for ElementVar {
    fn to_bits_le(&self) -> Result<Vec<Boolean<Fq>>, SynthesisError> {
        let compressed_fq = self.inner.to_bits_le()?;
        let encoded_bits = compressed_fq.to_bits_le()?;
        Ok(encoded_bits)
    }
}

impl ToBytesGadget<Fq> for ElementVar {
    fn to_bytes(&self) -> Result<Vec<UInt8<Fq>>, SynthesisError> {
        let compressed_fq = self.inner.to_bytes()?;
        let encoded_bytes = compressed_fq.to_bytes()?;
        Ok(encoded_bytes)
    }
}

impl<'a> GroupOpsBounds<'a, Element, ElementVar> for ElementVar {}

impl CurveVar<Element, Fq> for ElementVar {
    fn zero() -> Self {
        Self {
            inner: AffineVar::<EdwardsParameters, FqVar>::zero(),
        }
    }

    fn constant(other: Element) -> Self {
        Self {
            inner: AffineVar::<EdwardsParameters, FqVar>::constant(other.inner),
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
                let P = AffineVar::new_variable_omit_prime_order_check(cs, || Ok(ge.inner), mode)?;
                Ok(Self { inner: P })
            }
            _ => Err(SynthesisError::AssignmentMissing),
        }
    }

    fn enforce_prime_order(&self) -> Result<(), SynthesisError> {
        // This is decaf
        Ok(())
    }

    fn double_in_place(&mut self) -> Result<(), SynthesisError> {
        self.inner.double_in_place()?;
        Ok(())
    }

    fn negate(&self) -> Result<Self, SynthesisError> {
        let negated = self.inner.negate()?;
        Ok(Self { inner: negated })
    }
}

impl ToConstraintField<Fq> for Element {
    fn to_field_elements(&self) -> Option<Vec<Fq>> {
        self.inner.to_field_elements()
    }
}
