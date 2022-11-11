use ark_ed_on_bls12_377::constraints::FqVar;
use ark_ff::One;
use ark_r1cs_std::prelude::{AllocVar, FieldVar};
use ark_r1cs_std::R1CSVar;
use ark_r1cs_std::{eq::EqGadget, prelude::AllocationMode};
use ark_relations::ns;
use ark_relations::r1cs::SynthesisError;

use crate::sign::Sign;
use crate::{Fq, SqrtRatioZeta};

pub trait FqVarExtension: Sized {
    fn isqrt(x: Fq, x_var: FqVar) -> Result<(bool, Fq), SynthesisError>;

    // This is similar to the Sign trait in this crate,
    // however: we need to return `Result<_, SynthesisError>`
    // everywhere and we need to pass in the out-of-circuit field
    // element.
    fn is_nonnegative(&self, value: Fq) -> Result<bool, SynthesisError>;
    fn abs(self, value: Fq) -> Result<Self, SynthesisError>;
}

impl FqVarExtension for FqVar {
    /// Square root in R1CS
    ///
    /// Returns the result of the sqrt computation (out of circuit)
    /// and a boolean constraint that `y = sqrt(x)` is known.
    fn isqrt(x: Fq, x_var: FqVar) -> Result<(bool, Fq), SynthesisError> {
        // Out of circuit sqrt computation
        let (was_square, y) = Fq::sqrt_ratio_zeta(&x, &Fq::one());

        // Add constraints to certify we know the square root of x
        let lhs = y * y;
        let lhs_var = FqVar::new_variable(
            ns!(x_var.cs(), "lhs_sqrt"),
            || Ok(lhs),
            AllocationMode::Witness,
        )?;
        lhs_var.enforce_equal(&x_var)?;
        Ok((was_square, y))
    }

    fn is_nonnegative(&self, value: Fq) -> Result<bool, SynthesisError> {
        Ok(value.is_nonnegative())
    }

    fn abs(self, value: Fq) -> Result<Self, SynthesisError> {
        if self.is_nonnegative(value)? {
            Ok(self)
        } else {
            self.negate()
        }
    }
}
