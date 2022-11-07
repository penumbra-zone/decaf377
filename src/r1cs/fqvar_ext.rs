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
    fn isqrt(x: FqVar) -> Result<(bool, Fq), SynthesisError>;

    // This is similar to the Sign trait in this crate,
    // however: we need to return `Result<_, SynthesisError>`
    // everywhere.
    fn is_nonnegative(&self) -> Result<bool, SynthesisError>;
    fn abs(self) -> Result<Self, SynthesisError>;
}

impl FqVarExtension for FqVar {
    /// Square root in R1CS
    ///
    /// Returns the result of the sqrt computation (out of circuit)
    /// and a boolean constraint that `y = sqrt(x)` is known.
    fn isqrt(x: FqVar) -> Result<(bool, Fq), SynthesisError> {
        // Out of circuit sqrt computation
        let num = FqVar::constant(Fq::one());
        let (was_square, y) = Fq::sqrt_ratio_zeta(&x.value()?, &num.value()?);

        // Add constraints to certify we know the square root of x
        let cs = x.cs();
        let lhs = y * y;
        // TODO: Is constant the right allocation mode?
        let lhs_var =
            FqVar::new_variable(ns!(cs, "lhs_sqrt"), || Ok(lhs), AllocationMode::Constant)?;
        lhs_var.enforce_equal(&x)?;
        Ok((was_square, y))
    }

    fn is_nonnegative(&self) -> Result<bool, SynthesisError> {
        let value = self.value()?;
        Ok(value.is_nonnegative())
    }

    fn abs(self) -> Result<Self, SynthesisError> {
        if self.is_nonnegative()? {
            Ok(self)
        } else {
            self.negate()
        }
    }
}
