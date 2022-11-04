use ark_ed_on_bls12_377::constraints::FqVar;
use ark_ff::One;
use ark_r1cs_std::prelude::{AllocVar, FieldVar};
use ark_r1cs_std::R1CSVar;
use ark_r1cs_std::{eq::EqGadget, prelude::AllocationMode};
use ark_relations::ns;
use ark_relations::r1cs::SynthesisError;

use crate::{Fq, SqrtRatioZeta};

pub trait FqVarExtension {
    fn abs(&self) -> FqVar;
    fn isqrt(x: FqVar) -> Result<Fq, SynthesisError>;
}

impl FqVarExtension for FqVar {
    // Remove this in favor of impl Sign for FqVar
    fn abs(&self) -> FqVar {
        todo!()
    }

    /// Square root in R1CS
    ///
    /// Returns the result of the sqrt computation (out of circuit)
    /// and a boolean constraint that `y = sqrt(x)` is known.
    fn isqrt(x: FqVar) -> Result<Fq, SynthesisError> {
        // Out of circuit sqrt computation
        let num = FqVar::constant(Fq::one());
        let (_, y) = Fq::sqrt_ratio_zeta(&x.value()?, &num.value()?);

        // Add constraints to certify we know the square root of x
        let cs = x.cs();
        let lhs = y * y;
        // TODO: Is constant the right allocation mode?
        let lhs_var =
            FqVar::new_variable(ns!(cs, "lhs_sqrt"), || Ok(lhs), AllocationMode::Constant)?;
        lhs_var.enforce_equal(&x)?;
        Ok(y)
    }
}

//impl Sign for FqVar
