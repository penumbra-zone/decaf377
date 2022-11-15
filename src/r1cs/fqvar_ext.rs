use ark_ed_on_bls12_377::constraints::FqVar;
use ark_ff::One;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::prelude::{AllocVar, Boolean, FieldVar};
use ark_r1cs_std::select::CondSelectGadget;
use ark_r1cs_std::{R1CSVar, ToBitsGadget};
use ark_relations::r1cs::SynthesisError;

use crate::{constants::ZETA, Fq, SqrtRatioZeta};

pub trait FqVarExtension: Sized {
    fn isqrt(&self) -> Result<(Boolean<Fq>, FqVar), SynthesisError>;

    // This is similar to the Sign trait in this crate,
    // however: we need to return `Result<_, SynthesisError>`
    // everywhere.
    fn is_negative(&self) -> Result<Boolean<Fq>, SynthesisError>;
    fn is_nonnegative(&self) -> Result<Boolean<Fq>, SynthesisError>;
    fn abs(self) -> Result<Self, SynthesisError>;
}

impl FqVarExtension for FqVar {
    /// Inverse square root in R1CS
    ///
    /// Cases:
    /// - Case 1: `(true, sqrt(num/den))` if `num` and `den` are both nonzero and `num/den` is square;
    /// - Case 2: `(true, 0)` if `num` is zero;
    /// - Case 3: `(false, 0)` if `den` is zero;
    /// - Case 4: `(false, sqrt(zeta*num/den))` if `num` and `den` are both nonzero and `num/den` is nonsquare;
    fn isqrt(&self) -> Result<(Boolean<Fq>, FqVar), SynthesisError> {
        // During mode `SynthesisMode::Setup`, value() will not provide a field element.
        let x = self.value().unwrap_or(Fq::one());

        // Out of circuit sqrt computation
        let (was_square, y) = Fq::sqrt_ratio_zeta(&Fq::one(), &x);

        let cs = self.cs();
        let was_square_var = Boolean::new_witness(cs.clone(), || Ok(was_square))?;
        let y_var = FqVar::new_witness(cs.clone(), || Ok(y))?;
        let y_squared_var = y_var.square()?;

        // The below is a flattened version of the four cases above, excluding case 2 since `num` is hardcoded
        // to be one.
        //
        // Case 3: `(false, 0)` if `den` is zero
        let was_not_square_var = was_square_var.not();
        let x_var_is_zero = self.is_eq(&FqVar::zero())?;
        let in_case_3 = was_not_square_var.and(&x_var_is_zero)?;
        // Certify the return value y is 0.
        y_squared_var.conditional_enforce_equal(&FqVar::zero(), &in_case_3)?;

        // Case 1: `(true, sqrt(num/den))` if `num` and `den` are both nonzero and `num/den` is square
        let x_var_inv = self.inverse()?;
        let in_case_1 = was_square_var.clone();
        // Certify the return value y is sqrt(1/x)
        y_squared_var.conditional_enforce_equal(&x_var_inv, &in_case_1)?;

        // Case 4: `(false, sqrt(zeta*num/den))` if `num` and `den` are both nonzero and `num/den` is nonsquare;
        let zeta_var = FqVar::new_constant(cs, *ZETA)?;
        let zeta_times_one_over_x_var = zeta_var * x_var_inv;
        let in_case_4 = was_not_square_var.and(&x_var_is_zero.not())?;
        // Certify the return value y is sqrt(zeta * 1/x)
        y_squared_var.conditional_enforce_equal(&zeta_times_one_over_x_var, &in_case_4)?;

        Ok((was_square_var, y_var))
    }

    fn is_negative(&self) -> Result<Boolean<Fq>, SynthesisError> {
        Ok(self.is_nonnegative()?.not())
    }

    fn is_nonnegative(&self) -> Result<Boolean<Fq>, SynthesisError> {
        let bitvars = self.to_bits_le()?;

        // bytes[0] & 1 == 0
        let true_var = Boolean::<Fq>::TRUE;
        let false_var = Boolean::<Fq>::FALSE;
        let mut is_nonnegative_var = true_var.clone();
        // Check first 8 bits
        for _ in 0..8 {
            let lhs = bitvars[0].and(&true_var.clone())?;
            let this_loop_var = lhs.is_eq(&false_var)?;
            is_nonnegative_var = is_nonnegative_var.and(&this_loop_var)?;
        }
        Ok(is_nonnegative_var)
    }

    fn abs(self) -> Result<Self, SynthesisError> {
        let absolute_value =
            FqVar::conditionally_select(&self.is_nonnegative()?, &self, &self.negate()?)?;
        Ok(absolute_value)
    }
}
