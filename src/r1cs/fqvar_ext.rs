use ark_ed_on_bls12_377::constraints::FqVar;
use ark_ff::One;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::prelude::{AllocVar, Boolean, FieldVar};
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::SynthesisError;

use crate::sign::Sign;
use crate::{constants::ZETA, Fq, SqrtRatioZeta};

pub trait FqVarExtension: Sized {
    fn isqrt(&self) -> Result<(bool, Fq), SynthesisError>;

    // This is similar to the Sign trait in this crate,
    // however: we need to return `Result<_, SynthesisError>`
    // everywhere and we need to pass in the out-of-circuit field
    // element.
    fn is_negative(&self) -> Result<bool, SynthesisError>;
    fn is_nonnegative(&self, value: Fq) -> Result<bool, SynthesisError>;
    fn abs(self, value: Fq) -> Result<Self, SynthesisError>;
    // TODO: Remove value: Fq from everything
}

impl FqVarExtension for FqVar {
    /// Inverse square root in R1CS
    ///
    /// Cases:
    /// - Case 1: `(true, sqrt(num/den))` if `num` and `den` are both nonzero and `num/den` is square;
    /// - Case 2: `(true, 0)` if `num` is zero;
    /// - Case 3: `(false, 0)` if `den` is zero;
    /// - Case 4: `(false, sqrt(zeta*num/den))` if `num` and `den` are both nonzero and `num/den` is nonsquare;
    fn isqrt(&self) -> Result<(bool, Fq), SynthesisError> {
        // During mode `SynthesisMode::Setup`, value() will not provide a field element.
        let x = self.value().unwrap_or(Fq::one());

        // Out of circuit sqrt computation
        let (was_square, y) = Fq::sqrt_ratio_zeta(&Fq::one(), &x);

        let cs = self.cs();
        let was_square_var = Boolean::new_witness(cs.clone(), || Ok(was_square))?;
        let y_squared_var = FqVar::new_witness(cs.clone(), || Ok(y * y))?;

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
        let in_case_1 = was_square_var;
        // Certify the return value y is sqrt(1/x)
        y_squared_var.conditional_enforce_equal(&x_var_inv, &in_case_1)?;

        // Case 4: `(false, sqrt(zeta*num/den))` if `num` and `den` are both nonzero and `num/den` is nonsquare;
        let zeta_var = FqVar::new_constant(cs, *ZETA)?;
        let zeta_times_one_over_x_var = zeta_var * x_var_inv;
        let in_case_4 = was_not_square_var.and(&x_var_is_zero.not())?;
        // Certify the return value y is sqrt(zeta * 1/x)
        y_squared_var.conditional_enforce_equal(&zeta_times_one_over_x_var, &in_case_4)?;

        // TODO: Witness values and return Boolean and FqVar
        Ok((was_square, y))
    }

    fn is_negative(&self) -> Result<bool, SynthesisError> {
        todo!()
        // TODO: Witness and return Boolean
    }

    fn is_nonnegative(&self, value: Fq) -> Result<bool, SynthesisError> {
        // TODO: Add constraints here for not in circuit
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
