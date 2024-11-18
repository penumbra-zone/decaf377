use ark_ff::Field;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::prelude::ToBitsGadget;
use ark_r1cs_std::prelude::{AllocVar, Boolean, FieldVar};
use ark_r1cs_std::select::CondSelectGadget;
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::SynthesisError;

use crate::ark_curve::{constants::ZETA, r1cs::FqVar};
use crate::Fq;

pub trait FqVarExtension: Sized {
    fn isqrt(&self) -> Result<(Boolean<Fq>, FqVar), SynthesisError>;

    // This is similar to the Sign trait in this crate,
    // however: we need to return `Result<_, SynthesisError>`
    // everywhere.
    fn is_negative(&self) -> Result<Boolean<Fq>, SynthesisError>;
    fn is_nonnegative(&self) -> Result<Boolean<Fq>, SynthesisError>;
    fn abs(self) -> Result<Self, SynthesisError>;
}

// The methods for logical operations (and, or, not) were moved from the Boolean
// enum to helper functions in AllocatedBool. Consequently, we need to do some
// cursed redirection for the the Boolean enum to delegate these operations to the
// underlying AllocatedBool when applicable.
fn not<F: Field>(boolean: &Boolean<F>) -> Result<Boolean<F>, SynthesisError> {
    match boolean {
        Boolean::Var(allocated) => Ok(Boolean::Var(allocated.not()?)),
        Boolean::Constant(value) => Ok(Boolean::Constant(!value)),
    }
}

fn and<F: Field>(a: &Boolean<F>, b: &Boolean<F>) -> Result<Boolean<F>, SynthesisError> {
    match (a, b) {
        // Both are AllocatedBool
        (Boolean::Var(alloc_a), Boolean::Var(alloc_b)) => Ok(Boolean::Var(alloc_a.and(alloc_b)?)),
        // Both are constant
        (Boolean::Constant(val_a), Boolean::Constant(val_b)) => {
            Ok(Boolean::Constant(*val_a & *val_b))
        }
        // One is constant, one is variable
        (Boolean::Constant(true), other) | (other, Boolean::Constant(true)) => Ok(other.clone()),
        (Boolean::Constant(false), _) | (_, Boolean::Constant(false)) => {
            Ok(Boolean::Constant(false))
        }
    }
}

fn or<F: Field>(a: &Boolean<F>, b: &Boolean<F>) -> Result<Boolean<F>, SynthesisError> {
    match (a, b) {
        (Boolean::Var(alloc_a), Boolean::Var(alloc_b)) => Ok(Boolean::Var(alloc_a.or(alloc_b)?)),
        (Boolean::Constant(val_a), Boolean::Constant(val_b)) => {
            Ok(Boolean::Constant(*val_a | *val_b))
        }
        _ => Err(SynthesisError::Unsatisfiable),
    }
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
        let den = self.value().unwrap_or(Fq::ONE);

        // Out of circuit sqrt computation:
        // Note: `num = 1`
        // `y = sqrt(num/den)`
        let (was_square, y) = Fq::sqrt_ratio_zeta(&Fq::ONE, &den);

        let cs = self.cs();
        let was_square_var = Boolean::new_witness(cs.clone(), || Ok(was_square))?;
        let y_var = FqVar::new_witness(cs.clone(), || Ok(y))?;
        // `y^2 = num/den`
        let y_squared_var = y_var.square()?;

        // The below is a flattened version of the four cases above, excluding case 2 since `num` is hardcoded
        // to be one.
        //
        // Case 1: `(true, sqrt(num/den))` if `num` and `den` are both nonzero and `num/den` is square
        let den_var_is_zero = self.is_eq(&FqVar::zero())?;
        let den_var = FqVar::conditionally_select(&den_var_is_zero, &FqVar::one(), self)?;
        let den_var_inv = den_var.inverse()?;
        // Note we could be in case 1 or case 2 based on the constraint that `was_square = true`, but
        // num is hardcoded to be one above, so we're in case 1.
        let in_case_1 = was_square_var.clone();
        // Certify the return value y is sqrt(1/den) when we're in case 1. This also certifies that we are not in case 2.
        y_squared_var.conditional_enforce_equal(&den_var_inv, &in_case_1)?;

        // Case 3: `(false, 0)` if `den` is zero

        let was_not_square_var = not(&was_square_var)?;
        let in_case_3 = and(&was_not_square_var, &den_var_is_zero)?;
        // Certify the return value y is 0 when we're in case 3.
        y_squared_var.conditional_enforce_equal(&FqVar::zero(), &in_case_3)?;

        // Case 4: `(false, sqrt(zeta*num/den))` if `num` and `den` are both nonzero and `num/den` is nonsquare;
        let zeta_var = FqVar::new_constant(cs, ZETA)?;
        let zeta_times_one_over_den_var = zeta_var * den_var_inv;
        let is_den_var_is_zero = not(&den_var_is_zero)?;
        let in_case_4 = and(&was_not_square_var, &is_den_var_is_zero)?;
        // Certify the return value y is sqrt(zeta * 1/den)
        y_squared_var.conditional_enforce_equal(&zeta_times_one_over_den_var, &in_case_4)?;

        // Ensure that we are in case 1, 3, or 4.
        let in_case = or(&in_case_1, &or(&in_case_3, &in_case_4)?)?;
        in_case.enforce_equal(&Boolean::TRUE)?;

        Ok((was_square_var, y_var))
    }

    fn is_negative(&self) -> Result<Boolean<Fq>, SynthesisError> {
        Ok(not(&self.is_nonnegative()?)?)
    }

    fn is_nonnegative(&self) -> Result<Boolean<Fq>, SynthesisError> {
        let bitvars = self.to_bits_le()?;

        // bytes[0] & 1 == 0
        let true_var = Boolean::<Fq>::TRUE;
        let false_var = Boolean::<Fq>::FALSE;

        // Check least significant bit
        let lhs = and(&bitvars[0], &true_var)?;
        let is_nonnegative_var = lhs.is_eq(&false_var)?;

        Ok(is_nonnegative_var)
    }

    fn abs(self) -> Result<Self, SynthesisError> {
        let absolute_value =
            FqVar::conditionally_select(&self.is_nonnegative()?, &self, &self.negate()?)?;
        Ok(absolute_value)
    }
}
