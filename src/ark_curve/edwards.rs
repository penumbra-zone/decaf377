use ark_ec::{
    twisted_edwards::{Affine, MontCurveConfig, Projective, TECurveConfig},
    CurveConfig,
};

use crate::ark_curve::constants::{GENERATOR_X, GENERATOR_Y};
use crate::{Fq, Fr};

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Decaf377EdwardsConfig;

// These types should not be exported. They are similar to `EdwardsAffine` and
// `EdwardsProjective` from the `ark_ed_on_bls12_377` crate, except using our own
// `Decaf377Config` that has the cofactor set to 1. Consumers of this
// library should use the `AffinePoint` and `Element` (projective)
// types.
pub type EdwardsAffine = Affine<Decaf377EdwardsConfig>;
pub type EdwardsProjective = Projective<Decaf377EdwardsConfig>;

impl CurveConfig for Decaf377EdwardsConfig {
    type BaseField = Fq;
    type ScalarField = Fr;

    const COFACTOR: &'static [u64] = &[1];

    const COFACTOR_INV: Fr = Fr::ONE;
}

impl TECurveConfig for Decaf377EdwardsConfig {
    /// COEFF_A = -1
    const COEFF_A: Fq = Fq::from_montgomery_limbs([
        10157024534604021774,
        16668528035959406606,
        5322190058819395602,
        387181115924875961,
    ]);

    /// COEFF_D = 3021
    const COEFF_D: Fq = Fq::from_montgomery_limbs([
        15008245758212136496,
        17341409599856531410,
        648869460136961410,
        719771289660577536,
    ]);

    const GENERATOR: EdwardsAffine = EdwardsAffine::new_unchecked(GENERATOR_X, GENERATOR_Y);

    type MontCurveConfig = Decaf377EdwardsConfig;

    /// Multiplication by `a` is just negation.
    #[inline(always)]
    fn mul_by_a(elem: Self::BaseField) -> Self::BaseField {
        -elem
    }

    fn is_in_correct_subgroup_assuming_on_curve(_: &Affine<Self>) -> bool {
        true
    }
}

impl MontCurveConfig for Decaf377EdwardsConfig {
    const COEFF_A: Fq = Fq::from_montgomery_limbs([
        13800168384327121454,
        6841573379969807446,
        12529593083398462246,
        853978956621483129,
    ]);

    const COEFF_B: Fq = Fq::from_montgomery_limbs([
        7239382437352637935,
        14509846070439283655,
        5083066350480839936,
        1265663645916442191,
    ]);

    type TECurveConfig = Decaf377EdwardsConfig;
}
