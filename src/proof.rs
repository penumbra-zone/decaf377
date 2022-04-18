use ark_ec::twisted_edwards_extended::GroupAffine;
use ark_ec::{ModelParameters, TEModelParameters};
use ark_ed_on_bls12_377::EdwardsParameters;
use ark_ff::PrimeField;
use plonk_core::{
    constraint_system::{StandardComposer, Variable},
    prelude::*,
};

use crate::Element;

// temp: For testing purposes only until we implement a `decaf377::Element` gadget
impl From<Element> for GroupAffine<EdwardsParameters> {
    fn from(decaf_element: Element) -> GroupAffine<EdwardsParameters> {
        decaf_element.inner.into()
    }
}

// Additional functionality for convenience on the PLONK `StandardComposer`
pub trait ComposerExt<F, P>
where
    F: PrimeField,
    P: TEModelParameters<BaseField = F>,
{
    fn assert_points_not_equal(&mut self, a: Point<P>, b: Point<P>) {}
}

impl<F, P> ComposerExt<F, P> for StandardComposer<F, P>
where
    F: PrimeField,
    P: TEModelParameters<BaseField = F>,
{
    fn assert_points_not_equal(&mut self, a: Point<P>, b: Point<P>) {
        let a_x = a.x();
        let a_y = a.y();

        let b_x = b.x();
        let b_y = b.y();

        // Each gate here outputs a variable that is 1 if the two
        // variables are equal, else 0. We must check they are 0.
        let x_var = self.is_eq_with_output(*a_x, *b_x);
        let y_var = self.is_eq_with_output(*a_y, *b_y);

        let zero = self.zero_var();
        // Add constraints to the circuit that both variables are 0.
        self.assert_equal(x_var, zero);
        self.assert_equal(y_var, zero);
    }
}
