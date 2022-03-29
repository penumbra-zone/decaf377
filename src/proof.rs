use ark_ec::twisted_edwards_extended::GroupProjective;
use ark_ed_on_bls12_377::EdwardsParameters;

use jf_plonk::circuit::customized::ecc::Point;
use jf_plonk::circuit::PlonkCircuit;

use crate::{Element, Fq};

// temp: For testing purposes only until we implement a `decaf377::Element` gadget
impl From<Element> for Point<Fq> {
    fn from(decaf_element: Element) -> Point<Fq> {
        let inner: GroupProjective<EdwardsParameters> = decaf_element.inner.into();
        inner.into()
    }
}

// Extension trait on `PlonkCircuit` would add methods like
// `create_decaf377_public_point_variable`
// `decaf377_ecc_add`
// etc.
trait PlonkCircuitExt {}

// `PlonkCircuit<F>` is defined over `F: FftField`.
impl PlonkCircuitExt for PlonkCircuit<Fq> {}
