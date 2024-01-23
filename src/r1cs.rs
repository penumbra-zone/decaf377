pub mod element;
pub mod fqvar_ext;
mod inner;
mod lazy;
pub mod ops;

use ark_ff::ToConstraintField;
use ark_std::vec::Vec;
pub use element::ElementVar;
pub use lazy::TestCircuit;

use crate::{Element, Fq};
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, OptimizationGoal, SynthesisMode,
};

pub type FqVar = FpVar<Fq>;

pub trait CountConstraints: ConstraintSynthesizer<Fq> + Sized {
    fn num_constraints_and_instance_variables(self) -> (usize, usize) {
        let cs = ConstraintSystem::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        cs.set_mode(SynthesisMode::Setup);

        // Synthesize the circuit.
        self.generate_constraints(cs.clone())
            .expect("can generate constraints");
        cs.finalize();
        (cs.num_constraints(), cs.num_instance_variables())
    }
}

impl<T> CountConstraints for T where T: ConstraintSynthesizer<Fq> + Sized {}

impl ToConstraintField<Fq> for Element {
    fn to_field_elements(&self) -> Option<Vec<Fq>> {
        Some([self.vartime_compress_to_field()].to_vec())
    }
}
