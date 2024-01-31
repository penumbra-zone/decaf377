use core::cell::RefCell;

use ark_relations::r1cs::SynthesisError;

use super::inner::ElementVar;
use crate::ark_curve::r1cs::FqVar;

#[derive(Clone, Debug)]
pub enum Inner {
    Encoding(FqVar),
    Element(ElementVar),
    EncodingAndElement {
        encoding: FqVar,
        element: ElementVar,
    },
}

#[derive(Clone, Debug)]
pub struct LazyElementVar {
    inner: RefCell<Inner>,
}

impl LazyElementVar {
    pub fn new_from_element(element: ElementVar) -> Self {
        Self {
            inner: RefCell::new(Inner::Element(element)),
        }
    }

    pub fn new_from_encoding(encoding: FqVar) -> Self {
        Self {
            inner: RefCell::new(Inner::Encoding(encoding)),
        }
    }

    pub fn element(&self) -> Result<ElementVar, SynthesisError> {
        if matches!(&*self.inner.borrow(), Inner::Encoding(_)) {
            let encoding = self.encoding()?;
            let element = ElementVar::decompress_from_field(encoding.clone())?;
            *self.inner.borrow_mut() = Inner::EncodingAndElement { encoding, element };
        }
        match &*self.inner.borrow() {
            Inner::Encoding(_) => {
                unreachable!("encoding should have been replaced by encoding and element")
            }
            Inner::Element(element) => Ok(element.clone()),
            Inner::EncodingAndElement { element, .. } => Ok(element.clone()),
        }
    }

    pub fn encoding(&self) -> Result<FqVar, SynthesisError> {
        if matches!(&*self.inner.borrow(), Inner::Element(_)) {
            let element = self.element()?;
            let encoding = element.compress_to_field()?;
            *self.inner.borrow_mut() = Inner::EncodingAndElement { encoding, element };
        }
        match &*self.inner.borrow() {
            Inner::Encoding(encoding) => Ok(encoding.clone()),
            Inner::Element(_) => {
                unreachable!("encoding should have been replaced by encoding and element")
            }
            Inner::EncodingAndElement { encoding, .. } => Ok(encoding.clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Bls12_377, Element, Fq};
    use ark_groth16::{r1cs_to_qap::LibsnarkReduction, Groth16, ProvingKey, VerifyingKey};
    use ark_r1cs_std::prelude::AllocVar;
    use ark_relations::r1cs::ConstraintSynthesizer;
    use ark_snark::SNARK;
    use rand_core::OsRng;

    use super::*;

    #[derive(Clone)]
    struct TestCircuit {
        // Witness
        encoding: Fq,
    }

    impl ConstraintSynthesizer<Fq> for TestCircuit {
        fn generate_constraints(
            self,
            cs: ark_relations::r1cs::ConstraintSystemRef<Fq>,
        ) -> ark_relations::r1cs::Result<()> {
            let encoding_var = FqVar::new_witness(cs, || Ok(self.encoding))?;
            let lazy_var = LazyElementVar::new_from_encoding(encoding_var);
            let _element_var = lazy_var.element()?;
            Ok(())
        }
    }

    impl TestCircuit {
        fn generate_test_parameters() -> (ProvingKey<Bls12_377>, VerifyingKey<Bls12_377>) {
            let element = Element::default();
            let encoding = element.vartime_compress_to_field();
            let circuit = TestCircuit { encoding };
            let (pk, vk) = Groth16::<Bls12_377, LibsnarkReduction>::circuit_specific_setup(
                circuit, &mut OsRng,
            )
            .expect("can perform circuit specific setup");
            (pk, vk)
        }
    }

    #[test]
    fn lazy_element_var_evaluation() {
        let (pk, _) = TestCircuit::generate_test_parameters();
        let mut rng = OsRng;
        let test_circuit = TestCircuit {
            encoding: Element::default().vartime_compress_to_field(),
        };
        Groth16::<Bls12_377, LibsnarkReduction>::prove(&pk, test_circuit, &mut rng)
            .expect("can generate proof");
    }
}
