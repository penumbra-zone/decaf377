use ark_ec::models::{twisted_edwards_extended::GroupProjective, TEModelParameters};
use ark_ff::{Field, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;

use crate::{constants, Fr};

pub trait OnCurve {
    fn is_on_curve(&self) -> bool;
}

impl<P: TEModelParameters> OnCurve for GroupProjective<P> {
    #[allow(non_snake_case)]
    fn is_on_curve(&self) -> bool {
        let XX = self.x.square();
        let YY = self.y.square();
        let ZZ = self.z.square();
        let TT = self.t.square();

        let on_curve = (YY + P::COEFF_A * XX) == (ZZ + P::COEFF_D * TT);
        let on_segre_embedding = self.t * self.z == self.x * self.y;
        let z_non_zero = self.z != P::BaseField::zero();

        let mut r_bytes = [0u8; 32];
        (*constants::R)
            .serialize(&mut r_bytes[..])
            .expect("serialization into array should be infallible");
        let r = P::ScalarField::from_le_bytes_mod_order(&r_bytes);
        let mut P = self.clone();
        // Multiply by N to check if identity
        P *= r;
        let point_order_r = P == GroupProjective::zero();
        P *= r;
        let point_order_2r = P == GroupProjective::zero();
        P *= r;
        P *= r;
        let point_order_4r = P == GroupProjective::zero();
        // Point order should be at most 2r, and not 4r
        let point_order_correct = (point_order_r || point_order_2r) && !point_order_4r;

        on_curve && on_segre_embedding && z_non_zero && point_order_correct
    }
}
