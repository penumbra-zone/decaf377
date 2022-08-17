use ark_ec::{
    models::{twisted_edwards_extended::GroupProjective, TEModelParameters},
    ProjectiveCurve,
};
use ark_ff::{BigInteger, Field, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;

use crate::constants;

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
        let point_order_2r = {
            let mut r_bytes = [0u8; 32];
            (*constants::R)
                .serialize(&mut r_bytes[..])
                .expect("serialization into array should be infallible");
            let r = P::ScalarField::from_le_bytes_mod_order(&r_bytes);
            let mut two_r_bigint = r.into_repr();
            two_r_bigint.mul2();
            self.mul(two_r_bigint) == GroupProjective::zero()
        };

        on_curve && on_segre_embedding && z_non_zero && point_order_2r
    }
}
