use ark_ed_on_bls12_377::Fq;

pub trait Sign: core::ops::Neg<Output = Self> + Sized {
    fn is_nonnegative(&self) -> bool;

    fn is_negative(&self) -> bool {
        !self.is_nonnegative()
    }

    fn abs(self) -> Self {
        if self.is_nonnegative() {
            self
        } else {
            -self
        }
    }
}

impl Sign for Fq {
    fn is_nonnegative(&self) -> bool {
        use ark_serialize::CanonicalSerialize;
        let mut bytes = [0u8; 32];
        self.serialize_compressed(&mut bytes[..])
            .expect("serialization into array should be infallible");
        bytes[0] & 1 == 0
    }
}
