use crate::Fq;

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
        (self.to_le_limbs()[0] & 1) == 0
    }
}
