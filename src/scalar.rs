use core::ops::Neg;
use core::ops::{Add, AddAssign};
use core::ops::{Mul, MulAssign};
use core::ops::{Sub, SubAssign};

use zeroize::Zeroize;

/// `Scalar` Represents an integer value.
pub struct Scalar {
    pub(crate) inner: ark_ed_on_bls12_377::Fr,
}

// TODO: Methods to instantiate Scalar

impl Zeroize for Scalar {
    fn zeroize(&mut self) {
        self.inner.zeroize();
    }
}

impl PartialEq for Scalar {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<'b> Add<&'b Scalar> for Scalar {
    type Output = Scalar;

    fn add(self, other: &'b Scalar) -> Scalar {
        Scalar {
            inner: self.inner + other.inner,
        }
    }
}

impl<'b> AddAssign<&'b Scalar> for Scalar {
    fn add_assign(&mut self, other: &'b Scalar) {
        *self = Scalar {
            inner: self.inner + other.inner,
        }
    }
}

impl<'b> Sub<&'b Scalar> for Scalar {
    type Output = Scalar;

    fn sub(self, other: &'b Scalar) -> Scalar {
        Self {
            inner: self.inner - other.inner,
        }
    }
}

impl<'b> SubAssign<&'b Scalar> for Scalar {
    fn sub_assign(&mut self, other: &'b Scalar) {
        *self = Scalar {
            inner: self.inner - other.inner,
        }
    }
}

impl<'b> Mul<&'b Scalar> for Scalar {
    type Output = Scalar;

    fn mul(self, other: &'b Scalar) -> Scalar {
        Scalar {
            inner: self.inner * other.inner,
        }
    }
}

impl<'b> MulAssign<&'b Scalar> for Scalar {
    fn mul_assign(&mut self, other: &'b Scalar) {
        *self = Scalar {
            inner: self.inner * other.inner,
        }
    }
}

impl Neg for Scalar {
    type Output = Self;

    fn neg(self) -> Self {
        Scalar { inner: -self.inner }
    }
}
