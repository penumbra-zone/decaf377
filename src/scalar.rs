use core::ops::Neg;
use core::ops::{Add, AddAssign};
use core::ops::{Mul, MulAssign};
use core::ops::{Sub, SubAssign};

use ark_ff::Zero;
use zeroize::Zeroize;

/// `Scalar` Represents an integer value.
pub struct Scalar {
    pub(crate) inner: ark_ed_on_bls12_377::Fr,
}

impl Default for Scalar {
    fn default() -> Self {
        Scalar {
            inner: ark_ed_on_bls12_377::Fr::zero(),
        }
    }
}

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

impl<'a, 'b> Add<&'b Scalar> for &'a Scalar {
    type Output = Scalar;

    fn add(self, other: &'b Scalar) -> Scalar {
        Scalar {
            inner: self.inner + other.inner,
        }
    }
}

impl<'b> Add<&'b Scalar> for Scalar {
    type Output = Scalar;
    fn add(self, other: &'b Scalar) -> Scalar {
        &self + other
    }
}

impl<'a> Add<Scalar> for &'a Scalar {
    type Output = Scalar;
    fn add(self, other: Scalar) -> Scalar {
        self + &other
    }
}

impl Add<Scalar> for Scalar {
    type Output = Scalar;
    fn add(self, other: Scalar) -> Scalar {
        &self + &other
    }
}

impl<'b> AddAssign<&'b Scalar> for Scalar {
    fn add_assign(&mut self, other: &'b Scalar) {
        *self = Scalar {
            inner: self.inner + other.inner,
        }
    }
}

impl AddAssign<Scalar> for Scalar {
    fn add_assign(&mut self, other: Scalar) {
        *self += &other;
    }
}

impl<'a, 'b> Sub<&'b Scalar> for &'a Scalar {
    type Output = Scalar;

    fn sub(self, other: &'b Scalar) -> Scalar {
        Scalar {
            inner: self.inner - other.inner,
        }
    }
}

impl<'b> Sub<&'b Scalar> for Scalar {
    type Output = Scalar;

    fn sub(self, other: &'b Scalar) -> Scalar {
        &self - other
    }
}

impl<'a> Sub<Scalar> for &'a Scalar {
    type Output = Scalar;

    fn sub(self, other: Scalar) -> Scalar {
        self - &other
    }
}

impl Sub<Scalar> for Scalar {
    type Output = Scalar;

    fn sub(self, other: Scalar) -> Scalar {
        &self - &other
    }
}

impl<'b> SubAssign<&'b Scalar> for Scalar {
    fn sub_assign(&mut self, other: &'b Scalar) {
        *self = Scalar {
            inner: self.inner - other.inner,
        }
    }
}

impl SubAssign<Scalar> for Scalar {
    fn sub_assign(&mut self, other: Scalar) {
        *self -= &other;
    }
}

impl<'a, 'b> Mul<&'b Scalar> for &'a Scalar {
    type Output = Scalar;

    fn mul(self, other: &'b Scalar) -> Scalar {
        Scalar {
            inner: self.inner * other.inner,
        }
    }
}

impl<'b> Mul<&'b Scalar> for Scalar {
    type Output = Scalar;

    fn mul(self, other: &'b Scalar) -> Scalar {
        &self * other
    }
}

impl<'a> Mul<Scalar> for &'a Scalar {
    type Output = Scalar;

    fn mul(self, other: Scalar) -> Scalar {
        self * &other
    }
}

impl Mul<Scalar> for Scalar {
    type Output = Scalar;

    fn mul(self, other: Scalar) -> Scalar {
        &self * &other
    }
}

impl<'b> MulAssign<&'b Scalar> for Scalar {
    fn mul_assign(&mut self, other: &'b Scalar) {
        *self = Scalar {
            inner: self.inner * other.inner,
        }
    }
}

impl MulAssign<Scalar> for Scalar {
    fn mul_assign(&mut self, other: Scalar) {
        *self *= &other;
    }
}

impl Neg for Scalar {
    type Output = Self;

    fn neg(self) -> Self {
        Scalar { inner: -self.inner }
    }
}
