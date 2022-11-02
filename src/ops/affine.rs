use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::{element::AffineElement, Fr};

impl<'a, 'b> Add<&'b AffineElement> for &'a AffineElement {
    type Output = AffineElement;

    fn add(self, other: &'b AffineElement) -> AffineElement {
        AffineElement {
            inner: self.inner + other.inner,
        }
    }
}

impl<'b> Add<&'b AffineElement> for AffineElement {
    type Output = AffineElement;
    fn add(self, other: &'b AffineElement) -> AffineElement {
        &self + other
    }
}

impl<'a> Add<AffineElement> for &'a AffineElement {
    type Output = AffineElement;
    fn add(self, other: AffineElement) -> AffineElement {
        self + &other
    }
}

impl Add<AffineElement> for AffineElement {
    type Output = AffineElement;
    fn add(self, other: AffineElement) -> AffineElement {
        &self + &other
    }
}

impl<'b> AddAssign<&'b AffineElement> for AffineElement {
    fn add_assign(&mut self, other: &'b AffineElement) {
        *self = AffineElement {
            inner: self.inner + other.inner,
        }
    }
}

impl AddAssign<AffineElement> for AffineElement {
    fn add_assign(&mut self, other: AffineElement) {
        *self += &other;
    }
}

impl<'a, 'b> Sub<&'b AffineElement> for &'a AffineElement {
    type Output = AffineElement;

    fn sub(self, other: &'b AffineElement) -> AffineElement {
        AffineElement {
            inner: self.inner - other.inner,
        }
    }
}

impl<'b> Sub<&'b AffineElement> for AffineElement {
    type Output = AffineElement;

    fn sub(self, other: &'b AffineElement) -> AffineElement {
        &self - other
    }
}

impl<'a> Sub<AffineElement> for &'a AffineElement {
    type Output = AffineElement;

    fn sub(self, other: AffineElement) -> AffineElement {
        self - &other
    }
}

impl Sub<AffineElement> for AffineElement {
    type Output = AffineElement;

    fn sub(self, other: AffineElement) -> AffineElement {
        &self - &other
    }
}

impl<'b> SubAssign<&'b AffineElement> for AffineElement {
    fn sub_assign(&mut self, other: &'b AffineElement) {
        *self = AffineElement {
            inner: self.inner - other.inner,
        }
    }
}

impl SubAssign<AffineElement> for AffineElement {
    fn sub_assign(&mut self, other: AffineElement) {
        *self -= &other;
    }
}

impl Neg for AffineElement {
    type Output = Self;

    fn neg(self) -> Self {
        AffineElement { inner: -self.inner }
    }
}

impl<'b> MulAssign<&'b Fr> for AffineElement {
    fn mul_assign(&mut self, point: &'b Fr) {
        let mut p = self.inner;
        p *= *point;
        *self = AffineElement { inner: p }
    }
}

impl MulAssign<Fr> for AffineElement {
    fn mul_assign(&mut self, other: Fr) {
        *self *= &other;
    }
}

impl<'a, 'b> Mul<&'b Fr> for &'a AffineElement {
    type Output = AffineElement;

    fn mul(self, point: &'b Fr) -> AffineElement {
        let mut p = self.inner;
        p *= *point;
        AffineElement { inner: p }
    }
}

impl<'a, 'b> Mul<&'b AffineElement> for &'a Fr {
    type Output = AffineElement;

    fn mul(self, point: &'b AffineElement) -> AffineElement {
        point * self
    }
}

impl<'b> Mul<&'b Fr> for AffineElement {
    type Output = AffineElement;

    fn mul(self, other: &'b Fr) -> AffineElement {
        &self * other
    }
}

impl<'a> Mul<Fr> for &'a AffineElement {
    type Output = AffineElement;

    fn mul(self, other: Fr) -> AffineElement {
        self * &other
    }
}

impl Mul<Fr> for AffineElement {
    type Output = AffineElement;

    fn mul(self, other: Fr) -> AffineElement {
        &self * &other
    }
}

impl<'b> Mul<&'b AffineElement> for Fr {
    type Output = AffineElement;

    fn mul(self, other: &'b AffineElement) -> AffineElement {
        &self * other
    }
}

impl<'a> Mul<AffineElement> for &'a Fr {
    type Output = AffineElement;

    fn mul(self, other: AffineElement) -> AffineElement {
        self * &other
    }
}

impl Mul<AffineElement> for Fr {
    type Output = AffineElement;

    fn mul(self, other: AffineElement) -> AffineElement {
        &self * &other
    }
}
