use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use ark_ec::twisted_edwards::Projective;

use crate::{
    ark_curve::element::AffinePoint, ark_curve::Decaf377EdwardsConfig, ark_curve::Element, Fr,
};

impl<'a, 'b> Add<&'b AffinePoint> for &'a AffinePoint {
    type Output = AffinePoint;

    fn add(self, other: &'b AffinePoint) -> AffinePoint {
        AffinePoint {
            inner: (self.inner + other.inner).into(),
        }
    }
}

impl<'b> Add<&'b AffinePoint> for AffinePoint {
    type Output = Element;

    fn add(self, other: &'b AffinePoint) -> Element {
        (&self + other).into()
    }
}

impl<'a> Add<AffinePoint> for &'a AffinePoint {
    type Output = AffinePoint;
    fn add(self, other: AffinePoint) -> AffinePoint {
        self + &other
    }
}

impl<'b> AddAssign<&'b AffinePoint> for AffinePoint {
    fn add_assign(&mut self, other: &'b AffinePoint) {
        *self = AffinePoint {
            inner: (self.inner + other.inner).into(),
        }
    }
}

impl AddAssign<AffinePoint> for AffinePoint {
    fn add_assign(&mut self, other: AffinePoint) {
        *self += &other;
    }
}

impl<'a, 'b> Sub<&'b AffinePoint> for &'a AffinePoint {
    type Output = AffinePoint;

    fn sub(self, other: &'b AffinePoint) -> AffinePoint {
        AffinePoint {
            inner: (self.inner - other.inner).into(),
        }
    }
}

impl<'b> Sub<&'b AffinePoint> for AffinePoint {
    type Output = Element;

    fn sub(self, other: &'b AffinePoint) -> Element {
        (&self - other).into()
    }
}

impl<'a> Sub<AffinePoint> for &'a AffinePoint {
    type Output = AffinePoint;

    fn sub(self, other: AffinePoint) -> AffinePoint {
        self - &other
    }
}

impl Sub<AffinePoint> for AffinePoint {
    type Output = Element;

    fn sub(self, other: AffinePoint) -> Element {
        (&self - &other).into()
    }
}

impl<'a, 'b> Sub<&'b Element> for &'a AffinePoint {
    type Output = Element;

    fn sub(self, other: &'b Element) -> Element {
        Element {
            inner: self.inner - other.inner,
        }
    }
}

impl<'b> Sub<&'b Element> for AffinePoint {
    type Output = Element;

    fn sub(self, other: &'b Element) -> Element {
        &self - other
    }
}

impl<'a> Sub<Element> for &'a AffinePoint {
    type Output = Element;

    fn sub(self, other: Element) -> Element {
        self - &other
    }
}

impl Sub<Element> for AffinePoint {
    type Output = Element;

    fn sub(self, other: Element) -> Element {
        &self - &other
    }
}

impl<'b> SubAssign<&'b AffinePoint> for AffinePoint {
    fn sub_assign(&mut self, other: &'b AffinePoint) {
        *self = AffinePoint {
            inner: (self.inner - other.inner).into(),
        }
    }
}

impl SubAssign<AffinePoint> for AffinePoint {
    fn sub_assign(&mut self, other: AffinePoint) {
        *self -= &other;
    }
}

impl Neg for AffinePoint {
    type Output = Self;

    fn neg(self) -> Self {
        AffinePoint { inner: -self.inner }
    }
}

impl<'b> MulAssign<&'b Fr> for AffinePoint {
    fn mul_assign(&mut self, point: &'b Fr) {
        let mut p: Projective<Decaf377EdwardsConfig> = self.inner.into();
        p *= *point;
        *self = AffinePoint { inner: p.into() }
    }
}

impl MulAssign<Fr> for AffinePoint {
    fn mul_assign(&mut self, other: Fr) {
        *self *= &other;
    }
}

impl<'a, 'b> Mul<&'b Fr> for &'a AffinePoint {
    type Output = AffinePoint;

    fn mul(self, point: &'b Fr) -> AffinePoint {
        let mut p: Projective<Decaf377EdwardsConfig> = self.inner.into();
        p *= *point;
        AffinePoint { inner: p.into() }
    }
}

impl<'a, 'b> Mul<&'b AffinePoint> for &'a Fr {
    type Output = AffinePoint;

    fn mul(self, point: &'b AffinePoint) -> AffinePoint {
        point * self
    }
}

impl<'b> Mul<&'b Fr> for AffinePoint {
    type Output = Element;

    fn mul(self, other: &'b Fr) -> Element {
        (&self * other).into()
    }
}

impl<'a> Mul<Fr> for &'a AffinePoint {
    type Output = AffinePoint;

    fn mul(self, other: Fr) -> AffinePoint {
        self * &other
    }
}

impl Mul<Fr> for AffinePoint {
    type Output = Element;

    fn mul(self, other: Fr) -> Element {
        (&self * &other).into()
    }
}

impl<'b> Mul<&'b AffinePoint> for Fr {
    type Output = AffinePoint;

    fn mul(self, other: &'b AffinePoint) -> AffinePoint {
        &self * other
    }
}

impl<'a> Mul<AffinePoint> for &'a Fr {
    type Output = AffinePoint;

    fn mul(self, other: AffinePoint) -> AffinePoint {
        self * &other
    }
}

impl Mul<AffinePoint> for Fr {
    type Output = AffinePoint;

    fn mul(self, other: AffinePoint) -> AffinePoint {
        &self * &other
    }
}
