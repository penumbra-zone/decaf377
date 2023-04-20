use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::{Element, Fr};

impl<'a, 'b> Add<&'b Element> for &'a Element {
    type Output = Element;

    fn add(self, other: &'b Element) -> Element {
        Element {
            inner: self.inner + other.inner,
        }
    }
}

impl<'b> Add<&'b Element> for Element {
    type Output = Element;
    fn add(self, other: &'b Element) -> Element {
        &self + other
    }
}

impl<'a> Add<Element> for &'a Element {
    type Output = Element;
    fn add(self, other: Element) -> Element {
        self + &other
    }
}

impl Add<Element> for Element {
    type Output = Element;
    fn add(self, other: Element) -> Element {
        &self + &other
    }
}

impl<'b> AddAssign<&'b Element> for Element {
    fn add_assign(&mut self, other: &'b Element) {
        *self = Element {
            inner: self.inner + other.inner,
        }
    }
}

impl AddAssign<Element> for Element {
    fn add_assign(&mut self, other: Element) {
        *self += &other;
    }
}

impl<'a, 'b> Sub<&'b Element> for &'a Element {
    type Output = Element;

    fn sub(self, other: &'b Element) -> Element {
        Element {
            inner: self.inner - other.inner,
        }
    }
}

impl<'b> Sub<&'b Element> for Element {
    type Output = Element;

    fn sub(self, other: &'b Element) -> Element {
        &self - other
    }
}

impl<'a> Sub<Element> for &'a Element {
    type Output = Element;

    fn sub(self, other: Element) -> Element {
        self - &other
    }
}

impl Sub<Element> for Element {
    type Output = Element;

    fn sub(self, other: Element) -> Element {
        &self - &other
    }
}

impl<'b> SubAssign<&'b Element> for Element {
    fn sub_assign(&mut self, other: &'b Element) {
        *self = Element {
            inner: self.inner - other.inner,
        }
    }
}

impl SubAssign<Element> for Element {
    fn sub_assign(&mut self, other: Element) {
        *self -= &other;
    }
}

impl Neg for Element {
    type Output = Self;

    fn neg(self) -> Self {
        Element { inner: -self.inner }
    }
}

impl<'b> MulAssign<&'b Fr> for Element {
    // Scalar multiplication is performed through the implementation
    // of `MulAssign` on `EdwardsProjective` which is a type alias for
    // `GroupProjective<EdwardsConfig>`.
    fn mul_assign(&mut self, point: &'b Fr) {
        let mut p = self.inner;
        p *= *point;
        *self = Element { inner: p }
    }
}

impl MulAssign<Fr> for Element {
    fn mul_assign(&mut self, other: Fr) {
        *self *= &other;
    }
}

impl<'a, 'b> Mul<&'b Fr> for &'a Element {
    type Output = Element;

    fn mul(self, point: &'b Fr) -> Element {
        let mut p = self.inner;
        p *= *point;
        Element { inner: p }
    }
}

impl<'a, 'b> Mul<&'b Element> for &'a Fr {
    type Output = Element;

    fn mul(self, point: &'b Element) -> Element {
        point * self
    }
}

impl<'b> Mul<&'b Fr> for Element {
    type Output = Element;

    fn mul(self, other: &'b Fr) -> Element {
        &self * other
    }
}

impl<'a> Mul<Fr> for &'a Element {
    type Output = Element;

    fn mul(self, other: Fr) -> Element {
        self * &other
    }
}

impl Mul<Fr> for Element {
    type Output = Element;

    fn mul(self, other: Fr) -> Element {
        &self * &other
    }
}

impl<'b> Mul<&'b Element> for Fr {
    type Output = Element;

    fn mul(self, other: &'b Element) -> Element {
        &self * other
    }
}

impl<'a> Mul<Element> for &'a Fr {
    type Output = Element;

    fn mul(self, other: Element) -> Element {
        self * &other
    }
}

impl Mul<Element> for Fr {
    type Output = Element;

    fn mul(self, other: Element) -> Element {
        &self * &other
    }
}
