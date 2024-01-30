use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::{min_curve::element::Element, Fr};

// Element addition

impl<'a, 'b> Add<&'b Element> for &'a Element {
    type Output = Element;

    fn add(self, other: &'b Element) -> Element {
        self + *other
    }
}

impl<'b> Add<&'b Element> for Element {
    type Output = Element;
    fn add(self, other: &'b Element) -> Element {
        self + *other
    }
}

impl<'a> Add<Element> for &'a Element {
    type Output = Element;
    fn add(self, other: Element) -> Element {
        *self + other
    }
}

impl<'b> AddAssign<&'b Element> for Element {
    fn add_assign(&mut self, other: &'b Element) {
        *self = *self + other
    }
}

impl AddAssign<Element> for Element {
    fn add_assign(&mut self, other: Element) {
        *self += &other;
    }
}

// Element subtraction

impl Sub<Element> for Element {
    type Output = Element;

    fn sub(self, other: Element) -> Element {
        self + other.neg()
    }
}

impl<'a, 'b> Sub<&'b Element> for &'a Element {
    type Output = Element;

    fn sub(self, other: &'b Element) -> Element {
        *self - *other
    }
}

impl<'b> Sub<&'b Element> for Element {
    type Output = Element;

    fn sub(self, other: &'b Element) -> Element {
        self - *other
    }
}

impl<'a> Sub<Element> for &'a Element {
    type Output = Element;

    fn sub(self, other: Element) -> Element {
        *self - other
    }
}

impl<'b> SubAssign<&'b Element> for Element {
    fn sub_assign(&mut self, other: &'b Element) {
        *self = *self - other;
    }
}

impl SubAssign<Element> for Element {
    fn sub_assign(&mut self, other: Element) {
        *self -= &other;
    }
}

/// Scalar multiplication

impl Mul<Fr> for Element {
    type Output = Self;

    fn mul(self, rhs: Fr) -> Self::Output {
        Self::scalar_mul_vartime(self, &rhs.to_le_limbs())
    }
}

impl<'b> MulAssign<&'b Fr> for Element {
    fn mul_assign(&mut self, rhs: &'b Fr) {
        *self = *self * rhs;
    }
}

impl MulAssign<Fr> for Element {
    fn mul_assign(&mut self, other: Fr) {
        *self *= &other;
    }
}

impl<'a, 'b> Mul<&'b Fr> for &'a Element {
    type Output = Element;

    fn mul(self, scalar: &'b Fr) -> Element {
        scalar * self
    }
}

impl<'a, 'b> Mul<&'b Element> for &'a Fr {
    type Output = Element;

    fn mul(self, point: &'b Element) -> Element {
        point * self
    }
}

impl<'b> Mul<&'b Fr> for Element {
    type Output = Self;

    fn mul(self, other: &'b Fr) -> Element {
        self * *other
    }
}

impl<'a> Mul<Fr> for &'a Element {
    type Output = Element;

    fn mul(self, other: Fr) -> Element {
        *self * other
    }
}

impl<'b> Mul<&'b Element> for Fr {
    type Output = Element;

    fn mul(self, other: &'b Element) -> Element {
        other * self
    }
}

impl<'a> Mul<Element> for &'a Fr {
    type Output = Element;

    fn mul(self, other: Element) -> Element {
        other * *self
    }
}

impl Mul<Element> for Fr {
    type Output = Element;

    fn mul(self, other: Element) -> Element {
        other * self
    }
}
