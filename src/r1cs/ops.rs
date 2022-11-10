use std::ops::{Add, AddAssign, Sub, SubAssign};

use crate::{r1cs::gadget::ElementVar, Element};

impl Add for ElementVar {
    type Output = ElementVar;

    fn add(self, other: ElementVar) -> Self::Output {
        ElementVar {
            inner: self.inner.add(other.inner),
        }
    }
}

impl<'a> Add<&'a ElementVar> for ElementVar {
    type Output = ElementVar;

    fn add(self, other: &'a ElementVar) -> Self::Output {
        ElementVar {
            inner: self.inner.add(other.inner.clone()),
        }
    }
}

impl AddAssign for ElementVar {
    fn add_assign(&mut self, rhs: ElementVar) {
        self.inner.add_assign(rhs.inner)
    }
}

impl<'a> AddAssign<&'a ElementVar> for ElementVar {
    fn add_assign(&mut self, rhs: &'a ElementVar) {
        self.inner.add_assign(rhs.inner.clone())
    }
}

impl Sub for ElementVar {
    type Output = ElementVar;

    fn sub(self, other: ElementVar) -> Self::Output {
        ElementVar {
            inner: self.inner.sub(other.inner),
        }
    }
}

impl<'a> Sub<&'a ElementVar> for ElementVar {
    type Output = ElementVar;

    fn sub(self, other: &'a ElementVar) -> Self::Output {
        ElementVar {
            inner: self.inner.sub(other.inner.clone()),
        }
    }
}

impl SubAssign for ElementVar {
    fn sub_assign(&mut self, rhs: ElementVar) {
        self.inner.sub_assign(rhs.inner)
    }
}

impl<'a> SubAssign<&'a ElementVar> for ElementVar {
    fn sub_assign(&mut self, rhs: &'a ElementVar) {
        self.inner.sub_assign(rhs.inner.clone())
    }
}

impl Sub<Element> for ElementVar {
    type Output = ElementVar;

    fn sub(self, other: Element) -> Self::Output {
        ElementVar {
            inner: self.inner.sub(other.inner),
        }
    }
}

impl SubAssign<Element> for ElementVar {
    fn sub_assign(&mut self, rhs: Element) {
        self.inner.sub_assign(rhs.inner)
    }
}

impl Add<Element> for ElementVar {
    type Output = ElementVar;

    fn add(self, other: Element) -> Self::Output {
        ElementVar {
            inner: self.inner.add(other.inner),
        }
    }
}

impl AddAssign<Element> for ElementVar {
    fn add_assign(&mut self, rhs: Element) {
        self.inner.add_assign(rhs.inner)
    }
}
