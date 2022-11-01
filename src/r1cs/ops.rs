use std::ops::{Add, AddAssign, Sub, SubAssign};

use crate::{r1cs::gadget::Decaf377ElementVar, Element};

impl Add for Decaf377ElementVar {
    type Output = Decaf377ElementVar;

    fn add(self, other: Decaf377ElementVar) -> Self::Output {
        Decaf377ElementVar {
            inner: self.inner.add(other.inner),
        }
    }
}

impl<'a> Add<&'a Decaf377ElementVar> for Decaf377ElementVar {
    type Output = Decaf377ElementVar;

    fn add(self, other: &'a Decaf377ElementVar) -> Self::Output {
        Decaf377ElementVar {
            inner: self.inner.add(other.inner.clone()),
        }
    }
}

impl AddAssign for Decaf377ElementVar {
    fn add_assign(&mut self, rhs: Decaf377ElementVar) {
        self.inner.add_assign(rhs.inner)
    }
}

impl<'a> AddAssign<&'a Decaf377ElementVar> for Decaf377ElementVar {
    fn add_assign(&mut self, rhs: &'a Decaf377ElementVar) {
        self.inner.add_assign(rhs.inner.clone())
    }
}

impl Sub for Decaf377ElementVar {
    type Output = Decaf377ElementVar;

    fn sub(self, other: Decaf377ElementVar) -> Self::Output {
        Decaf377ElementVar {
            inner: self.inner.sub(other.inner),
        }
    }
}

impl<'a> Sub<&'a Decaf377ElementVar> for Decaf377ElementVar {
    type Output = Decaf377ElementVar;

    fn sub(self, other: &'a Decaf377ElementVar) -> Self::Output {
        Decaf377ElementVar {
            inner: self.inner.sub(other.inner.clone()),
        }
    }
}

impl SubAssign for Decaf377ElementVar {
    fn sub_assign(&mut self, rhs: Decaf377ElementVar) {
        self.inner.sub_assign(rhs.inner)
    }
}

impl<'a> SubAssign<&'a Decaf377ElementVar> for Decaf377ElementVar {
    fn sub_assign(&mut self, rhs: &'a Decaf377ElementVar) {
        self.inner.sub_assign(rhs.inner.clone())
    }
}

impl Sub<Element> for Decaf377ElementVar {
    type Output = Decaf377ElementVar;

    fn sub(self, other: Element) -> Self::Output {
        Decaf377ElementVar {
            inner: self.inner.sub(other.inner),
        }
    }
}

impl SubAssign<Element> for Decaf377ElementVar {
    fn sub_assign(&mut self, rhs: Element) {
        self.inner.sub_assign(rhs.inner)
    }
}

impl Add<Element> for Decaf377ElementVar {
    type Output = Decaf377ElementVar;

    fn add(self, other: Element) -> Self::Output {
        Decaf377ElementVar {
            inner: self.inner.add(other.inner),
        }
    }
}

impl AddAssign<Element> for Decaf377ElementVar {
    fn add_assign(&mut self, rhs: Element) {
        self.inner.add_assign(rhs.inner)
    }
}
