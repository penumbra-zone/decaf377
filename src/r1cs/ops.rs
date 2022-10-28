use std::ops::{Add, AddAssign, Sub, SubAssign};

use crate::r1cs::gadget::Decaf377ElementVar;

impl Add for Decaf377ElementVar {
    type Output = Decaf377ElementVar;

    fn add(self, other: Decaf377ElementVar) -> Self::Output {
        Decaf377ElementVar {
            inner: self.inner.add(other.inner),
        }
    }
}

impl AddAssign for Decaf377ElementVar {
    fn add_assign(&mut self, rhs: Decaf377ElementVar) {
        self.inner.add_assign(rhs.inner)
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

impl SubAssign for Decaf377ElementVar {
    fn sub_assign(&mut self, rhs: Decaf377ElementVar) {
        self.inner.sub_assign(rhs.inner)
    }
}
