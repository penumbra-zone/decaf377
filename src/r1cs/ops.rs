use std::ops::{Add, AddAssign, Sub, SubAssign};

use ark_ed_on_bls12_377::EdwardsProjective;

use crate::r1cs::gadget::Decaf377ElementVar;

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

// BELOW ARE NOT FOR MERGE. These are required for
// `GroupOpsBounds` but should not be done infallibly
// since we do not know the other `EdwardsProjective`
// is a valid decaf point.
impl Sub<EdwardsProjective> for Decaf377ElementVar {
    type Output = Decaf377ElementVar;

    fn sub(self, other: EdwardsProjective) -> Self::Output {
        Decaf377ElementVar {
            inner: self.inner.sub(other),
        }
    }
}

impl SubAssign<EdwardsProjective> for Decaf377ElementVar {
    fn sub_assign(&mut self, rhs: EdwardsProjective) {
        self.inner.sub_assign(rhs)
    }
}

impl Add<EdwardsProjective> for Decaf377ElementVar {
    type Output = Decaf377ElementVar;

    fn add(self, other: EdwardsProjective) -> Self::Output {
        Decaf377ElementVar {
            inner: self.inner.add(other),
        }
    }
}

impl AddAssign<EdwardsProjective> for Decaf377ElementVar {
    fn add_assign(&mut self, rhs: EdwardsProjective) {
        self.inner.add_assign(rhs)
    }
}
