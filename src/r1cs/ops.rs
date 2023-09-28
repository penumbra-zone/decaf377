use std::ops::{Add, AddAssign, Sub, SubAssign};

use crate::{r1cs::element::ElementVar, Element};

use super::lazy::LazyElementVar;

impl Add for ElementVar {
    type Output = ElementVar;

    fn add(self, other: ElementVar) -> Self::Output {
        ElementVar {
            inner: LazyElementVar::new_from_element(
                self.inner
                    .element()
                    .expect("element will exist")
                    .add(other.inner.element().expect("element will exist")),
            ),
        }
    }
}

impl<'a> Add<&'a ElementVar> for ElementVar {
    type Output = ElementVar;

    fn add(self, other: &'a ElementVar) -> Self::Output {
        ElementVar {
            inner: LazyElementVar::new_from_element(
                self.inner
                    .element()
                    .expect("element will exist")
                    .add(other.inner.element().expect("element will exist")),
            ),
        }
    }
}

impl AddAssign for ElementVar {
    fn add_assign(&mut self, rhs: ElementVar) {
        let rhs = rhs.inner.element().expect("element will exist");
        let mut lhs = self.inner.element().expect("element will exist");
        lhs.add_assign(rhs);

        *self = ElementVar {
            inner: LazyElementVar::new_from_element(lhs),
        };
    }
}

impl<'a> AddAssign<&'a ElementVar> for ElementVar {
    fn add_assign(&mut self, rhs: &'a ElementVar) {
        let rhs = rhs.inner.element().expect("element will exist");
        let mut lhs = self.inner.element().expect("element will exist");
        lhs.add_assign(rhs);

        *self = ElementVar {
            inner: LazyElementVar::new_from_element(lhs),
        };
    }
}

impl Sub for ElementVar {
    type Output = ElementVar;

    fn sub(self, other: ElementVar) -> Self::Output {
        ElementVar {
            inner: LazyElementVar::new_from_element(
                self.inner
                    .element()
                    .expect("element will exist")
                    .sub(other.inner.element().expect("element will exist")),
            ),
        }
    }
}

impl<'a> Sub<&'a ElementVar> for ElementVar {
    type Output = ElementVar;

    fn sub(self, other: &'a ElementVar) -> Self::Output {
        ElementVar {
            inner: LazyElementVar::new_from_element(
                self.inner
                    .element()
                    .expect("element will exist")
                    .sub(other.inner.element().expect("element will exist")),
            ),
        }
    }
}

impl SubAssign for ElementVar {
    fn sub_assign(&mut self, rhs: ElementVar) {
        let rhs = rhs.inner.element().expect("element will exist");
        let mut lhs = self.inner.element().expect("element will exist");
        lhs.sub_assign(rhs);

        *self = ElementVar {
            inner: LazyElementVar::new_from_element(lhs),
        };
    }
}

impl<'a> SubAssign<&'a ElementVar> for ElementVar {
    fn sub_assign(&mut self, rhs: &'a ElementVar) {
        let rhs = rhs.inner.element().expect("element will exist");
        let mut lhs = self.inner.element().expect("element will exist");
        lhs.sub_assign(rhs);

        *self = ElementVar {
            inner: LazyElementVar::new_from_element(lhs),
        };
    }
}

impl Sub<Element> for ElementVar {
    type Output = ElementVar;

    fn sub(self, other: Element) -> Self::Output {
        ElementVar {
            inner: LazyElementVar::new_from_element(
                self.inner.element().expect("element will exist").sub(other),
            ),
        }
    }
}

impl SubAssign<Element> for ElementVar {
    fn sub_assign(&mut self, rhs: Element) {
        let mut lhs = self.inner.element().expect("element will exist");
        lhs.sub_assign(rhs);

        *self = ElementVar {
            inner: LazyElementVar::new_from_element(lhs),
        };
    }
}

impl Add<Element> for ElementVar {
    type Output = ElementVar;

    fn add(self, other: Element) -> Self::Output {
        ElementVar {
            inner: LazyElementVar::new_from_element(
                self.inner.element().expect("element will exist").add(other),
            ),
        }
    }
}

impl AddAssign<Element> for ElementVar {
    fn add_assign(&mut self, rhs: Element) {
        let mut lhs = self.inner.element().expect("element will exist");
        lhs.add_assign(rhs);

        *self = ElementVar {
            inner: LazyElementVar::new_from_element(lhs),
        };
    }
}
