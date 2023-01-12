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
        self.inner
            .element()
            .expect("element will exist")
            .add_assign(rhs.inner.element().expect("element will exist"));
    }
}

impl<'a> AddAssign<&'a ElementVar> for ElementVar {
    fn add_assign(&mut self, rhs: &'a ElementVar) {
        self.inner
            .element()
            .expect("element will exist")
            .add_assign(rhs.inner.element().expect("element will exist"));
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
        self.inner
            .element()
            .expect("element will exist")
            .sub_assign(rhs.inner.element().expect("element will exist"));
    }
}

impl<'a> SubAssign<&'a ElementVar> for ElementVar {
    fn sub_assign(&mut self, rhs: &'a ElementVar) {
        self.inner
            .element()
            .expect("element will exist")
            .sub_assign(rhs.inner.element().expect("element will exist"));
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
        self.inner
            .element()
            .expect("element will exist")
            .sub_assign(rhs)
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
        self.inner
            .element()
            .expect("element will exist")
            .add_assign(rhs)
    }
}
