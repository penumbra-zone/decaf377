use crate::Fq;

/// A point on an Edwards curve.
///
/// There exist points which do not correspond to elements of the Decaf377 group.
///
/// This curve can be equipped with an additive group structure.
///
/// This is an internal implementation detail of how we've constructed this group, and should
/// only be used by consumers who are cursed with the knowledge of what an Elliptic Curve is.
#[derive(Debug, Clone, Copy)]
pub struct AffinePoint {
    x: Fq,
    y: Fq,
}

impl AffinePoint {
    /// The identity element for the group structure.
    const IDENTITY: Self = Self {
        x: Fq::zero(),
        y: Fq::one(),
    };
}

/// An element of the Decaf377 group.
#[derive(Debug, Clone, Copy)]
pub struct Element {
    // These elements always satisfy the invariant that (x/z) * (y/z) = t.
    // Furthermore, ((x/z), (y/z)) returns the affine point associated with this element.
    x: Fq,
    y: Fq,
    z: Fq,
    t: Fq,
}

impl Element {
    /// The identity element for the group structure.
    pub const IDENTITY: Self = Self {
        x: Fq::zero(),
        y: Fq::one(),
        z: Fq::one(),
        t: Fq::zero(),
    };

    /// The generator element for the group structure.
    pub const GENERATOR: Self = Self {
        x: Fq::from_montgomery_limbs_64([
            5825153684096051627,
            16988948339439369204,
            186539475124256708,
            1230075515893193738,
        ]),
        y: Fq::from_montgomery_limbs_64([
            9786171649960077610,
            13527783345193426398,
            10983305067350511165,
            1251302644532346138,
        ]),
        z: Fq::one(),
        t: Fq::from_montgomery_limbs_64([
            7466800842436274004,
            14314110021432015475,
            14108125795146788134,
            1305086759679105397,
        ]),
    };
}

impl PartialEq for Element {
    fn eq(&self, other: &Self) -> bool {
        // This check is equivalent to checking that the ratio of each affine point matches.
        // ((x1 / z1) / (y1 / z1)) == ((x2 / z2) / (y2 / z2)) <=> x1 * y2 == x2 * y1
        self.x * other.y == other.x * self.y
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_basic_equalities() {
        assert_eq!(Element::GENERATOR, Element::GENERATOR);
        assert_eq!(Element::IDENTITY, Element::IDENTITY);
        assert_ne!(Element::IDENTITY, Element::GENERATOR);
    }
}
