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
    x: Fq,
    y: Fq,
    t: Fq,
    z: Fq,
}
