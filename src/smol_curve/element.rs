use core::ops::{Add, Mul};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

use crate::{Fq, Fr};

/// COEFF_A = -1
const COEFF_A: Fq = Fq::from_montgomery_limbs_64([
    10157024534604021774,
    16668528035959406606,
    5322190058819395602,
    387181115924875961,
]);

/// COEFF_D = 3021
const COEFF_D: Fq = Fq::from_montgomery_limbs_64([
    15008245758212136496,
    17341409599856531410,
    648869460136961410,
    719771289660577536,
]);

/// -2 COEFF_D / COEFF_A = 6042
const COEFF_K: Fq = Fq::from_montgomery_limbs_64([
    10844245690243005535,
    9774967673803681700,
    12776203677742963460,
    94262208632981673,
]);

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
    pub const IDENTITY: Self = Self {
        x: Fq::zero(),
        y: Fq::one(),
    };
}

/// An element of the Decaf377 group.
#[derive(Debug, Clone, Copy)]
pub struct Element {
    // These elements always satisfy the invariant that x * y = t * z.
    // Furthermore, ((x/z), (y/z)) returns the affine point associated with this element.
    x: Fq,
    y: Fq,
    z: Fq,
    t: Fq,
}

impl ConditionallySelectable for Element {
    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        Self {
            x: Fq::conditional_select(&a.x, &b.x, choice),
            y: Fq::conditional_select(&a.y, &b.y, choice),
            z: Fq::conditional_select(&a.z, &b.z, choice),
            t: Fq::conditional_select(&a.t, &b.t, choice),
        }
    }
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

    pub fn double(self) -> Self {
        // https://eprint.iacr.org/2008/522 Section 3.3
        let a = self.x.square();
        let b = self.y.square();
        let mut c = self.z.square();
        c += c;
        // Since COEFF_A is -1
        let d = -a;
        let e = (self.x + self.y).square() - a - b;
        let g = d + b;
        let f = g - c;
        let h = d - b;
        let x3 = e * f;
        let y3 = g * h;
        let t3 = e * h;
        let z3 = f * g;
        Self {
            x: x3,
            y: y3,
            z: z3,
            t: t3,
        }
    }

    fn scalar_mul_both<const CT: bool>(self, le_bits: &[u64]) -> Self {
        let mut acc = Self::IDENTITY;
        let mut insert = self;
        for limb in le_bits {
            for i in 0..64 {
                let flag = ((limb >> i) & 1) as u8;
                if CT {
                    acc = Self::conditional_select(&acc, &(acc + insert), Choice::from(flag))
                } else if flag == 1 {
                    acc = acc + insert;
                }
                insert = insert.double();
            }
        }
        acc
    }

    pub fn scalar_mul_vartime(self, le_bits: &[u64]) -> Self {
        Self::scalar_mul_both::<false>(self, le_bits)
    }

    pub fn scalar_mul(self, le_bits: &[u64]) -> Self {
        Self::scalar_mul_both::<true>(self, le_bits)
    }
}

impl Add for Element {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        // https://eprint.iacr.org/2008/522 Section 3.1, 8M + 1D algorithm
        let Element {
            x: x1,
            y: y1,
            z: z1,
            t: t1,
        } = self;
        let Element {
            x: x2,
            y: y2,
            z: z2,
            t: t2,
        } = other;
        let a = (y1 - x1) * (y2 - x2);
        let b = (y1 + x1) * (y2 + x2);
        let c = COEFF_K * t1 * t2;
        let d = (z1 + z1) * z2;
        let e = b - a;
        let f = d - c;
        let g = d + c;
        let h = b + a;
        let x3 = e * f;
        let y3 = g * h;
        let t3 = e * h;
        let z3 = f * g;
        Self {
            x: x3,
            y: y3,
            z: z3,
            t: t3,
        }
    }
}

impl Mul<Fr> for Element {
    type Output = Self;

    fn mul(self, rhs: Fr) -> Self::Output {
        Self::scalar_mul_vartime(self, &rhs.to_le_limbs())
    }
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

    #[test]
    fn test_adding_is_doubling_on_generator() {
        assert_eq!(
            Element::GENERATOR + Element::GENERATOR,
            Element::GENERATOR.double()
        );
    }

    #[test]
    fn test_g_times_one() {
        assert_eq!(Element::GENERATOR * Fr::one(), Element::GENERATOR);
    }

    #[test]
    fn test_g_times_zero() {
        assert_eq!(Element::GENERATOR * Fr::zero(), Element::IDENTITY);
    }
}

#[cfg(all(test, feature = "arkworks"))]
mod proptests {
    use super::*;
    use ark_ff::{BigInt, PrimeField};
    use proptest::prelude::*;

    prop_compose! {
        // Technically this might overflow, but we won't miss any values,
        // just return 0 if you overflow when consuming.
        fn arb_fr_limbs()(
            z0 in 0..u64::MAX,
            z1 in 0..u64::MAX,
            z2 in 0..u64::MAX,
            z3 in 0..336320092672043349u64
        ) -> [u64; 4] {
            [z0, z1, z2, z3]
        }
    }

    prop_compose! {
        fn arb_fr()(a in arb_fr_limbs()) -> Fr {
            // Will be fine because of the bounds in the arb_fr_limbs
            Fr::from_bigint(BigInt(a)).unwrap_or(Fr::zero())
        }
    }

    proptest! {
        fn test_is_fq_module(a in arb_fr(), b in arb_fr()) {
            const G: Element = Element::GENERATOR;

            assert_eq!(G * (a + b), G * a + G * b);
            assert_eq!(G * (a * b), (G * a) * b);
        }
    }
}
