use core::ops::{Add, Neg};
use subtle::{Choice, ConditionallySelectable};

use crate::{
    on_curve::OnCurve, sign::Sign, smol_curve::constants::*, smol_curve::encoding::Encoding, Fq,
};

/// Error type for decompression
pub enum EncodingError {
    InvalidEncoding,
}

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

    pub fn vartime_compress_to_field(&self) -> Fq {
        let A_MINUS_D = COEFF_A - COEFF_D;

        // 1.
        let u_1 = (self.x + self.t) * (self.x - self.t);

        // 2.
        let (_always_square, v) =
            Fq::non_arkworks_sqrt_ratio_zeta(&Fq::one(), &(u_1 * A_MINUS_D * self.x.square()));

        // 3.
        let u_2 = (v * u_1).abs();

        // 4.
        let u_3 = u_2 * self.z - self.t;

        // 5.
        (A_MINUS_D * v * u_3 * self.x).abs()
    }

    pub fn vartime_compress(&self) -> Encoding {
        let s = self.vartime_compress_to_field();
        let bytes = s.to_bytes_le();
        Encoding(bytes)
    }
}

impl Encoding {
    pub fn vartime_decompress(&self) -> Result<Element, EncodingError> {
        // Top three bits of last byte must be zero
        if self.0[31] >> 5 != 0u8 {
            return Err(EncodingError::InvalidEncoding);
        }

        // 1/2. Reject unless s is canonically encoded and nonnegative.
        // Check bytes correspond to valid field element (i.e. less than field modulus)
        let s = Fq::from_bytes_checked(&self.0).ok_or(EncodingError::InvalidEncoding)?;
        if s.is_negative() {
            return Err(EncodingError::InvalidEncoding);
        }

        // 3. u_1 <- 1 - s^2
        let ss = s.square();
        let u_1 = Fq::one() - ss;

        // 4. u_2 <- u_1^2 - 4d s^2
        let u_2 = u_1.square() - (Fq::from(4u32) * COEFF_D) * ss;

        // 5. sqrt
        let (was_square, mut v) = Fq::sqrt_ratio_zeta(&Fq::one(), &(u_2 * u_1.square()));
        if !was_square {
            return Err(EncodingError::InvalidEncoding);
        }

        // 6. sign check
        let two_s_u_1 = (Fq::one() + Fq::one()) * s * u_1;
        let check = two_s_u_1 * v;
        if check.is_negative() {
            v = -v;
        }

        // 7. coordinates
        let x = two_s_u_1 * v.square() * u_2;
        let y = (Fq::one() + ss) * v * u_1;
        let z = Fq::one();
        let t = x * y;

        let element = Element { x, y, z, t };
        debug_assert!(
            element.is_on_curve(),
            "resulting point must be on the curve",
        );

        Ok(Element { x, y, z, t })
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

impl Neg for Element {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        self.x = -self.x;
        self.t = -self.t;
        self
    }
}

impl PartialEq for Element {
    fn eq(&self, other: &Self) -> bool {
        // This check is equivalent to checking that the ratio of each affine point matches.
        // ((x1 / z1) / (y1 / z1)) == ((x2 / z2) / (y2 / z2)) <=> x1 * y2 == x2 * y1
        self.x * other.y == other.x * self.y
    }
}

impl OnCurve for Element {
    fn is_on_curve(&self) -> bool {
        let XX = self.x.square();
        let YY = self.y.square();
        let ZZ = self.z.square();
        let TT = self.t.square();

        let on_curve = (YY + COEFF_A * XX) == (ZZ + COEFF_D * TT);

        // TODO: Add other checks
        on_curve
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::Fr;

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

    #[test]
    fn test_g_times_minus_one() {
        assert_eq!(Element::GENERATOR * (-Fr::one()), -Element::GENERATOR);
    }

    #[test]
    fn test_g_plus_minus_g() {
        assert_eq!(
            Element::GENERATOR + (-Element::GENERATOR),
            Element::IDENTITY
        );
    }

    #[test]
    fn test_g_minus_g() {
        let generator = Element::GENERATOR;
        assert_eq!(generator - generator, Element::IDENTITY);
    }
}

#[cfg(all(test, feature = "arkworks"))]
mod proptests {
    use super::*;
    use ark_ff::{BigInt, PrimeField};
    use proptest::prelude::*;

    use crate::Fr;

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
