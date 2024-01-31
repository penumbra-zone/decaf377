use core::ops::{Add, Neg};
use subtle::{Choice, ConditionallySelectable};

use crate::{min_curve::constants::*, min_curve::encoding::Encoding, sign::Sign, Fq};

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

    /// Construct a new element from the projective coordinates, checking on curve.
    fn new_checked(x: Fq, y: Fq, z: Fq, t: Fq) -> Option<Self> {
        let XX = x.square();
        let YY = y.square();
        let ZZ = z.square();
        let TT = t.square();

        let on_curve = (YY + COEFF_A * XX) == (ZZ + COEFF_D * TT);
        if on_curve {
            Some(Self { x, y, z, t })
        } else {
            None
        }
    }

    fn from_affine(x: Fq, y: Fq) -> Self {
        let z = Fq::one();
        let t = x * y;
        Self::new(x, y, z, t)
    }

    fn new(x: Fq, y: Fq, z: Fq, t: Fq) -> Self {
        if cfg!(debug_assertions) {
            Element::new_checked(x, y, z, t).expect("decompression should be on curve")
        } else {
            Element { x, y, z, t }
        }
    }

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
        Self::new(x3, y3, z3, t3)
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

    /// Elligator 2 map to decaf377 point
    fn elligator_map(r_0: &Fq) -> Self {
        // Ref: `Decaf_1_1_Point.elligator` (optimized) in `ristretto.sage`
        const A: Fq = COEFF_A;
        const D: Fq = COEFF_D;

        let r = ZETA * r_0.square();

        let den = (D * r - (D - A)) * ((D - A) * r - D);
        let num = (r + Fq::one()) * (A - (Fq::one() + Fq::one()) * D);

        let x = num * den;
        let (iss, mut isri) = Fq::non_arkworks_sqrt_ratio_zeta(&Fq::one(), &x);

        let sgn;
        let twiddle;
        if iss {
            sgn = Fq::one();
            twiddle = Fq::one();
        } else {
            sgn = -(Fq::one());
            twiddle = *r_0;
        }

        isri *= twiddle;

        let mut s = isri * num;
        let t = -(sgn) * isri * s * (r - Fq::one()) * (A - (Fq::one() + Fq::one()) * D).square()
            - Fq::one();

        if s.is_negative() == iss {
            s = -s
        }

        // Convert point to extended projective (X : Y : Z : T)
        let E = (Fq::one() + Fq::one()) * s;
        let F = Fq::one() + A * s.square();
        let G = Fq::one() - A * s.square();
        let H = t;

        Self::new(E * H, F * G, F * H, E * G)
    }

    /// Maps two field elements to a uniformly distributed decaf377 `Element`.
    ///
    /// The two field elements provided as inputs should be independently chosen.
    pub fn hash_to_curve(r_1: &Fq, r_2: &Fq) -> Element {
        let R_1 = Element::elligator_map(r_1);
        let R_2 = Element::elligator_map(r_2);
        &R_1 + &R_2
    }

    /// Maps a field element to a decaf377 `Element` suitable for CDH challenges.
    pub fn encode_to_curve(r: &Fq) -> Element {
        Element::elligator_map(r)
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
        let (was_square, mut v) =
            Fq::non_arkworks_sqrt_ratio_zeta(&Fq::one(), &(u_2 * u_1.square()));
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

        Ok(Element::new(x, y, z, t))
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
        Self::new(x3, y3, z3, t3)
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

    proptest! {
        #[test]
        fn group_encoding_round_trip_if_successful(bytes: [u8; 32]) {
            let bytes = Encoding(bytes);

            if let Ok(element) = bytes.vartime_decompress() {
                let bytes2 = element.vartime_compress();
                assert_eq!(bytes, bytes2);
            }
        }
    }

    #[test]
    fn test_elligator() {
        // These are the test cases from testElligatorDeterministic in ristretto.sage
        let inputs = [
            [
                221, 101, 215, 58, 170, 229, 36, 124, 172, 234, 94, 214, 186, 163, 242, 30, 65,
                123, 76, 74, 56, 60, 24, 213, 240, 137, 49, 189, 138, 39, 90, 6,
            ],
            [
                23, 203, 214, 51, 26, 149, 7, 160, 228, 239, 208, 147, 124, 109, 75, 72, 64, 16,
                64, 215, 53, 185, 249, 168, 188, 49, 22, 194, 118, 7, 242, 16,
            ],
            [
                177, 123, 90, 180, 115, 7, 108, 183, 161, 167, 24, 15, 248, 218, 206, 227, 76, 137,
                162, 187, 148, 174, 66, 44, 205, 1, 211, 91, 140, 50, 144, 1,
            ],
            [
                204, 225, 121, 228, 145, 30, 86, 208, 132, 242, 203, 9, 153, 90, 195, 150, 215, 49,
                166, 70, 78, 68, 47, 98, 30, 130, 115, 139, 168, 242, 238, 8,
            ],
            [
                59, 150, 40, 159, 229, 96, 201, 47, 170, 163, 9, 208, 205, 201, 112, 241, 179, 82,
                198, 79, 207, 160, 184, 245, 63, 189, 101, 115, 217, 228, 74, 13,
            ],
            [
                74, 159, 227, 190, 73, 213, 131, 200, 50, 102, 249, 230, 48, 103, 85, 168, 239,
                149, 7, 164, 12, 42, 217, 177, 189, 97, 214, 98, 102, 73, 10, 16,
            ],
            [
                183, 227, 227, 192, 119, 10, 155, 143, 64, 60, 249, 165, 240, 39, 31, 197, 159,
                121, 64, 82, 10, 1, 34, 35, 121, 34, 146, 69, 226, 196, 156, 14,
            ],
            [
                61, 21, 56, 224, 11, 181, 71, 186, 238, 126, 234, 240, 14, 168, 75, 73, 251, 111,
                175, 85, 108, 9, 77, 2, 88, 249, 24, 235, 53, 96, 51, 15,
            ],
        ];

        let expected_xy_coordinates = [
            [
                ark_ff::MontFp!(
                    "1267955849280145133999011095767946180059440909377398529682813961428156596086"
                ),
                ark_ff::MontFp!(
                    "5356565093348124788258444273601808083900527100008973995409157974880178412098"
                ),
            ],
            [
                ark_ff::MontFp!(
                    "1502379126429822955521756759528876454108853047288874182661923263559139887582"
                ),
                ark_ff::MontFp!(
                    "7074060208122316523843780248565740332109149189893811936352820920606931717751"
                ),
            ],
            [
                ark_ff::MontFp!(
                    "2943006201157313879823661217587757631000260143892726691725524748591717287835"
                ),
                ark_ff::MontFp!(
                    "4988568968545687084099497807398918406354768651099165603393269329811556860241"
                ),
            ],
            [
                ark_ff::MontFp!(
                    "2893226299356126359042735859950249532894422276065676168505232431940642875576"
                ),
                ark_ff::MontFp!(
                    "5540423804567408742733533031617546054084724133604190833318816134173899774745"
                ),
            ],
            [
                ark_ff::MontFp!(
                    "2950911977149336430054248283274523588551527495862004038190631992225597951816"
                ),
                ark_ff::MontFp!(
                    "4487595759841081228081250163499667279979722963517149877172642608282938805393"
                ),
            ],
            [
                ark_ff::MontFp!(
                    "3318574188155535806336376903248065799756521242795466350457330678746659358665"
                ),
                ark_ff::MontFp!(
                    "7706453242502782485686954136003233626318476373744684895503194201695334921001"
                ),
            ],
            [
                ark_ff::MontFp!(
                    "3753408652523927772367064460787503971543824818235418436841486337042861871179"
                ),
                ark_ff::MontFp!(
                    "2820605049615187268236268737743168629279853653807906481532750947771625104256"
                ),
            ],
            [
                ark_ff::MontFp!(
                    "7803875556376973796629423752730968724982795310878526731231718944925551226171"
                ),
                ark_ff::MontFp!(
                    "7033839813997913565841973681083930410776455889380940679209912201081069572111"
                ),
            ],
        ];

        use ark_serialize::CanonicalDeserialize;

        for (ind, input) in inputs.iter().enumerate() {
            let input_element =
                Fq::deserialize_compressed(&input[..]).expect("encoding of test vector is valid");

            let expected: Element = crate::min_curve::element::Element::from_affine(
                crate::constants::from_ark_fq(expected_xy_coordinates[ind][0]),
                crate::constants::from_ark_fq(expected_xy_coordinates[ind][1]),
            );

            let actual = Element::elligator_map(&input_element);

            assert_eq!(actual, expected);
        }
    }
}
