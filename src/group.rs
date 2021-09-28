use core::ops::Neg;
use core::ops::{Add, AddAssign};
use core::ops::{Mul, MulAssign};
use core::ops::{Sub, SubAssign};
use std::convert::{TryFrom, TryInto};

use ark_ec::models::twisted_edwards_extended::GroupProjective;
use ark_ec::models::TEModelParameters;
use ark_ed_on_bls12_377::{EdwardsAffine, EdwardsParameters, EdwardsProjective, Fq};
use ark_ff::{Field, One, SquareRootField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

use zeroize::Zeroize;

use crate::constants::{ONE, TWO, ZETA};
use crate::{
    arkworks_ext::XSqrt, invsqrt::SqrtRatioZeta, scalar::Scalar, sign::Sign, EncodingError,
};

trait OnCurve {
    fn is_on_curve(&self) -> bool;
}

impl<P: TEModelParameters> OnCurve for GroupProjective<P> {
    #[allow(non_snake_case)]
    fn is_on_curve(&self) -> bool {
        let XX = self.x.square();
        let YY = self.y.square();
        let ZZ = self.z.square();
        let TT = self.t.square();

        let on_curve = (YY + P::COEFF_A * XX) == (ZZ + P::COEFF_D * TT);
        let on_segre_embedding = self.t * self.z == self.x * self.y;

        on_curve && on_segre_embedding
    }
}

#[derive(Copy, Clone, Default, Eq, PartialEq, Debug)]
pub struct Encoding(pub [u8; 32]);

#[derive(Copy, Clone, Debug)]
pub struct Element {
    inner: EdwardsProjective,
}

impl From<EdwardsAffine> for Element {
    fn from(point: EdwardsAffine) -> Self {
        Element {
            inner: point.into(),
        }
    }
}

impl Default for Element {
    fn default() -> Self {
        Element {
            inner: EdwardsProjective::zero(),
        }
    }
}

impl PartialEq for Element {
    fn eq(&self, other: &Element) -> bool {
        self.inner.x * other.inner.y == self.inner.y * other.inner.x
    }
}

impl Eq for Element {}

impl Zeroize for Element {
    fn zeroize(&mut self) {
        self.inner.zeroize()
    }
}

impl Element {
    pub fn basepoint() -> Element {
        let mut bytes = [0u8; 32];
        bytes[0] = 8;

        Encoding(bytes)
            .decompress()
            .expect("hardcoded basepoint bytes are valid")
    }

    #[allow(non_snake_case)]
    pub fn compress(&self) -> Encoding {
        // This isn't a constant, only because traits don't have const methods
        // yet and subtraction is only implemented as part of the Sub trait.
        let A_MINUS_D = EdwardsParameters::COEFF_A - EdwardsParameters::COEFF_D;
        let p = &self.inner;

        // 1.
        let u_1 = (p.x + p.t) * (p.x - p.t);

        // 2. division by 0 occurs on the identity point, but since
        // sqrt_ratio_zeta outputs v=0 it computes the right encoding anyway
        let (_always_square, v) =
            Fq::sqrt_ratio_zeta(&Fq::one(), &(u_1 * A_MINUS_D * p.x.square()));

        // 3.
        let u_2 = (v * u_1).abs();

        // 4.
        let u_3 = u_2 * p.z - p.t;

        // 5.
        let s = (A_MINUS_D * v * u_3 * p.x).abs();

        // Encode.
        let mut bytes = [0u8; 32];
        debug_assert_eq!(s.serialized_size(), 32);
        s.serialize(&mut bytes[..])
            .expect("serialization into array should be infallible");

        Encoding(bytes)
    }

    /// Create a decaf377 point (X : Y : Z : T) from its Jacobi Quartic representation (s, t)
    fn from_jacobi_quartic(
        s: ark_ed_on_bls12_377::Fq,
        t: ark_ed_on_bls12_377::Fq,
        sgn: ark_ed_on_bls12_377::Fq,
    ) -> Element {
        if s == Fq::zero() {
            return Element::default();
        }

        let x = *TWO * s / (*ONE + EdwardsParameters::COEFF_A * s.square());
        let y = (*ONE - EdwardsParameters::COEFF_A * s.square()) / t;

        EdwardsAffine::new(x, sgn * y).into()
    }

    /// Elligator map to decaf377 point
    #[allow(non_snake_case)]
    fn elligator_map(r_0: &ark_ed_on_bls12_377::Fq) -> Element {
        // Ref: `Decaf_1_1_Point.elligatorSpec` in `ristretto.sage`
        let A = EdwardsParameters::COEFF_A;
        let D = EdwardsParameters::COEFF_D;

        let r = *ZETA * r_0.square();
        let den = (D * r - (D - A)) * ((D - A) * r - D);
        if den == Fq::zero() {
            return Element::default();
        }

        let n1 = (r + *ONE) * (A - *TWO * D) / den;
        let n2 = r * n1;

        let mut sgn = *ONE;
        let s;
        let t;

        match n1.xsqrt() {
            Some(n1_root) => {
                s = n1_root;
                t = -(r - *ONE) * (A - *TWO * D).square() / den - *ONE;
            }
            None => {
                sgn = -*ONE;
                s = -(n2.sqrt().expect("n2 sqrt not found!"));
                t = r * (r - *ONE) * (A - *TWO * D).square() / den - *ONE;
            }
        }

        let result = Element::from_jacobi_quartic(s, t, sgn);

        debug_assert!(
            result.inner.is_on_curve(),
            "resulting point must be on the curve",
        );

        result
    }

    /// Maps two field elements to a uniformly distributed decaf377 `Element`.
    ///
    /// The two field elements provided as inputs should be independently chosen.
    #[allow(non_snake_case)]
    pub fn map_to_group_uniform(
        r_1: &ark_ed_on_bls12_377::Fq,
        r_2: &ark_ed_on_bls12_377::Fq,
    ) -> Element {
        let R_1 = Element::elligator_map(&r_1);
        let R_2 = Element::elligator_map(&r_2);
        let result = &R_1 + &R_2;

        debug_assert!(
            result.inner.is_on_curve(),
            "resulting point must be on the curve",
        );

        result
    }

    /// Maps a field element to a decaf377 `Element` suitable for CDH challenges.
    #[allow(non_snake_case)]
    pub fn map_to_group_cdh(r: &ark_ed_on_bls12_377::Fq) -> Element {
        let R = Element::elligator_map(&r);

        debug_assert!(
            R.inner.is_on_curve(),
            "resulting point must be on the curve",
        );

        R
    }
}

impl From<&Element> for Encoding {
    fn from(point: &Element) -> Self {
        point.compress()
    }
}

impl From<Element> for Encoding {
    fn from(point: Element) -> Self {
        point.compress()
    }
}

impl CanonicalSerialize for Encoding {
    fn serialized_size(&self) -> usize {
        32
    }

    fn serialize<W: std::io::Write>(
        &self,
        mut writer: W,
    ) -> Result<(), ark_serialize::SerializationError> {
        writer.write_all(&self.0[..])?;
        Ok(())
    }
}

impl CanonicalSerialize for Element {
    fn serialized_size(&self) -> usize {
        32
    }

    fn serialize<W: std::io::Write>(
        &self,
        writer: W,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.compress().serialize(writer)
    }
}

impl Encoding {
    #[allow(non_snake_case)]
    pub fn decompress(&self) -> Result<Element, EncodingError> {
        // This isn't a constant, only because traits don't have const methods
        // yet and multiplication is only implemented as part of the Mul trait.
        let D4: Fq = EdwardsParameters::COEFF_D * Fq::from(4u32);

        // 1/2. Reject unless s is canonically encoded and nonnegative.
        let s = Fq::deserialize(&self.0[..]).map_err(|_| EncodingError::InvalidEncoding)?;
        if s.is_negative() {
            return Err(EncodingError::InvalidEncoding);
        }

        // 3. u_1 <- 1 - s^2
        let ss = s.square();
        let u_1 = Fq::one() - ss;

        // 4. u_2 <- u_1^2 - 4d s^2
        let u_2 = u_1.square() - D4 * ss;

        // 5. sqrt
        let (was_square, mut v) = Fq::sqrt_ratio_zeta(&Fq::one(), &(u_2 * u_1.square()));
        if !was_square {
            return Err(EncodingError::InvalidEncoding);
        }

        // 6. sign check
        let two_s_u_1 = *TWO * s * u_1;
        let check = two_s_u_1 * v;
        if check.is_negative() {
            v = -v;
        }

        // 7. coordinates
        let x = two_s_u_1 * v.square() * u_2;
        let y = (Fq::one() + ss) * v * u_1;
        let z = Fq::one();
        let t = x * y;

        debug_assert!(
            EdwardsProjective::new(x, y, t, z).is_on_curve(),
            "resulting point must be on the curve",
        );

        Ok(Element {
            inner: EdwardsProjective::new(x, y, t, z),
        })
    }
}

impl TryFrom<&[u8]> for Encoding {
    type Error = EncodingError;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        if bytes.len() != 32 {
            Err(EncodingError::InvalidSliceLength)
        } else {
            let mut arr = [0u8; 32];
            arr.copy_from_slice(&bytes[0..32]);
            Ok(Encoding(arr))
        }
    }
}

impl TryFrom<&Encoding> for Element {
    type Error = EncodingError;
    fn try_from(bytes: &Encoding) -> Result<Self, Self::Error> {
        bytes.decompress()
    }
}

impl TryFrom<Encoding> for Element {
    type Error = EncodingError;
    fn try_from(bytes: Encoding) -> Result<Self, Self::Error> {
        bytes.decompress()
    }
}

impl CanonicalDeserialize for Encoding {
    fn deserialize<R: std::io::Read>(
        mut reader: R,
    ) -> Result<Self, ark_serialize::SerializationError> {
        let mut bytes = [0u8; 32];
        reader.read_exact(&mut bytes[..])?;
        Ok(Self(bytes))
    }
}

impl CanonicalDeserialize for Element {
    fn deserialize<R: std::io::Read>(reader: R) -> Result<Self, ark_serialize::SerializationError> {
        let bytes = Encoding::deserialize(reader)?;
        bytes
            .try_into()
            .map_err(|_| ark_serialize::SerializationError::InvalidData)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Group operations
////////////////////////////////////////////////////////////////////////////////

impl<'a, 'b> Add<&'b Element> for &'a Element {
    type Output = Element;

    fn add(self, other: &'b Element) -> Element {
        Element {
            inner: self.inner + other.inner,
        }
    }
}

impl<'b> Add<&'b Element> for Element {
    type Output = Element;
    fn add(self, other: &'b Element) -> Element {
        &self + other
    }
}

impl<'a> Add<Element> for &'a Element {
    type Output = Element;
    fn add(self, other: Element) -> Element {
        self + &other
    }
}

impl Add<Element> for Element {
    type Output = Element;
    fn add(self, other: Element) -> Element {
        &self + &other
    }
}

impl<'b> AddAssign<&'b Element> for Element {
    fn add_assign(&mut self, other: &'b Element) {
        *self = Element {
            inner: self.inner + other.inner,
        }
    }
}

impl AddAssign<Element> for Element {
    fn add_assign(&mut self, other: Element) {
        *self += &other;
    }
}

impl<'a, 'b> Sub<&'b Element> for &'a Element {
    type Output = Element;

    fn sub(self, other: &'b Element) -> Element {
        Element {
            inner: self.inner - other.inner,
        }
    }
}

impl<'b> Sub<&'b Element> for Element {
    type Output = Element;

    fn sub(self, other: &'b Element) -> Element {
        &self - other
    }
}

impl<'a> Sub<Element> for &'a Element {
    type Output = Element;

    fn sub(self, other: Element) -> Element {
        self - &other
    }
}

impl Sub<Element> for Element {
    type Output = Element;

    fn sub(self, other: Element) -> Element {
        &self - &other
    }
}

impl<'b> SubAssign<&'b Element> for Element {
    fn sub_assign(&mut self, other: &'b Element) {
        *self = Element {
            inner: self.inner - other.inner,
        }
    }
}

impl SubAssign<Element> for Element {
    fn sub_assign(&mut self, other: Element) {
        *self -= &other;
    }
}

impl Neg for Element {
    type Output = Self;

    fn neg(self) -> Self {
        Element { inner: -self.inner }
    }
}

impl<'b> MulAssign<&'b Scalar> for Element {
    // Scalar multiplication is performed through the implementation
    // of `MulAssign` on `EdwardsProjective` which is a type alias for
    // `GroupProjective<EdwardsParameters>`.
    fn mul_assign(&mut self, point: &'b Scalar) {
        let mut p = self.inner;
        p *= point.inner;
        *self = Element { inner: p }
    }
}

impl MulAssign<Scalar> for Element {
    fn mul_assign(&mut self, other: Scalar) {
        *self *= &other;
    }
}

impl<'a, 'b> Mul<&'b Scalar> for &'a Element {
    type Output = Element;

    fn mul(self, point: &'b Scalar) -> Element {
        let mut p = self.inner;
        p *= point.inner;
        Element { inner: p }
    }
}

impl<'a, 'b> Mul<&'b Element> for &'a Scalar {
    type Output = Element;

    fn mul(self, point: &'b Element) -> Element {
        point * self
    }
}

impl<'b> Mul<&'b Scalar> for Element {
    type Output = Element;

    fn mul(self, other: &'b Scalar) -> Element {
        &self * other
    }
}

impl<'a> Mul<Scalar> for &'a Element {
    type Output = Element;

    fn mul(self, other: Scalar) -> Element {
        self * &other
    }
}

impl Mul<Scalar> for Element {
    type Output = Element;

    fn mul(self, other: Scalar) -> Element {
        &self * &other
    }
}

impl<'b> Mul<&'b Element> for Scalar {
    type Output = Element;

    fn mul(self, other: &'b Element) -> Element {
        &self * other
    }
}

impl<'a> Mul<Element> for &'a Scalar {
    type Output = Element;

    fn mul(self, other: Element) -> Element {
        self * &other
    }
}

impl Mul<Element> for Scalar {
    type Output = Element;

    fn mul(self, other: Element) -> Element {
        &self * &other
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;

    #[test]
    fn identity_encoding_is_zero() {
        let identity = Element::default();
        let identity_bytes = identity.compress();
        assert_eq!(identity_bytes.0, [0; 32]);
        let identity2 = identity_bytes.decompress().unwrap();
        assert_eq!(identity, identity2);
    }

    #[test]
    fn check_generator() {
        let mut bytes = [0u8; 32];

        for b in 1..=255 {
            bytes[0] = b;
            if let Ok(_element) = Encoding(bytes).decompress() {
                break;
            }
        }

        // The generator [8,0,...] is minimal
        assert_eq!(bytes[0], 8);

        let enc2 = Encoding(bytes).decompress().unwrap().compress();
        assert_eq!(bytes, enc2.0);
    }

    #[test]
    fn test_encoding_matches_sage_encoding() {
        use hex;

        let mut accumulator = Element::default();
        let basepoint = Element::basepoint();

        let expected_points = [
            "0000000000000000000000000000000000000000000000000000000000000000",
            "0800000000000000000000000000000000000000000000000000000000000000",
            "b2ecf9b9082d6306538be73b0d6ee741141f3222152da78685d6596efc8c1506",
            "2ebd42dd3a2307083c834e79fb9e787e352dd33e0d719f86ae4adb02fe382409",
            "6acd327d70f9588fac373d165f4d9d5300510274dffdfdf2bf0955acd78da50d",
            "460f913e516441c286d95dd30b0a2d2bf14264f325528b06455d7cb93ba13a0b",
            "ec8798bcbb3bf29329549d769f89cf7993e15e2c68ec7aa2a956edf5ec62ae07",
            "48b01e513dd37d94c3b48940dc133b92ccba7f546e99d3fc2e602d284f609f00",
            "a4e85dddd19c80ecf5ef10b9d27b6626ac1a4f90bd10d263c717ecce4da6570a",
            "1a8fea8cbfbc91236d8c7924e3e7e617f9dd544b710ee83827737fe8dc63ae00",
            "0a0f86eaac0c1af30eb138467c49381edb2808904c81a4b81d2b02a2d7816006",
            "588125a8f4e2bab8d16affc4ca60c5f64b50d38d2bb053148021631f72e99b06",
            "f43f4cefbe7326eaab1584722b1b4860de554b23a14490a03f3fd63a089add0b",
            "76c739a33ffd15cf6554a8e705dc573f26490b64de0c5bd4e4ac75ed5af8e60b",
            "200136952d18d3f6c70347032ba3fef4f60c240d706be2950b4f42f1a7087705",
            "bcb0f922df1c7aa9579394020187a2e19e2d8073452c6ab9b0c4b052aa50f505",
        ];

        for hexstr in expected_points {
            let bytes = hex::decode(hexstr).unwrap();
            let point = Encoding::try_from(bytes.as_slice())
                .unwrap()
                .decompress()
                .unwrap();

            let result_hexstr = hex::encode(point.compress().0);

            assert_eq!(result_hexstr.as_str(), hexstr);

            assert_eq!(accumulator, point);

            accumulator += basepoint;
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
                118, 191, 44, 105, 223, 173, 54, 26, 156, 64, 125, 117, 96, 97, 33, 66, 88, 153,
                14, 206, 174, 129, 102, 135, 58, 214, 120, 89, 56, 163, 205, 2,
            ],
            [
                72, 47, 66, 129, 24, 237, 191, 146, 248, 97, 173, 205, 208, 146, 214, 222, 207, 15,
                66, 231, 182, 40, 110, 244, 120, 41, 156, 60, 95, 51, 113, 0,
            ],
            [
                180, 100, 186, 73, 164, 233, 192, 87, 87, 111, 188, 196, 232, 194, 253, 202, 145,
                80, 72, 186, 245, 243, 12, 140, 43, 48, 233, 64, 220, 246, 195, 4,
            ],
            [
                251, 184, 112, 124, 131, 61, 118, 222, 107, 35, 212, 35, 158, 128, 150, 67, 14, 56,
                5, 27, 231, 103, 126, 206, 75, 44, 121, 192, 43, 218, 169, 18,
            ],
            [
                111, 209, 86, 18, 133, 185, 154, 96, 249, 211, 127, 84, 195, 120, 202, 226, 39,
                251, 42, 33, 171, 197, 213, 54, 50, 139, 98, 160, 160, 76, 66, 0,
            ],
        ];

        let expected_xy_coordinates = [
            [
                ark_ff::field_new!(
                    Fq,
                    "1267955849280145133999011095767946180059440909377398529682813961428156596086"
                ),
                ark_ff::field_new!(
                    Fq,
                    "5356565093348124788258444273601808083900527100008973995409157974880178412098"
                ),
            ],
            [
                ark_ff::field_new!(
                    Fq,
                    "200008274961555948861247117495670973596739637087794512618526686349329837896"
                ),
                ark_ff::field_new!(
                    Fq,
                    "2647160997166078743329301827422337374657888721988786738921611999944531338531"
                ),
            ],
            [
                ark_ff::field_new!(
                    Fq,
                    "2155490339590342463221653343294318190999589388357737005449404856842887783604"
                ),
                ark_ff::field_new!(
                    Fq,
                    "4481458139914468306847063704257284041203193835717940998143249933452019482864"
                ),
            ],
            [
                ark_ff::field_new!(
                    Fq,
                    "8441734188697456667144320566571776204829442942061036742254289993746772703483"
                ),
                ark_ff::field_new!(
                    Fq,
                    "7620110693934777700596031508223455603299325399921316208494126022090241681882"
                ),
            ],
            [
                ark_ff::field_new!(
                    Fq,
                    "117140769479701400914019462651613478220779023707299711126764550434911080815"
                ),
                ark_ff::field_new!(
                    Fq,
                    "5810205353606534415061383517342879526260822986695264074414984877708731584311"
                ),
            ],
            [
                ark_ff::field_new!(
                    Fq,
                    "2862934919620274750419502812011588585092662737799324413702618024907129157332"
                ),
                ark_ff::field_new!(
                    Fq,
                    "230753360126360732618318176279626021301046880630378028205676927966589412379"
                ),
            ],
        ];

        for (ind, input) in inputs.iter().enumerate() {
            let input_element =
                Fq::deserialize(&input[..]).expect("encoding of test vector is valid");

            let expected: Element = EdwardsAffine::new(
                expected_xy_coordinates[ind][0],
                expected_xy_coordinates[ind][1],
            )
            .into();
            let actual = Element::elligator_map(&input_element);

            assert_eq!(actual, expected);
        }
    }

    proptest! {
        #[test]
        fn decompress_round_trip_if_successful(bytes: [u8; 32]) {
            let bytes = Encoding(bytes);

            if let Ok(element) = bytes.decompress() {
                let bytes2 = element.compress();
                assert_eq!(bytes, bytes2);
            }
        }
    }
}
