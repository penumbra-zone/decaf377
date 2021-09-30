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

use crate::constants::{TWO, ZETA};
use crate::{invsqrt::SqrtRatioZeta, scalar::Scalar, sign::Sign, EncodingError};

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

        let n1 = (r + Fq::one()) * (A - *TWO * D) / den;
        let n2 = r * n1;

        let s;
        let t;

        match n1.sqrt() {
            Some(n1_root) => {
                s = n1_root.abs();
                t = -(r - Fq::one()) * (A - *TWO * D).square() / den - Fq::one();
            }
            None => {
                s = -(n2.sqrt().expect("n2 sqrt not found!").abs());
                t = r * (r - Fq::one()) * (A - *TWO * D).square() / den - Fq::one();
            }
        }

        if s == Fq::zero() {
            return Element::default();
        }

        // Convert point from its Jacobi quartic representation (s, t)
        let x = *TWO * s / (Fq::one() + EdwardsParameters::COEFF_A * s.square());
        let y = (Fq::one() - EdwardsParameters::COEFF_A * s.square()) / t;

        // Convert point from affine (x, y) to projective (X : Y : Z : T)
        let result = Element {
            inner: EdwardsAffine::new(x, y).into(),
        };

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
        if bytes.len() == 32 {
            let mut arr = [0u8; 32];
            arr.copy_from_slice(&bytes[0..32]);
            Ok(Encoding(arr))
        } else {
            Err(EncodingError::InvalidSliceLength)
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
                    "1502379126429822955521756759528876454108853047288874182661923263559139887582"
                ),
                ark_ff::field_new!(
                    Fq,
                    "7074060208122316523843780248565740332109149189893811936352820920606931717751"
                ),
            ],
            [
                ark_ff::field_new!(
                    Fq,
                    "2943006201157313879823661217587757631000260143892726691725524748591717287835"
                ),
                ark_ff::field_new!(
                    Fq,
                    "4988568968545687084099497807398918406354768651099165603393269329811556860241"
                ),
            ],
            [
                ark_ff::field_new!(
                    Fq,
                    "2893226299356126359042735859950249532894422276065676168505232431940642875576"
                ),
                ark_ff::field_new!(
                    Fq,
                    "5540423804567408742733533031617546054084724133604190833318816134173899774745"
                ),
            ],
            [
                ark_ff::field_new!(
                    Fq,
                    "2950911977149336430054248283274523588551527495862004038190631992225597951816"
                ),
                ark_ff::field_new!(
                    Fq,
                    "4487595759841081228081250163499667279979722963517149877172642608282938805393"
                ),
            ],
            [
                ark_ff::field_new!(
                    Fq,
                    "3318574188155535806336376903248065799756521242795466350457330678746659358665"
                ),
                ark_ff::field_new!(
                    Fq,
                    "7706453242502782485686954136003233626318476373744684895503194201695334921001"
                ),
            ],
            [
                ark_ff::field_new!(
                    Fq,
                    "3753408652523927772367064460787503971543824818235418436841486337042861871179"
                ),
                ark_ff::field_new!(
                    Fq,
                    "2820605049615187268236268737743168629279853653807906481532750947771625104256"
                ),
            ],
            [
                ark_ff::field_new!(
                    Fq,
                    "7803875556376973796629423752730968724982795310878526731231718944925551226171"
                ),
                ark_ff::field_new!(
                    Fq,
                    "7033839813997913565841973681083930410776455889380940679209912201081069572111"
                ),
            ],
        ];

        for (ind, input) in inputs.iter().enumerate() {
            let input_element =
                Fq::deserialize(&input[..]).expect("encoding of test vector is valid");

            let expected: Element = Element {
                inner: EdwardsAffine::new(
                    expected_xy_coordinates[ind][0],
                    expected_xy_coordinates[ind][1],
                )
                .into(),
            };

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
