#![allow(non_snake_case)]

use core::convert::{TryFrom, TryInto};

use ark_ec::twisted_edwards::TECurveConfig;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, Write};

use crate::ark_curve::{
    constants::TWO, edwards::Decaf377EdwardsConfig, on_curve::OnCurve, EdwardsProjective, Element,
};
use crate::sign::Sign;
use crate::{EncodingError, Fq};

#[derive(Copy, Clone, Default, Eq, Ord, PartialOrd, PartialEq)]
pub struct Encoding(pub [u8; 32]);

impl core::fmt::Debug for Encoding {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_fmt(format_args!(
            "decaf377::Encoding({})",
            hex::encode(&self.0[..])
        ))
    }
}

impl Encoding {
    #[deprecated(note = "please use `vartime_decompress` instead")]
    pub fn decompress(&self) -> Result<Element, EncodingError> {
        self.vartime_decompress()
    }

    pub fn vartime_decompress(&self) -> Result<Element, EncodingError> {
        // Top three bits of last byte should be zero
        if self.0[31] >> 5 != 0u8 {
            return Err(EncodingError::InvalidEncoding);
        }

        // This isn't a constant, only because traits don't have const methods
        // yet and multiplication is only implemented as part of the Mul trait.
        let D4: Fq = Decaf377EdwardsConfig::COEFF_D * Fq::from(4u32);

        // 1/2. Reject unless s is canonically encoded and nonnegative.
        let s =
            Fq::deserialize_compressed(&self.0[..]).map_err(|_| EncodingError::InvalidEncoding)?;
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

impl Element {
    pub fn negate(&self) -> Element {
        Element { inner: -self.inner }
    }

    pub fn vartime_compress_to_field(&self) -> Fq {
        // This isn't a constant, only because traits don't have const methods
        // yet and subtraction is only implemented as part of the Sub trait.
        let A_MINUS_D = Decaf377EdwardsConfig::COEFF_A - Decaf377EdwardsConfig::COEFF_D;
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

        s
    }

    pub fn vartime_compress(&self) -> Encoding {
        let s = self.vartime_compress_to_field();

        // Encode.
        let mut bytes = [0u8; 32];
        debug_assert_eq!(s.serialized_size(ark_serialize::Compress::Yes), 32);
        s.serialize_compressed(&mut bytes[..])
            .expect("serialization into array should be infallible");
        // Set top three bits of last byte to zero
        bytes[31] &= 0b00011111;

        Encoding(bytes)
    }
}

impl From<&Element> for Encoding {
    fn from(point: &Element) -> Self {
        point.vartime_compress()
    }
}

impl From<Element> for Encoding {
    fn from(point: Element) -> Self {
        point.vartime_compress()
    }
}

impl CanonicalSerialize for Encoding {
    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        match compress {
            ark_serialize::Compress::Yes => 32,
            ark_serialize::Compress::No => unimplemented!(),
        }
    }

    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        _mode: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        writer.write_all(&self.0[..])?;
        Ok(())
    }
}

impl CanonicalSerialize for Element {
    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        match compress {
            ark_serialize::Compress::Yes => 32,
            ark_serialize::Compress::No => unimplemented!(),
        }
    }

    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        mode: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.vartime_compress().serialize_with_mode(writer, mode)
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

impl From<[u8; 32]> for Encoding {
    fn from(bytes: [u8; 32]) -> Encoding {
        Encoding(bytes)
    }
}

impl From<Encoding> for [u8; 32] {
    fn from(enc: Encoding) -> [u8; 32] {
        enc.0
    }
}

impl TryFrom<&Encoding> for Element {
    type Error = EncodingError;
    fn try_from(bytes: &Encoding) -> Result<Self, Self::Error> {
        bytes.vartime_decompress()
    }
}

impl TryFrom<Encoding> for Element {
    type Error = EncodingError;
    fn try_from(bytes: Encoding) -> Result<Self, Self::Error> {
        bytes.vartime_decompress()
    }
}

impl TryFrom<&[u8]> for Element {
    type Error = EncodingError;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        let b: [u8; 32] = bytes
            .try_into()
            .map_err(|_| EncodingError::InvalidSliceLength)?;

        Encoding(b).try_into()
    }
}

impl TryFrom<[u8; 32]> for Element {
    type Error = EncodingError;

    fn try_from(bytes: [u8; 32]) -> Result<Self, Self::Error> {
        let encoding = Encoding(bytes);
        encoding.try_into()
    }
}

impl From<Element> for [u8; 32] {
    fn from(enc: Element) -> [u8; 32] {
        enc.vartime_compress().0
    }
}

impl ark_serialize::Valid for Encoding {
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        // At this stage, validity just means the point has 32 bytes
        // which is encoded in the type information.
        Ok(())
    }
}

impl CanonicalDeserialize for Encoding {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        match compress {
            ark_serialize::Compress::Yes => (),
            ark_serialize::Compress::No => unimplemented!(),
        }
        match validate {
            ark_serialize::Validate::Yes => (),
            ark_serialize::Validate::No => unimplemented!(),
        }
        let mut bytes = [0u8; 32];
        reader.read_exact(&mut bytes[..])?;
        Ok(Self(bytes))
    }
}

impl CanonicalDeserialize for Element {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        match compress {
            ark_serialize::Compress::Yes => (),
            ark_serialize::Compress::No => unimplemented!(),
        }
        match validate {
            ark_serialize::Validate::Yes => (),
            ark_serialize::Validate::No => unimplemented!(),
        }
        let bytes = Encoding::deserialize_compressed(reader)?;
        bytes
            .try_into()
            .map_err(|_| ark_serialize::SerializationError::InvalidData)
    }
}
