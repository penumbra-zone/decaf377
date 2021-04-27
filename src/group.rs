use std::convert::{TryFrom, TryInto};

use ark_ec::models::TEModelParameters;
use ark_ed_on_bls12_377::{EdwardsParameters, EdwardsProjective, Fq};
use ark_ff::{Field, One, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

use crate::{invsqrt::InvSqrt, sign::Sign, EncodingError};

use ark_ec::models::twisted_edwards_extended::GroupProjective;

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

        let on_curve = (YY - XX) == (ZZ + P::COEFF_D * TT);
        let on_segre_embedding = self.t * self.z == self.x * self.y;

        on_curve && on_segre_embedding
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Decaf377Bytes(pub [u8; 32]);

#[derive(Copy, Clone, Debug)]
pub struct Decaf377 {
    inner: EdwardsProjective,
}

impl Decaf377 {
    #[allow(non_snake_case)]
    pub fn compress(&self) -> Decaf377Bytes {
        // This isn't a constant, only because traits don't have const methods
        // yet and subtraction is only implemented as part of the Sub trait.
        let D = EdwardsParameters::COEFF_D;
        let A_MINUS_D = EdwardsParameters::COEFF_A - EdwardsParameters::COEFF_D;
        let p = &self.inner;

        // 1. r <- 1 / \sqrt { (a -d ) (Z  + Y) (Z - Y)}
        let Z_plus_Y = p.z + &p.y;
        let Z_minus_Y = p.z - &p.y;
        let mut r = (A_MINUS_D * Z_plus_Y * Z_minus_Y)
            .invsqrt()
            .expect("input is square");

        // 2. u <- (a - d) r
        let u = A_MINUS_D * r;

        // 3. r <- -r if -2uZ is negative
        let check = (Fq::zero() - (u + u)) * &p.z;
        if check.is_negative() {
            r = -r;
        }

        // 4. s <- | u ( r ( aZX - dYT) + Y) / a|
        // Since a = -1, this is
        //   |u ( r ( -ZX - dYT) + Y) / -1 |
        // = |-u(Y - r(ZX + dYT))|
        let s = (-u * (p.y - r * (p.z * p.x + D * p.y * p.t))).abs();

        let mut bytes = [0u8; 32];
        debug_assert_eq!(s.serialized_size(), 32);
        s.serialize(&mut bytes[..])
            .expect("serialization into array should be infallible");

        Decaf377Bytes(bytes)
    }
}

impl From<&Decaf377> for Decaf377Bytes {
    fn from(point: &Decaf377) -> Self {
        point.compress()
    }
}

impl From<Decaf377> for Decaf377Bytes {
    fn from(point: Decaf377) -> Self {
        point.compress()
    }
}

impl CanonicalSerialize for Decaf377Bytes {
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

impl CanonicalSerialize for Decaf377 {
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

impl Decaf377Bytes {
    #[allow(non_snake_case)]
    pub fn decompress(&self) -> Result<Decaf377, EncodingError> {
        // This isn't a constant, only because traits don't have const methods
        // yet and multiplication is only implemented as part of the Mul trait.
        let D4: Fq = EdwardsParameters::COEFF_D * Fq::from(4u32);
        let TWO = Fq::one() + Fq::one();

        // 1. Reject unless s is canonically encoded and nonnegative.
        let s = Fq::deserialize(&self.0[..]).map_err(|_| EncodingError::InvalidEncoding)?;
        if !s.is_nonnegative() {
            return Err(EncodingError::InvalidEncoding);
        }

        // 2. X <- 2s
        let X = s + s;

        // 3. Z <- 1 + as^2 = 1 - s^2
        let ss = s.square();
        let Z = Fq::one() - ss;

        // 4. u <- Z^2 - 4d s^2
        let ZZ = Z.square();
        let u = ZZ - D4 * ss;

        // 5. v <- 1 / \sqrt { u s^2} if u s^2 is square and nonzero, 0 if zero, reject if nonsquare.
        let uss: Fq = u * ss;
        let mut v = uss.invsqrt().ok_or(EncodingError::InvalidEncoding)?;
        debug_assert_eq!(v * v * uss, Fq::one(), "invsqrt should be invsqrt");

        // 6. v <- -v if uv is negative
        let uv: Fq = u * v;
        if uv.is_negative() {
            v = -v;
        }

        // 7/8. w <- vs(2-Z) ;  w <- w + 1 if s = 0
        let w = if s.is_zero() {
            Fq::one()
        } else {
            v * s * (TWO - Z)
        };

        // 9. Y <- wZ
        let Y = w * Z;

        // 10. T <- wX
        let T = w * X;

        debug_assert!(
            EdwardsProjective::new(X, Y, Z, T).is_on_curve(),
            "resulting point must be on the curve",
        );

        Ok(Decaf377 {
            inner: EdwardsProjective::new(X, Y, Z, T),
        })
    }
}

impl TryFrom<&Decaf377Bytes> for Decaf377 {
    type Error = EncodingError;
    fn try_from(bytes: &Decaf377Bytes) -> Result<Self, Self::Error> {
        bytes.decompress()
    }
}

impl TryFrom<Decaf377Bytes> for Decaf377 {
    type Error = EncodingError;
    fn try_from(bytes: Decaf377Bytes) -> Result<Self, Self::Error> {
        bytes.decompress()
    }
}

impl CanonicalDeserialize for Decaf377Bytes {
    fn deserialize<R: std::io::Read>(
        mut reader: R,
    ) -> Result<Self, ark_serialize::SerializationError> {
        let mut bytes = [0u8; 32];
        reader.read_exact(&mut bytes[..])?;
        Ok(Self(bytes))
    }
}

impl CanonicalDeserialize for Decaf377 {
    fn deserialize<R: std::io::Read>(reader: R) -> Result<Self, ark_serialize::SerializationError> {
        let bytes = Decaf377Bytes::deserialize(reader)?;
        bytes
            .try_into()
            .map_err(|_| ark_serialize::SerializationError::InvalidData)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Group operations
////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;

    #[test]
    fn identity_encoding_is_zero() {
        let identity = Decaf377 {
            inner: EdwardsProjective::zero(),
        };
        let identity_bytes = identity.compress();
        assert_eq!(identity_bytes.0, [0; 32]);
        let identity2 = identity_bytes.decompress().unwrap();
        //assert_eq!(identity, identity2);
    }

    proptest! {
        #[test]
        fn generator_multiples_on_curve(x: u64) {
            use ark_ec::ProjectiveCurve;
            let gen = EdwardsProjective::prime_subgroup_generator();
            let point = gen.mul(&[x]);
            assert!(point.is_on_curve());
        }

        #[test]
        fn decompress_round_trip_if_successful(bytes: [u8; 32]) {
            let bytes = Decaf377Bytes(bytes);

            if let Ok(element) = bytes.decompress() {
                let bytes2 = element.compress();
                assert_eq!(bytes, bytes2);
            }
        }
    }
}
