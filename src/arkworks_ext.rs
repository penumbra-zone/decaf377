use ark_ed_on_bls12_377::Fq;
use ark_ff::SquareRootField;
use ark_serialize::CanonicalSerialize;

use crate::sign::Sign;

pub trait FieldFormatExt: Sized {
    fn to_decimal_string(&self) -> String;
}

pub trait XSqrt: Sized {
    // This trait matches the xsqrt function in the sage spec,
    // always returning a positive root if it exists.
    fn xsqrt(&self) -> Option<Self>;
}

impl FieldFormatExt for Fq {
    fn to_decimal_string(&self) -> String {
        // incantation to convert to LE bytes
        let mut bytes = [0u8; 32];
        debug_assert_eq!(self.serialized_size(), 32);
        self.serialize(&mut bytes[..])
            .expect("serialization into array should be infallible");

        let num = num_bigint::BigUint::from_bytes_le(&bytes);

        format!("{}", num)
    }
}

impl XSqrt for Fq {
    fn xsqrt(&self) -> Option<Self> {
        match self.sqrt() {
            Some(s) => {
                if s.is_negative() {
                    Some(-s)
                } else {
                    Some(s)
                }
            }
            None => None,
        }
    }
}
