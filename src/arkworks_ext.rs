use ark_ed_on_bls12_377::Fq;
use ark_serialize::CanonicalSerialize;

pub trait FieldFormatExt: Sized {
    fn to_decimal_string(&self) -> String;
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
