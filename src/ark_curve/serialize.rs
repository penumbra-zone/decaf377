use core::convert::TryInto;

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::io::{Read, Write};

use crate::ark_curve::{AffineElement, Element, Encoding};

impl CanonicalDeserialize for AffineElement {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        match compress {
            ark_serialize::Compress::Yes => (),
            ark_serialize::Compress::No => unimplemented!(),
        };
        match validate {
            ark_serialize::Validate::Yes => (),
            ark_serialize::Validate::No => unimplemented!(),
        }
        let bytes = Encoding::deserialize_compressed(reader)?;
        let element: Element = bytes
            .try_into()
            .map_err(|_| ark_serialize::SerializationError::InvalidData)?;
        Ok(element.into())
    }
}

impl CanonicalSerialize for AffineElement {
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
        let element: Element = self.into();
        element.vartime_compress().serialize_with_mode(writer, mode)
    }
}
