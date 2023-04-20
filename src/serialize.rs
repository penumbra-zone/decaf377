use std::convert::TryInto;

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::io::{Read, Result as IoResult, Write};

use crate::{AffineElement, Element, Encoding, FieldExt, Fq};

impl CanonicalDeserialize for AffineElement {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        let bytes = Encoding::deserialize(reader)?;
        let element: Element = bytes
            .try_into()
            .map_err(|_| ark_serialize::SerializationError::InvalidData)?;
        Ok(element.into())
    }
}

impl CanonicalSerialize for AffineElement {
    fn serialized_size(&self) -> usize {
        32
    }

    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        mode: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        let element: Element = self.into();
        element.vartime_compress().serialize(writer)
    }
}
