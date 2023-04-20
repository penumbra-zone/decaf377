use std::convert::TryInto;

use ark_ff::{FromBytes, ToBytes};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::io::{Read, Result as IoResult, Write};

use crate::{AffineElement, Element, Encoding, FieldExt, Fq};

impl ToBytes for Element {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        let field_element = self.vartime_compress_to_field();
        let bytes: [u8; 32] = field_element.to_bytes();
        bytes.write(&mut writer)
    }
}

impl FromBytes for Element {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        let field_element = Fq::read(&mut reader)?;
        let element = Encoding(field_element.to_bytes())
            .vartime_decompress()
            .map_err(|_| std::io::ErrorKind::InvalidData)?;
        Ok(element)
    }
}

impl ToBytes for AffineElement {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        let element: Element = self.into();
        element.write(&mut writer)
    }
}

impl FromBytes for AffineElement {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        let element = Element::read(&mut reader)?;
        Ok(element.into())
    }
}

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
