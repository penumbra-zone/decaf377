use ark_ff::{FromBytes, ToBytes};
use ark_std::io::{Read, Result as IoResult, Write};

use crate::{Element, Encoding, FieldExt, Fq};

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
