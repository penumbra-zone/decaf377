use ark_ed_on_bls12_377::EdwardsProjective;
use ark_ff::Zero;
use zeroize::Zeroize;

use crate::Encoding;

#[derive(Copy, Clone)]
pub struct Element {
    pub(crate) inner: EdwardsProjective,
}

impl std::fmt::Debug for Element {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // This prints the hex of the encoding of self, rather than the
        // coordinates, because that's what's most useful to downstream
        // consumers of the library.
        f.write_fmt(format_args!(
            "decaf377::Element({})",
            hex::encode(&self.compress().0[..])
        ))
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
}
