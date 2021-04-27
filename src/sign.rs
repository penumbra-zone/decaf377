use std::str::FromStr;

use ark_ed_on_bls12_377::Fq;

pub trait Sign: core::ops::Neg<Output = Self> + Sized {
    fn is_nonnegative(&self) -> bool;

    fn is_negative(&self) -> bool {
        !self.is_nonnegative()
    }

    fn abs(self) -> Self {
        if self.is_nonnegative() {
            self
        } else {
            -self
        }
    }
}

impl Sign for Fq {
    fn is_nonnegative(&self) -> bool {
        // TODO: make this a constant
        let half_q = Fq::from_str(
            "4222230874714185212124412469390773265687949667577031913967616727958704619520",
        )
        .unwrap();
        self <= &half_q
    }
}
