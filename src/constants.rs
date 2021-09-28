use once_cell::sync::Lazy;

use ark_ed_on_bls12_377::Fq;
use ark_ff;
use ark_ff::One;

pub static ONE: Lazy<ark_ed_on_bls12_377::Fq> = Lazy::new(|| Fq::one());

pub static TWO: Lazy<ark_ed_on_bls12_377::Fq> = Lazy::new(|| Fq::one() + Fq::one());

// Zeta is called QNR in the sage specification.
pub static ZETA: Lazy<ark_ed_on_bls12_377::Fq> = Lazy::new(|| {
    ark_ff::field_new!(
        Fq,
        "2841681278031794617739547238867782961338435681360110683443920362658525667816"
    )
});
