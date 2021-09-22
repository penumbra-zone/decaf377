use lazy_static::lazy_static;

use ark_ed_on_bls12_377::Fq;
use ark_ff;
use ark_ff::One;

lazy_static! {
    // Zeta is called QNR in the sage specification.
    pub static ref ZETA: ark_ed_on_bls12_377::Fq = ark_ff::field_new!(
        Fq,
        "2841681278031794617739547238867782961338435681360110683443920362658525667816"
    );
    pub static ref ONE: ark_ed_on_bls12_377::Fq = Fq::one();
    pub static ref TWO: ark_ed_on_bls12_377::Fq = Fq::one() + Fq::one();
}
