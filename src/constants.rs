use once_cell::sync::Lazy;

use ark_ed_on_bls12_377::Fq;
use ark_ff::{self, BigInteger256, Field, One};

pub static ONE: Lazy<Fq> = Lazy::new(|| Fq::one());
pub static TWO: Lazy<Fq> = Lazy::new(|| Fq::one() + Fq::one());

// Zeta is called QNR in the sage specification.
pub static ZETA: Lazy<Fq> = Lazy::new(|| {
    ark_ff::field_new!(
        Fq,
        "2841681278031794617739547238867782961338435681360110683443920362658525667816"
    )
});

// Constants used for square root computation //

pub static ZETA_INVERSE: Lazy<Fq> =
    Lazy::new(|| (*ZETA).inverse().expect("inverse of zeta must exist"));

// N is the 2-adicity
pub static N: u32 = 47;

// (p - 1) // 2 = 4222230874714185212124412469390773265687949667577031913967616727958704619520
pub static EULER_CRITERION_POW: Lazy<BigInteger256> = Lazy::new(|| {
    ark_ff::field_new!(
        Fq,
        "4222230874714185212124412469390773265687949667577031913967616727958704619520"
    )
    .into()
});

// M is `(p - 1) / 2^N` = 60001509534603559531609739528203892656505753216962260608619555
pub static M: Lazy<BigInteger256> = Lazy::new(|| {
    ark_ff::field_new!(
        Fq,
        "60001509534603559531609739528203892656505753216962260608619555"
    )
    .into()
});

// (M-1)/2 = 30000754767301779765804869764101946328252876608481130304309777
pub static M_MINUS_ONE_DIV_TWO: Lazy<BigInteger256> = Lazy::new(|| {
    ark_ff::field_new!(
        Fq,
        "30000754767301779765804869764101946328252876608481130304309777"
    )
    .into()
});

// G = ZETA^M
// = 4732611889701835744065511820927274956354524915951001256593514693060564426294
pub static G: Lazy<Fq> = Lazy::new(|| (*ZETA).pow(*M));

// Choice of W in the square root algorithm.
pub static SQRT_W: u32 = 8;
