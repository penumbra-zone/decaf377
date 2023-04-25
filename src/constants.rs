use once_cell::sync::Lazy;

use ark_ed_on_bls12_377::{Fq, Fr};
use ark_ff::{self, BigInteger256, Field, One};

pub static ONE: Lazy<Fq> = Lazy::new(|| Fq::one());
pub static TWO: Lazy<Fq> = Lazy::new(|| Fq::one() + Fq::one());

// Zeta is called QNR in the sage specification.
pub static ZETA: Lazy<Fq> = Lazy::new(|| {
    ark_ff::MontFp!("2841681278031794617739547238867782961338435681360110683443920362658525667816")
});

// Constants used for square root computation //

// N is the 2-adicity
pub static N: u32 = 47;

// M is `(p - 1) / 2^N` = 60001509534603559531609739528203892656505753216962260608619555
pub static M: Lazy<BigInteger256> = Lazy::new(|| {
    let elem: Fq =
        ark_ff::MontFp!("60001509534603559531609739528203892656505753216962260608619555");
    elem.into()
});

// (M-1)/2 = 30000754767301779765804869764101946328252876608481130304309777
pub static M_MINUS_ONE_DIV_TWO: Lazy<BigInteger256> = Lazy::new(|| {
    let elem: Fq =
        ark_ff::MontFp!("30000754767301779765804869764101946328252876608481130304309777");
    elem.into()
});

// ZETA**((1-M)/2) = 6762755396584113496485389421189479608933826763106393667349575256979972066439
pub static ZETA_TO_ONE_MINUS_M_DIV_TWO: Lazy<Fq> = Lazy::new(|| {
    ark_ff::MontFp!("6762755396584113496485389421189479608933826763106393667349575256979972066439")
});

// G = ZETA^M
// = 4732611889701835744065511820927274956354524915951001256593514693060564426294
pub static G: Lazy<Fq> = Lazy::new(|| (*ZETA).pow(*M));

// Choice of W in the square root algorithm.
pub static SQRT_W: u32 = 8;

// Canonical basepoint projective coordinates
pub static B_X: Lazy<Fq> = Lazy::new(|| {
    ark_ff::MontFp!("4959445789346820725352484487855828915252512307947624787834978378872129235627")
});
pub static B_Y: Lazy<Fq> = Lazy::new(|| {
    ark_ff::MontFp!("6060471950081851567114691557659790004756535011754163002297540472747064943288")
});
pub static B_T: Lazy<Fq> = Lazy::new(|| {
    ark_ff::MontFp!("7709528722369014828560854854815397945854484030754980890329689855465844419067")
});
pub static B_Z: Lazy<Fq> = Lazy::new(|| ark_ff::MontFp!("1"));

// Canonical basepoint affine coordinates
pub const GENERATOR_X: Fq =
    ark_ff::MontFp!("4959445789346820725352484487855828915252512307947624787834978378872129235627");
pub const GENERATOR_Y: Fq =
    ark_ff::MontFp!("6060471950081851567114691557659790004756535011754163002297540472747064943288");

// Modulus of basefield
pub static R: Lazy<Fr> = Lazy::new(|| {
    ark_ff::MontFp!("2111115437357092606062206234695386632838870926408408195193685246394721360383")
});
