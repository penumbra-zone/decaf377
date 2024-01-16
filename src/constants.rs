use once_cell::sync::Lazy;

use crate::{Fq, Fr};
use ark_ff::{self, BigInteger256, Field, One};

use ark_ed_on_bls12_377::{Fq as ArkFq, Fr as ArkFr};

pub static ONE: Lazy<Fq> = Lazy::new(|| Fq::one());
pub static TWO: Lazy<Fq> = Lazy::new(|| Fq::one() + Fq::one());

pub(crate) fn from_ark_fq(x: ArkFq) -> Fq {
    BigInteger256::from(x).into()
}

fn from_ark_fr(x: ArkFr) -> Fr {
    BigInteger256::from(x).into()
}

// Zeta is called QNR in the sage specification.
pub static ZETA: Lazy<Fq> = Lazy::new(|| {
    from_ark_fq(ark_ff::MontFp!(
        "2841681278031794617739547238867782961338435681360110683443920362658525667816"
    ))
});

// Constants used for square root computation //

// N is the 2-adicity
pub static N: u32 = 47;

// M is `(p - 1) / 2^N` = 60001509534603559531609739528203892656505753216962260608619555
pub static M: Lazy<BigInteger256> = Lazy::new(|| {
    let elem: ArkFq =
        ark_ff::MontFp!("60001509534603559531609739528203892656505753216962260608619555");
    elem.into()
});

// (M-1)/2 = 30000754767301779765804869764101946328252876608481130304309777
pub static M_MINUS_ONE_DIV_TWO: Lazy<BigInteger256> = Lazy::new(|| {
    let elem: ArkFq =
        ark_ff::MontFp!("30000754767301779765804869764101946328252876608481130304309777");
    elem.into()
});

// ZETA**((1-M)/2) = 6762755396584113496485389421189479608933826763106393667349575256979972066439
pub static ZETA_TO_ONE_MINUS_M_DIV_TWO: Lazy<Fq> = Lazy::new(|| {
    from_ark_fq(ark_ff::MontFp!(
        "6762755396584113496485389421189479608933826763106393667349575256979972066439"
    ))
});

// G = ZETA^M
// = 4732611889701835744065511820927274956354524915951001256593514693060564426294
pub static G: Lazy<Fq> = Lazy::new(|| (*ZETA).pow(*M));

// Choice of W in the square root algorithm.
pub static SQRT_W: u32 = 8;

// Canonical basepoint projective coordinates
pub static B_X: Lazy<Fq> = Lazy::new(|| {
    from_ark_fq(ark_ff::MontFp!(
        "4959445789346820725352484487855828915252512307947624787834978378872129235627"
    ))
});
pub static B_Y: Lazy<Fq> = Lazy::new(|| {
    from_ark_fq(ark_ff::MontFp!(
        "6060471950081851567114691557659790004756535011754163002297540472747064943288"
    ))
});
pub static B_T: Lazy<Fq> = Lazy::new(|| {
    from_ark_fq(ark_ff::MontFp!(
        "7709528722369014828560854854815397945854484030754980890329689855465844419067"
    ))
});
pub static B_Z: Lazy<Fq> = Lazy::new(|| from_ark_fq(ark_ff::MontFp!("1")));

// Canonical basepoint affine coordinates
pub const GENERATOR_X: Fq = Fq::from_montgomery_limbs_64([
    5825153684096051627,
    16988948339439369204,
    186539475124256708,
    1230075515893193738,
]);
pub const GENERATOR_Y: Fq = Fq::from_montgomery_limbs_64([
    9786171649960077610,
    13527783345193426398,
    10983305067350511165,
    1251302644532346138,
]);

// Modulus of basefield
pub static R: Lazy<Fr> = Lazy::new(|| {
    from_ark_fr(ark_ff::MontFp!(
        "2111115437357092606062206234695386632838870926408408195193685246394721360383"
    ))
});
