use super::Fp;

pub const MODULUS_LIMBS: [u64; 6] = [
    9586122913090633729,
    1660523435060625408,
    2230234197602682880,
    1883307231910630287,
    14284016967150029115,
    121098312706494698,
];

pub const MODULUS_MINUS_ONE_DIV_TWO_LIMBS: [u64; 6] = [
    4793061456545316864,
    830261717530312704,
    10338489135656117248,
    10165025652810090951,
    7142008483575014557,
    60549156353247349,
];

pub const MODULUS_BIT_SIZE: u32 = 0x179;

pub const TRACE_LIMBS: [u64; 6] = [
    8435453208297608227,
    9853568280881552429,
    7479357291536088013,
    1657802422768920715,
    16796279350917535980,
    1720,
];

pub const TRACE_MINUS_ONE_DIV_TWO_LIMBS: [u64; 6] = [
    13441098641003579921,
    14150156177295552022,
    12963050682622819814,
    828901211384460357,
    8398139675458767990,
    860,
];

pub const TWO_ADICITY: u32 = 0x2e;

pub const QUADRATIC_NON_RESIDUE_TO_TRACE: Fp = Fp::from_montgomery_limbs([
    2343670258, 1761113770, 2792500817, 625887104, 529141423, 2820205081, 495800407, 739929555,
    2699006747, 3437600971, 3369043093, 12220676,
]);

pub const MULTIPLICATIVE_GENERATOR: Fp = Fp::from_montgomery_limbs([
    4294965012, 367984639, 3221224285, 1721492387, 892444466, 3700424240, 1970634519, 3507452915,
    3506873522, 1768468278, 3989639519, 26220195,
]);

pub const TWO_ADIC_ROOT_OF_UNITY: Fp = Fp::from_montgomery_limbs([
    2031790878, 3754616354, 3204826524, 1913374628, 226001622, 631062918, 2984565398, 3626713688,
    1739907172, 3086590412, 1450066569, 16622719,
]);