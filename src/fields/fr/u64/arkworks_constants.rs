use super::Fr;

pub const MODULUS_LIMBS: [u64; 4] = [13356249993388743167, 5950279507993463550, 10965441865914903552, 336320092672043349];

pub const MODULUS_MINUS_ONE_DIV_TWO_LIMBS: [u64; 4] = [6678124996694371583, 2975139753996731775, 14706092969812227584, 168160046336021674];

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

pub const QUADRATIC_NON_RESIDUE_TO_TRACE: Fr = Fr::from_montgomery_limbs([
    7563926049028936178,
    2688164645460651601,
    12112688591437172399,
    3177973240564633687,
    14764383749841851163,
    52487407124055189,
]);

pub const MULTIPLICATIVE_GENERATOR: Fr = Fr::from_montgomery_limbs([
    1580481994230331156,
    7393753505699199837,
    15893201093018099506,
    15064395564155502359,
    7595513421530309810,
    112614884009382239,
]);

pub const TWO_ADIC_ROOT_OF_UNITY: Fr = Fr::from_montgomery_limbs([
    16125954451488549662,
    8217881455460992412,
    2710394594754331350,
    15576616684900113046,
    13256804877427073124,
    71394035925664393,
]);
