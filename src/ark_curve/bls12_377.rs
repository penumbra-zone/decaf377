use crate::fields::{fp::Fp, fq::Fq};
use ark_ec::{
    bls12::{Bls12, Bls12Config, TwistType},
    models::short_weierstrass::SWCurveConfig,
    models::CurveConfig,
    short_weierstrass::Affine,
};
use ark_ff::{
    fields::models::fp2::Fp2Config, AdditiveGroup, Field, Fp12Config, Fp2, Fp6, Fp6Config,
};

pub struct F2Config;

impl Fp2Config for F2Config {
    type Fp = Fp;

    const NONRESIDUE: Fp = Fp::QUADRATIC_NON_RESIDUE;

    const FROBENIUS_COEFF_FP2_C1: &'static [Fp] = &[Fp::ONE, Fp::MINUS_ONE];
}

#[derive(Debug, Clone, Copy)]
pub struct F6Config;

impl Fp6Config for F6Config {
    type Fp2Config = F2Config;

    const NONRESIDUE: Fp2<Self::Fp2Config> = Fp2::new(Fp::ZERO, Fp::ONE);

    const FROBENIUS_COEFF_FP6_C1: &'static [Fp2<Self::Fp2Config>] = &[
        Fp2::new(Fp::ONE, Fp::ZERO),
        Fp2::new(
            Fp::from_montgomery_limbs([
                6382252053795993818,
                1383562296554596171,
                11197251941974877903,
                6684509567199238270,
                6699184357838251020,
                19987743694136192,
            ]),
            Fp::ZERO,
        ),
        Fp2::new(
            Fp::from_montgomery_limbs([
                15766275933608376691,
                15635974902606112666,
                1934946774703877852,
                18129354943882397960,
                15437979634065614942,
                101285514078273488,
            ]),
            Fp::ZERO,
        ),
        Fp2::new(Fp::MINUS_ONE, Fp::ZERO),
        Fp2::new(
            Fp::from_montgomery_limbs([
                3203870859294639911,
                276961138506029237,
                9479726329337356593,
                13645541738420943632,
                7584832609311778094,
                101110569012358506,
            ]),
            Fp::ZERO,
        ),
        Fp2::new(
            Fp::from_montgomery_limbs([
                12266591053191808654,
                4471292606164064357,
                295287422898805027,
                2200696361737783943,
                17292781406793965788,
                19812798628221209,
            ]),
            Fp::ZERO,
        ),
    ];

    const FROBENIUS_COEFF_FP6_C2: &'static [Fp2<Self::Fp2Config>] = &[
        Fp2::new(Fp::ONE, Fp::ZERO),
        Fp2::new(
            Fp::from_montgomery_limbs([
                15766275933608376691,
                15635974902606112666,
                1934946774703877852,
                18129354943882397960,
                15437979634065614942,
                101285514078273488,
            ]),
            Fp::ZERO,
        ),
        Fp2::new(
            Fp::from_montgomery_limbs([
                3203870859294639911,
                276961138506029237,
                9479726329337356593,
                13645541738420943632,
                7584832609311778094,
                101110569012358506,
            ]),
            Fp::ZERO,
        ),
        Fp2::new(Fp::ONE, Fp::ZERO),
        Fp2::new(
            Fp::from_montgomery_limbs([
                15766275933608376691,
                15635974902606112666,
                1934946774703877852,
                18129354943882397960,
                15437979634065614942,
                101285514078273488,
            ]),
            Fp::ZERO,
        ),
        Fp2::new(
            Fp::from_montgomery_limbs([
                3203870859294639911,
                276961138506029237,
                9479726329337356593,
                13645541738420943632,
                7584832609311778094,
                101110569012358506,
            ]),
            Fp::ZERO,
        ),
    ];
}

#[derive(Debug, Clone, Copy)]
pub struct F12Config;

impl Fp12Config for F12Config {
    type Fp6Config = F6Config;

    const NONRESIDUE: Fp6<Self::Fp6Config> = Fp6::new(Fp2::ZERO, Fp2::ONE, Fp2::ZERO);

    const FROBENIUS_COEFF_FP12_C1: &'static [Fp2<F2Config>] = &[
        Fp2::new(Fp::ONE, Fp::ZERO),
        Fp2::new(
            Fp::from_montgomery_limbs([
                7981638599956744862,
                11830407261614897732,
                6308788297503259939,
                10596665404780565693,
                11693741422477421038,
                61545186993886319,
            ]),
            Fp::ZERO,
        ),
        Fp2::new(
            Fp::from_montgomery_limbs([
                6382252053795993818,
                1383562296554596171,
                11197251941974877903,
                6684509567199238270,
                6699184357838251020,
                19987743694136192,
            ]),
            Fp::ZERO,
        ),
        Fp2::new(
            Fp::from_montgomery_limbs([
                10965161018967488287,
                18251363109856037426,
                7036083669251591763,
                16109345360066746489,
                4679973768683352764,
                96952949334633821,
            ]),
            Fp::ZERO,
        ),
        Fp2::new(
            Fp::from_montgomery_limbs([
                15766275933608376691,
                15635974902606112666,
                1934946774703877852,
                18129354943882397960,
                15437979634065614942,
                101285514078273488,
            ]),
            Fp::ZERO,
        ),
        Fp2::new(
            Fp::from_montgomery_limbs([
                2983522419010743425,
                6420955848241139694,
                727295371748331824,
                5512679955286180796,
                11432976419915483342,
                35407762340747501,
            ]),
            Fp::ZERO,
        ),
        Fp2::new(Fp::MINUS_ONE, Fp::ZERO),
        Fp2::new(
            Fp::from_montgomery_limbs([
                1604484313133888867,
                8276860247155279292,
                14368189973808974556,
                9733385900839616209,
                2590275544672608076,
                59553125712608379,
            ]),
            Fp::ZERO,
        ),
        Fp2::new(
            Fp::from_montgomery_limbs([
                3203870859294639911,
                276961138506029237,
                9479726329337356593,
                13645541738420943632,
                7584832609311778094,
                101110569012358506,
            ]),
            Fp::ZERO,
        ),
        Fp2::new(
            Fp::from_montgomery_limbs([
                17067705967832697058,
                1855904398914139597,
                13640894602060642732,
                4220705945553435413,
                9604043198466676350,
                24145363371860877,
            ]),
            Fp::ZERO,
        ),
        Fp2::new(
            Fp::from_montgomery_limbs([
                12266591053191808654,
                4471292606164064357,
                295287422898805027,
                2200696361737783943,
                17292781406793965788,
                19812798628221209,
            ]),
            Fp::ZERO,
        ),
        Fp2::new(
            Fp::from_montgomery_limbs([
                6602600494079890304,
                13686311660529037330,
                1502938825854351055,
                14817371350334001107,
                2851040547234545772,
                85690550365747197,
            ]),
            Fp::ZERO,
        ),
    ];
}

pub struct OurG1Config;

impl CurveConfig for OurG1Config {
    type BaseField = Fp;

    type ScalarField = Fq;

    const COFACTOR: &'static [u64] = &[0x0, 0x170b5d4430000000];

    const COFACTOR_INV: Self::ScalarField = Fq::from_montgomery_limbs([
        2013239619100046060,
        4201184776506987597,
        2526766393982337036,
        1114629510922847535,
    ]);
}

const G1_GENERATOR_X: Fp = Fp::from_montgomery_limbs([
    2742467569752756724,
    14217256487979144792,
    6635299530028159197,
    8509097278468658840,
    14518893593143693938,
    46181716169194829,
]);

const G1_GENERATOR_Y: Fp = Fp::from_montgomery_limbs([
    9336971515457667571,
    28021381849722296,
    18085035374859187530,
    14013031479170682136,
    3369780711397861396,
    35370409237953649,
]);

impl SWCurveConfig for OurG1Config {
    const COEFF_A: Self::BaseField = Fp::ZERO;

    const COEFF_B: Self::BaseField = Fp::ONE;

    const GENERATOR: Affine<Self> = Affine::new_unchecked(G1_GENERATOR_X, G1_GENERATOR_Y);
}

pub struct OurG2Config;

impl CurveConfig for OurG2Config {
    type BaseField = Fp2<F2Config>;

    type ScalarField = Fq;

    const COFACTOR: &'static [u64] = &[
        0x0000000000000001,
        0x452217cc90000000,
        0xa0f3622fba094800,
        0xd693e8c36676bd09,
        0x8c505634fae2e189,
        0xfbb36b00e1dcc40c,
        0xddd88d99a6f6a829,
        0x26ba558ae9562a,
    ];

    const COFACTOR_INV: Self::ScalarField = Fq::from_montgomery_limbs([
        15499857013495546999,
        4613531467548868169,
        14546778081091178013,
        549402535258503313,
    ]);
}

pub const G2_GENERATOR_X: Fp2<F2Config> = Fp2::new(
    Fp::from_montgomery_limbs([
        7534593107747697243,
        7390176809662624395,
        16990527120569264207,
        2168572232730518502,
        9443417493680878057,
        109821976444144002,
    ]),
    Fp::from_montgomery_limbs([
        6846220294590070585,
        17925825951095956135,
        15355657819052935248,
        16808496983586309946,
        18438381910454061441,
        78904498268135389,
    ]),
);

pub const G2_GENERATOR_Y: Fp2<F2Config> = Fp2::new(
    Fp::from_montgomery_limbs([
        15398259615690998543,
        413927750809907693,
        6945668964135547374,
        3622202639115414553,
        11542235856284301842,
        111174645670174930,
    ]),
    Fp::from_montgomery_limbs([
        6296061721506977525,
        16832990956758385678,
        2538166719760928425,
        9449086974571632418,
        3122185334549858583,
        25052933797626130,
    ]),
);

impl SWCurveConfig for OurG2Config {
    const COEFF_A: Self::BaseField = Fp2::new(OurG1Config::COEFF_A, OurG1Config::COEFF_A);

    const COEFF_B: Self::BaseField = Fp2::new(
        Fp::ZERO,
        Fp::from_montgomery_limbs([
            9255502405446297221,
            10229180150694123945,
            9215585410771530959,
            13357015519562362907,
            5437107869987383107,
            16259554076827459,
        ]),
    );

    const GENERATOR: Affine<Self> = Affine::new_unchecked(G2_GENERATOR_X, G2_GENERATOR_Y);
}

/// A marker struct for our implementation of BLS12-377 over our backend fields, using Arkworks.
pub struct Config;

impl Bls12Config for Config {
    const X: &'static [u64] = &[0x8508c00000000001];
    /// `x` is positive
    const X_IS_NEGATIVE: bool = false;

    const TWIST_TYPE: TwistType = TwistType::D;

    type Fp = Fp;

    type Fp2Config = F2Config;

    type Fp6Config = F6Config;

    type Fp12Config = F12Config;

    type G1Config = OurG1Config;

    type G2Config = OurG2Config;
}

pub type Bls12_377 = Bls12<Config>;
