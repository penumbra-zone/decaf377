#![allow(non_snake_case)]
use ark_ec::twisted_edwards::TECurveConfig;

use crate::element::{Decaf377EdwardsConfig, EdwardsProjective};

use crate::{
    constants::{ONE, TWO, ZETA},
    sign::Sign,
    Element, Fq, OnCurve,
};

impl Element {
    /// Elligator 2 map to decaf377 point
    fn elligator_map(r_0: &Fq) -> Element {
        // Ref: `Decaf_1_1_Point.elligator` (optimized) in `ristretto.sage`
        let A = Decaf377EdwardsConfig::COEFF_A;
        let D = Decaf377EdwardsConfig::COEFF_D;

        let r = *ZETA * r_0.square();

        let den = (D * r - (D - A)) * ((D - A) * r - D);
        let num = (r + *ONE) * (A - *TWO * D);

        let x = num * den;
        let (iss, mut isri) = Fq::sqrt_ratio_zeta(&ONE, &x);

        let sgn;
        let twiddle;
        if iss {
            sgn = *ONE;
            twiddle = *ONE;
        } else {
            sgn = -(*ONE);
            twiddle = *r_0;
        }

        isri *= twiddle;

        let mut s = isri * num;
        let t = -(sgn) * isri * s * (r - *ONE) * (A - *TWO * D).square() - *ONE;

        if s.is_negative() == iss {
            s = -s
        }

        // Convert point to extended projective (X : Y : Z : T)
        let E = *TWO * s;
        let F = *ONE + Decaf377EdwardsConfig::COEFF_A * s.square();
        let G = *ONE - Decaf377EdwardsConfig::COEFF_A * s.square();
        let H = t;
        let result = Element {
            inner: EdwardsProjective::new(E * H, F * G, E * G, F * H),
        };

        debug_assert!(
            result.inner.is_on_curve(),
            "resulting point must be on the curve",
        );

        result
    }

    /// Maps two field elements to a uniformly distributed decaf377 `Element`.
    ///
    /// The two field elements provided as inputs should be independently chosen.
    pub fn hash_to_curve(r_1: &Fq, r_2: &Fq) -> Element {
        let R_1 = Element::elligator_map(r_1);
        let R_2 = Element::elligator_map(r_2);
        &R_1 + &R_2
    }

    /// Maps a field element to a decaf377 `Element` suitable for CDH challenges.
    pub fn encode_to_curve(r: &Fq) -> Element {
        Element::elligator_map(r)
    }
}

#[cfg(test)]
mod tests {
    use crate::element::EdwardsAffine;

    use super::*;

    #[test]
    fn test_elligator() {
        // These are the test cases from testElligatorDeterministic in ristretto.sage
        let inputs = [
            [
                221, 101, 215, 58, 170, 229, 36, 124, 172, 234, 94, 214, 186, 163, 242, 30, 65,
                123, 76, 74, 56, 60, 24, 213, 240, 137, 49, 189, 138, 39, 90, 6,
            ],
            [
                23, 203, 214, 51, 26, 149, 7, 160, 228, 239, 208, 147, 124, 109, 75, 72, 64, 16,
                64, 215, 53, 185, 249, 168, 188, 49, 22, 194, 118, 7, 242, 16,
            ],
            [
                177, 123, 90, 180, 115, 7, 108, 183, 161, 167, 24, 15, 248, 218, 206, 227, 76, 137,
                162, 187, 148, 174, 66, 44, 205, 1, 211, 91, 140, 50, 144, 1,
            ],
            [
                204, 225, 121, 228, 145, 30, 86, 208, 132, 242, 203, 9, 153, 90, 195, 150, 215, 49,
                166, 70, 78, 68, 47, 98, 30, 130, 115, 139, 168, 242, 238, 8,
            ],
            [
                59, 150, 40, 159, 229, 96, 201, 47, 170, 163, 9, 208, 205, 201, 112, 241, 179, 82,
                198, 79, 207, 160, 184, 245, 63, 189, 101, 115, 217, 228, 74, 13,
            ],
            [
                74, 159, 227, 190, 73, 213, 131, 200, 50, 102, 249, 230, 48, 103, 85, 168, 239,
                149, 7, 164, 12, 42, 217, 177, 189, 97, 214, 98, 102, 73, 10, 16,
            ],
            [
                183, 227, 227, 192, 119, 10, 155, 143, 64, 60, 249, 165, 240, 39, 31, 197, 159,
                121, 64, 82, 10, 1, 34, 35, 121, 34, 146, 69, 226, 196, 156, 14,
            ],
            [
                61, 21, 56, 224, 11, 181, 71, 186, 238, 126, 234, 240, 14, 168, 75, 73, 251, 111,
                175, 85, 108, 9, 77, 2, 88, 249, 24, 235, 53, 96, 51, 15,
            ],
        ];

        let expected_xy_coordinates = [
            [
                ark_ff::MontFp!(
                    "1267955849280145133999011095767946180059440909377398529682813961428156596086"
                ),
                ark_ff::MontFp!(
                    "5356565093348124788258444273601808083900527100008973995409157974880178412098"
                ),
            ],
            [
                ark_ff::MontFp!(
                    "1502379126429822955521756759528876454108853047288874182661923263559139887582"
                ),
                ark_ff::MontFp!(
                    "7074060208122316523843780248565740332109149189893811936352820920606931717751"
                ),
            ],
            [
                ark_ff::MontFp!(
                    "2943006201157313879823661217587757631000260143892726691725524748591717287835"
                ),
                ark_ff::MontFp!(
                    "4988568968545687084099497807398918406354768651099165603393269329811556860241"
                ),
            ],
            [
                ark_ff::MontFp!(
                    "2893226299356126359042735859950249532894422276065676168505232431940642875576"
                ),
                ark_ff::MontFp!(
                    "5540423804567408742733533031617546054084724133604190833318816134173899774745"
                ),
            ],
            [
                ark_ff::MontFp!(
                    "2950911977149336430054248283274523588551527495862004038190631992225597951816"
                ),
                ark_ff::MontFp!(
                    "4487595759841081228081250163499667279979722963517149877172642608282938805393"
                ),
            ],
            [
                ark_ff::MontFp!(
                    "3318574188155535806336376903248065799756521242795466350457330678746659358665"
                ),
                ark_ff::MontFp!(
                    "7706453242502782485686954136003233626318476373744684895503194201695334921001"
                ),
            ],
            [
                ark_ff::MontFp!(
                    "3753408652523927772367064460787503971543824818235418436841486337042861871179"
                ),
                ark_ff::MontFp!(
                    "2820605049615187268236268737743168629279853653807906481532750947771625104256"
                ),
            ],
            [
                ark_ff::MontFp!(
                    "7803875556376973796629423752730968724982795310878526731231718944925551226171"
                ),
                ark_ff::MontFp!(
                    "7033839813997913565841973681083930410776455889380940679209912201081069572111"
                ),
            ],
        ];

        use ark_serialize::CanonicalDeserialize;

        for (ind, input) in inputs.iter().enumerate() {
            let input_element =
                Fq::deserialize_compressed(&input[..]).expect("encoding of test vector is valid");

            let expected: Element = Element {
                inner: EdwardsAffine::new(
                    crate::constants::from_ark_fq(expected_xy_coordinates[ind][0]),
                    crate::constants::from_ark_fq(expected_xy_coordinates[ind][1]),
                )
                .into(),
            };

            let actual = Element::elligator_map(&input_element);

            assert_eq!(actual, expected);
        }
    }
}
