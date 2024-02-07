use super::{
    super::{B, N_64, N_8},
    fiat,
};

const N: usize = N_64;

#[derive(Copy, Clone)]
pub struct Fp(pub fiat::FpMontgomeryDomainFieldElement);

impl PartialEq for Fp {
    fn eq(&self, other: &Self) -> bool {
        let sub = self.sub(other);
        let mut check_word = 0;
        fiat::fp_nonzero(&mut check_word, &sub.0 .0);
        check_word == 0
    }
}

impl Eq for Fp {}

impl zeroize::Zeroize for Fp {
    fn zeroize(&mut self) {
        self.0 .0.zeroize()
    }
}

impl Fp {
    pub fn from_le_limbs(limbs: [u64; N_64]) -> Fp {
        let x_non_monty = fiat::FpNonMontgomeryDomainFieldElement(limbs);
        let mut x = fiat::FpMontgomeryDomainFieldElement([0; N]);
        fiat::fp_to_montgomery(&mut x, &x_non_monty);
        Self(x)
    }

    pub(crate) fn from_raw_bytes(bytes: &[u8; N_8]) -> Fp {
        let mut x_non_montgomery = fiat::FpNonMontgomeryDomainFieldElement([0; N]);
        let mut x = fiat::FpMontgomeryDomainFieldElement([0; N]);

        fiat::fp_from_bytes(&mut x_non_montgomery.0, &bytes);
        fiat::fp_to_montgomery(&mut x, &x_non_montgomery);

        Self(x)
    }

    pub fn to_le_limbs(&self) -> [u64; N_64] {
        let mut x_non_montgomery = fiat::FpNonMontgomeryDomainFieldElement([0; N]);
        fiat::fp_from_montgomery(&mut x_non_montgomery, &self.0);
        x_non_montgomery.0
    }

    pub fn to_bytes_le(&self) -> [u8; N_8] {
        let mut bytes = [0u8; N_8];
        let mut x_non_montgomery = fiat::FpNonMontgomeryDomainFieldElement([0; N]);
        fiat::fp_from_montgomery(&mut x_non_montgomery, &self.0);
        fiat::fp_to_bytes(&mut bytes, &x_non_montgomery.0);
        bytes
    }

    pub const fn from_montgomery_limbs(limbs: [u64; N]) -> Fp {
        Self(fiat::FpMontgomeryDomainFieldElement(limbs))
    }

    pub const ZERO: Self = Self(fiat::FpMontgomeryDomainFieldElement([0; N]));

    pub const ONE: Self = Self(fiat::FpMontgomeryDomainFieldElement([
        202099033278250856,
        5854854902718660529,
        11492539364873682930,
        8885205928937022213,
        5545221690922665192,
        39800542322357402,
    ]));

    pub const MINUS_ONE: Self = Self(fiat::FpMontgomeryDomainFieldElement([
        9384023879812382873,
        14252412606051516495,
        9184438906438551565,
        11444845376683159689,
        8738795276227363922,
        81297770384137296,
    ]));

    pub const QUADRATIC_NON_RESIDUE: Self = Self(fiat::FpMontgomeryDomainFieldElement([
        18161750659790013178,
        10940260503947051403,
        2338003791965605956,
        14680817040264804354,
        841925479686732267,
        43193913801202386,
    ]));

    pub fn square(&self) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; N]);
        fiat::fp_square(&mut result, &self.0);
        Self(result)
    }

    pub fn inverse(&self) -> Option<Self> {
        if self == &Self::ZERO {
            return None;
        }

        const I: usize = (49 * B + 57) / 17;

        let mut a = fiat::FpNonMontgomeryDomainFieldElement([0; N]);
        fiat::fp_from_montgomery(&mut a, &self.0);
        let mut d = 1;
        let mut f: [u64; N + 1] = [0u64; N + 1];
        fiat::fp_msat(&mut f);
        let mut g: [u64; N + 1] = [0u64; N + 1];
        let mut v: [u64; N] = [0u64; N];
        let mut r: [u64; N] = Self::ONE.0 .0;
        let mut i = 0;
        let mut j = 0;

        while j < N {
            g[j] = a[j];
            j += 1;
        }

        let mut out1: u64 = 0;
        let mut out2: [u64; N + 1] = [0; N + 1];
        let mut out3: [u64; N + 1] = [0; N + 1];
        let mut out4: [u64; N] = [0; N];
        let mut out5: [u64; N] = [0; N];
        let mut out6: u64 = 0;
        let mut out7: [u64; N + 1] = [0; N + 1];
        let mut out8: [u64; N + 1] = [0; N + 1];
        let mut out9: [u64; N] = [0; N];
        let mut out10: [u64; N] = [0; N];

        while i < I - I % 2 {
            fiat::fp_divstep(
                &mut out1, &mut out2, &mut out3, &mut out4, &mut out5, d, &f, &g, &v, &r,
            );
            fiat::fp_divstep(
                &mut out6, &mut out7, &mut out8, &mut out9, &mut out10, out1, &out2, &out3, &out4,
                &out5,
            );
            d = out6;
            f = out7;
            g = out8;
            v = out9;
            r = out10;
            i += 2;
        }

        if I % 2 != 0 {
            fiat::fp_divstep(
                &mut out1, &mut out2, &mut out3, &mut out4, &mut out5, d, &f, &g, &v, &r,
            );
            v = out4;
            f = out2;
        }

        let s = ((f[f.len() - 1] >> (64 - 1)) & 1) as u8;
        let mut neg = fiat::FpMontgomeryDomainFieldElement([0; N]);
        fiat::fp_opp(&mut neg, &fiat::FpMontgomeryDomainFieldElement(v));

        let mut v_prime: [u64; N] = [0u64; N];
        fiat::fp_selectznz(&mut v_prime, s, &v, &neg.0);

        let mut pre_comp: [u64; N] = [0u64; N];
        fiat::fp_divstep_precomp(&mut pre_comp);

        let mut result = fiat::FpMontgomeryDomainFieldElement([0; N]);
        fiat::fp_mul(
            &mut result,
            &fiat::FpMontgomeryDomainFieldElement(v_prime),
            &fiat::FpMontgomeryDomainFieldElement(pre_comp),
        );

        Some(Fp(result))
    }

    pub fn add(self, other: &Fp) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; N]);
        fiat::fp_add(&mut result, &self.0, &other.0);
        Fp(result)
    }

    pub fn sub(self, other: &Fp) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; N]);
        fiat::fp_sub(&mut result, &self.0, &other.0);
        Fp(result)
    }

    pub fn mul(self, other: &Fp) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; N]);
        fiat::fp_mul(&mut result, &self.0, &other.0);
        Fp(result)
    }

    pub fn neg(self) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; N]);
        fiat::fp_opp(&mut result, &self.0);
        Fp(result)
    }
}
