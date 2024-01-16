use super::fiat;

const B: usize = 377;
const N_64: usize = (B + 63) / 64;
const N_8: usize = (B + 7) / 8;
const N: usize = (B + 31) / 32;

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
        let limbs = {
            let mut out = [0u32; N];
            for i in 0..N_64 {
                out[2 * i] = (limbs[i] & 0xFFFF_FFFF_FFFF_FFFF) as u32;
                out[2 * i + 1] = (limbs[i] >> 32) as u32;
            }
            out
        };
        let x_non_monty = fiat::FpNonMontgomeryDomainFieldElement(limbs);
        let mut x = fiat::FpMontgomeryDomainFieldElement([0; N]);
        fiat::fp_to_montgomery(&mut x, &x_non_monty);
        Self(x)
    }

    pub fn from_raw_bytes(bytes: &[u8; N_8]) -> Fp {
        let mut x_non_montgomery = fiat::FpNonMontgomeryDomainFieldElement([0; N]);
        let mut x = fiat::FpMontgomeryDomainFieldElement([0; N]);

        fiat::fp_from_bytes(&mut x_non_montgomery.0, &bytes);
        fiat::fp_to_montgomery(&mut x, &x_non_montgomery);

        Self(x)
    }

    pub fn to_le_limbs(&self) -> [u64; N_64] {
        let mut x_non_montgomery = fiat::FpNonMontgomeryDomainFieldElement([0; N]);
        fiat::fp_from_montgomery(&mut x_non_montgomery, &self.0);
        let limbs = x_non_montgomery.0;
        let mut out = [0u64; N_64];
        for i in 0..N_64 {
            out[i] = (limbs[2 * i] as u64) | ((limbs[2 * i + 1] as u64) << 32);
        }
        out
    }

    pub fn to_bytes_le(&self) -> [u8; N_8] {
        let mut bytes = [0u8; N_8];
        let mut x_non_montgomery = fiat::FpNonMontgomeryDomainFieldElement([0; N]);
        fiat::fp_from_montgomery(&mut x_non_montgomery, &self.0);
        fiat::fp_to_bytes(&mut bytes, &x_non_montgomery.0);
        bytes
    }

    pub const fn from_montgomery_limbs(limbs: [u32; N]) -> Fp {
        Self(fiat::FpMontgomeryDomainFieldElement(limbs))
    }

    pub const fn from_montgomery_limbs_64(limbs: [u64; N_64]) -> Fp {
        Self(fiat::FpMontgomeryDomainFieldElement([
            limbs[0] as u32,
            (limbs[0] >> 32) as u32,
            limbs[1] as u32,
            (limbs[1] >> 32) as u32,
            limbs[2] as u32,
            (limbs[2] >> 32) as u32,
            limbs[3] as u32,
            (limbs[3] >> 32) as u32,
            limbs[4] as u32,
            (limbs[4] >> 32) as u32,
            limbs[5] as u32,
            (limbs[5] >> 32) as u32,
        ]))
    }

    pub const fn zero() -> Fp {
        Self(fiat::FpMontgomeryDomainFieldElement([0; N]))
    }

    pub const fn one() -> Self {
        Self(fiat::FpMontgomeryDomainFieldElement([
            4294967144, 47054847, 2147483569, 1363189635, 2323464178, 2675815337, 1853645573,
            2068748215, 2151449832, 1291097535, 3808294042, 9266785,
        ]))
    }

    pub const fn quadratic_non_residue() -> Fp {
        Self(fiat::FpMontgomeryDomainFieldElement([
            762, 4228612096, 3758096779, 2547227894, 3214954564, 544358927, 3648796674, 3418144080,
            1477704171, 196026051, 3230948050, 10056866,
        ]))
    }

    pub const fn minus_one() -> Self {
        Self(fiat::FpMontgomeryDomainFieldElement([
            153, 2184888320, 2952790095, 3318398400, 797706253, 2138418822, 2457383049, 2664710715,
            3966026834, 2034659328, 885464144, 18928612,
        ]))
    }

    pub fn square(&self) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; N]);
        fiat::fp_square(&mut result, &self.0);
        Self(result)
    }

    pub fn inverse(&self) -> Option<Fp> {
        if self == &Fp::zero() {
            return None;
        }

        const I: usize = (49 * B + 57) / 17;

        let mut a = fiat::FpNonMontgomeryDomainFieldElement([0; N]);
        fiat::fp_from_montgomery(&mut a, &self.0);
        let mut d = 1;
        let mut f: [u32; N + 1] = [0u32; N + 1];
        fiat::fp_msat(&mut f);
        let mut g: [u32; N + 1] = [0u32; N + 1];
        let mut v: [u32; N] = [0u32; N];
        let mut r: [u32; N] = Fp::one().0 .0;
        let mut i = 0;
        let mut j = 0;

        while j < N {
            g[j] = a[j];
            j += 1;
        }

        let mut out1: u32 = 0;
        let mut out2: [u32; N + 1] = [0; N + 1];
        let mut out3: [u32; N + 1] = [0; N + 1];
        let mut out4: [u32; N] = [0; N];
        let mut out5: [u32; N] = [0; N];
        let mut out6: u32 = 0;
        let mut out7: [u32; N + 1] = [0; N + 1];
        let mut out8: [u32; N + 1] = [0; N + 1];
        let mut out9: [u32; N] = [0; N];
        let mut out10: [u32; N] = [0; N];

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

        let s = ((f[f.len() - 1] >> (32 - 1)) & 1) as u8;
        let mut neg = fiat::FpMontgomeryDomainFieldElement([0; N]);
        fiat::fp_opp(&mut neg, &fiat::FpMontgomeryDomainFieldElement(v));

        let mut v_prime: [u32; N] = [0u32; N];
        fiat::fp_selectznz(&mut v_prime, s, &v, &neg.0);

        let mut pre_comp: [u32; N] = [0u32; N];
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
