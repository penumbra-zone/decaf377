use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

use super::{
    super::{B, N_64, N_8},
    fiat,
};

const N: usize = N_64;

#[derive(Copy, Clone)]
pub struct Fq(pub fiat::FqMontgomeryDomainFieldElement);

impl PartialEq for Fq {
    fn eq(&self, other: &Self) -> bool {
        match (self.is_sentinel(), other.is_sentinel()) {
            (true, true) => true,
            (true, false) => false,
            (false, true) => false,
            (false, false) => {
                let sub = self.sub(other);
                let mut check_word = 0;
                fiat::fq_nonzero(&mut check_word, &sub.0 .0);
                check_word == 0
            }
        }
    }
}

impl Eq for Fq {}

impl zeroize::Zeroize for Fq {
    fn zeroize(&mut self) {
        self.0 .0.zeroize()
    }
}

impl Fq {
    pub fn from_le_limbs(limbs: [u64; N_64]) -> Fq {
        let x_non_monty = fiat::FqNonMontgomeryDomainFieldElement(limbs);
        let mut x = fiat::FqMontgomeryDomainFieldElement([0; N]);
        fiat::fq_to_montgomery(&mut x, &x_non_monty);
        Self(x)
    }

    pub(crate) fn from_raw_bytes(bytes: &[u8; N_8]) -> Fq {
        let mut x_non_montgomery = fiat::FqNonMontgomeryDomainFieldElement([0; N]);
        let mut x = fiat::FqMontgomeryDomainFieldElement([0; N]);

        fiat::fq_from_bytes(&mut x_non_montgomery.0, &bytes);
        fiat::fq_to_montgomery(&mut x, &x_non_montgomery);

        Self(x)
    }

    pub fn to_le_limbs(&self) -> [u64; N_64] {
        debug_assert!(!self.is_sentinel());

        let mut x_non_montgomery = fiat::FqNonMontgomeryDomainFieldElement([0; N]);
        fiat::fq_from_montgomery(&mut x_non_montgomery, &self.0);
        x_non_montgomery.0
    }

    pub fn to_bytes_le(&self) -> [u8; N_8] {
        debug_assert!(!self.is_sentinel());

        let mut bytes = [0u8; N_8];
        let mut x_non_montgomery = fiat::FqNonMontgomeryDomainFieldElement([0; N]);
        fiat::fq_from_montgomery(&mut x_non_montgomery, &self.0);
        fiat::fq_to_bytes(&mut bytes, &x_non_montgomery.0);
        bytes
    }

    pub const fn from_montgomery_limbs(limbs: [u64; N]) -> Fq {
        Self(fiat::FqMontgomeryDomainFieldElement(limbs))
    }

    pub const ZERO: Self = Self(fiat::FqMontgomeryDomainFieldElement([0; N]));

    pub const ONE: Self = Self(fiat::FqMontgomeryDomainFieldElement([
        9015221291577245683,
        8239323489949974514,
        1646089257421115374,
        958099254763297437,
    ]));

    /// A sentinel value which exists only to not be equal to any other field element.
    ///
    /// Operations involving this element are undefined.
    pub const SENTINEL: Self = Self::from_montgomery_limbs([u64::MAX; N_64]);

    fn is_sentinel(&self) -> bool {
        self.0 .0 == Self::SENTINEL.0 .0
    }

    pub fn square(&self) -> Fq {
        debug_assert!(!self.is_sentinel());

        let mut result = fiat::FqMontgomeryDomainFieldElement([0; N]);
        fiat::fq_square(&mut result, &self.0);
        Self(result)
    }

    pub fn inverse(&self) -> Option<Fq> {
        debug_assert!(!self.is_sentinel());

        if self == &Fq::ZERO {
            return None;
        }

        const I: usize = (49 * B + 57) / 17;

        let mut a = fiat::FqNonMontgomeryDomainFieldElement([0; N]);
        fiat::fq_from_montgomery(&mut a, &self.0);
        let mut d = 1;
        let mut f: [u64; N + 1] = [0u64; N + 1];
        fiat::fq_msat(&mut f);
        let mut g: [u64; N + 1] = [0u64; N + 1];
        let mut v: [u64; N] = [0u64; N];
        let mut r: [u64; N] = Fq::ONE.0 .0;
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
            fiat::fq_divstep(
                &mut out1, &mut out2, &mut out3, &mut out4, &mut out5, d, &f, &g, &v, &r,
            );
            fiat::fq_divstep(
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
            fiat::fq_divstep(
                &mut out1, &mut out2, &mut out3, &mut out4, &mut out5, d, &f, &g, &v, &r,
            );
            v = out4;
            f = out2;
        }

        let s = ((f[f.len() - 1] >> (64 - 1)) & 1) as u8;
        let mut neg = fiat::FqMontgomeryDomainFieldElement([0; N]);
        fiat::fq_opp(&mut neg, &fiat::FqMontgomeryDomainFieldElement(v));

        let mut v_prime: [u64; N] = [0u64; N];
        fiat::fq_selectznz(&mut v_prime, s, &v, &neg.0);

        let mut pre_comp: [u64; N] = [0u64; N];
        fiat::fq_divstep_precomp(&mut pre_comp);

        let mut result = fiat::FqMontgomeryDomainFieldElement([0; N]);
        fiat::fq_mul(
            &mut result,
            &fiat::FqMontgomeryDomainFieldElement(v_prime),
            &fiat::FqMontgomeryDomainFieldElement(pre_comp),
        );

        Some(Fq(result))
    }

    pub fn add(self, other: &Fq) -> Fq {
        debug_assert!(!self.is_sentinel() && !other.is_sentinel());

        let mut result = fiat::FqMontgomeryDomainFieldElement([0; N]);
        fiat::fq_add(&mut result, &self.0, &other.0);
        Fq(result)
    }

    pub fn sub(self, other: &Fq) -> Fq {
        debug_assert!(!self.is_sentinel() && !other.is_sentinel());

        let mut result = fiat::FqMontgomeryDomainFieldElement([0; N]);
        fiat::fq_sub(&mut result, &self.0, &other.0);
        Fq(result)
    }

    pub fn mul(self, other: &Fq) -> Fq {
        debug_assert!(!self.is_sentinel() && !other.is_sentinel());

        let mut result = fiat::FqMontgomeryDomainFieldElement([0; N]);
        fiat::fq_mul(&mut result, &self.0, &other.0);
        Fq(result)
    }

    pub fn neg(self) -> Fq {
        debug_assert!(!self.is_sentinel());

        let mut result = fiat::FqMontgomeryDomainFieldElement([0; N]);
        fiat::fq_opp(&mut result, &self.0);
        Fq(result)
    }
}

impl ConditionallySelectable for Fq {
    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        let mut out = [0u64; 4];
        for i in 0..4 {
            out[i] = u64::conditional_select(&a.0 .0[i], &b.0 .0[i], choice);
        }
        Self(fiat::FqMontgomeryDomainFieldElement(out))
    }
}

impl ConstantTimeEq for Fq {
    fn ct_eq(&self, other: &Fq) -> Choice {
        self.0 .0.ct_eq(&other.0 .0)
    }
}
