use core::{ops::{Add, Mul, Neg, Sub}, marker::PhantomData};

use super::fiat::{self, FpMontgomeryDomainFieldElement};
use ark_ff::{BigInt, SqrtPrecomputation};
use ark_std::{
    hash::Hash,
};
use derivative::Derivative;

#[derive(Copy, Clone)]
pub struct Fp(FpMontgomeryDomainFieldElement);
    
pub trait FpTrait: Send + Sync + 'static + Sized {
    // fn from_bytes(bytes: &[u8; 48]) -> Self;
    // fn to_bytes(&self) -> [u8; 48];
    // fn zero() -> Self;
    // fn one() -> Self;
    // fn square(&self) -> Self;

    /// The modulus of the field.
    const MODULUS: BigInt<6>;

    /// A multiplicative generator of the field.
    /// `Self::GENERATOR` is an element having multiplicative order
    /// `Self::MODULUS - 1`.
    const GENERATOR: Fp;

    /// Additive identity of the field, i.e. the element `e`
    /// such that, for all elements `f` of the field, `e + f = f`.
    const ZERO: Fp;

    /// Multiplicative identity of the field, i.e. the element `e`
    /// such that, for all elements `f` of the field, `e * f = f`.
    const ONE: Fp;

    /// Let `N` be the size of the multiplicative group defined by the field.
    /// Then `TWO_ADICITY` is the two-adicity of `N`, i.e. the integer `s`
    /// such that `N = 2^s * t` for some odd integer `t`.
    const TWO_ADICITY: u32;

    /// 2^s root of unity computed by GENERATOR^t
    const TWO_ADIC_ROOT_OF_UNITY: Fp;

    /// An integer `b` such that there exists a multiplicative subgroup
    /// of size `b^k` for some integer `k`.
    const SMALL_SUBGROUP_BASE: Option<u32> = None;

    /// The integer `k` such that there exists a multiplicative subgroup
    /// of size `Self::SMALL_SUBGROUP_BASE^k`.
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = None;

    /// GENERATOR^((MODULUS-1) / (2^s *
    /// SMALL_SUBGROUP_BASE^SMALL_SUBGROUP_BASE_ADICITY)) Used for mixed-radix
    /// FFT.
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Fp> = None;

    // Precomputed material for use when computing square roots.
    // Currently uses the generic Tonelli-Shanks,
    // which works for every modulus.
    const SQRT_PRECOMP: Option<SqrtPrecomputation<Fp>>;

    /// Set a += b.
    fn add_assign(self, other: Fp) -> Fp;

    /// Set a -= b.
    fn sub_assign(self, other: Fp) -> Fp;

    /// Set a = a + a.
    fn double_in_place(a: &mut Fp);

    /// Set a = -a;
    fn neg_in_place(self) -> Fp;

    /// Set a *= b.
    fn mul_assign(self, other: Fp) -> Fp;

    /// Compute the inner product `<a, b>`.
    fn sum_of_products<const T: usize>(a: &[Fp; T], b: &[Fp; T]) -> Fp;

    /// Set a *= b.
    fn square_in_place(&self) -> Self;

    /// Compute a^{-1} if `a` is not zero.
    fn inverse(a: &Fp) -> Option<Fp>;

    /// Construct a field element from an integer in the range
    /// `0..(Self::MODULUS - 1)`. Returns `None` if the integer is outside
    /// this range.
    fn from_bigint(other: BigInt<6>) -> Option<Fp>;

    /// Convert a field element to an integer in the range `0..(Self::MODULUS -
    /// 1)`.
    fn into_bigint(other: Fp) -> BigInt<6>;

    fn from_bytes(bytes: &[u8; 48]) -> Self;

    fn to_bytes(&self) -> [u8; 48];

    fn zero() -> Self;

    fn one() -> Self;
}

impl FpTrait for Fp {
    const MODULUS: BigInt<6> = ark_ff::BigInt([0; 6]);
    const GENERATOR: Fp = Fp(FpMontgomeryDomainFieldElement([0; 6]));
    const ZERO: Fp = Fp(FpMontgomeryDomainFieldElement([0; 6]));
    const ONE: Fp = Fp(FpMontgomeryDomainFieldElement([0; 6]));
    const TWO_ADICITY: u32 = 0;
    const TWO_ADIC_ROOT_OF_UNITY: Fp = Fp(FpMontgomeryDomainFieldElement([0; 6]));
    const SMALL_SUBGROUP_BASE: Option<u32> = None;
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = None;
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Fp> = None;
    const SQRT_PRECOMP: Option<SqrtPrecomputation<Fp>> = None;

    fn add_assign(self, other: Fp) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; 6]);
        fiat::fp_add(&mut result, &self.0, &other.0);
        Fp(result)
    }

    fn sub_assign(self, other: Fp) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; 6]);
        fiat::fp_sub(&mut result, &self.0, &other.0);
        Fp(result)
    }

    fn double_in_place(a: &mut Fp) {
        unimplemented!()
    }

    fn neg_in_place(self) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; 6]);
        fiat::fp_opp(&mut result, &self.0);
        Fp(result)
    }

    fn mul_assign(self, other: Fp) -> Fp {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; 6]);
        fiat::fp_mul(&mut result, &self.0, &other.0);
        Fp(result)
    }

    fn sum_of_products<const T: usize>(a: &[Fp; T], b: &[Fp; T]) -> Fp {
        unimplemented!()
    }

    fn square_in_place(&self) -> Self {
        let mut result = fiat::FpMontgomeryDomainFieldElement([0; 6]);
        fiat::fp_square(&mut result, &self.0);
        Self(result)
    }

    fn inverse(a: &Fp) -> Option<Fp> {
        unimplemented!()
    }

    fn from_bigint(other: BigInt<6>) -> Option<Fp> {
        todo!()
    }

    fn into_bigint(other: Fp) -> BigInt<6> {
        unimplemented!()
    }

    fn from_bytes(bytes: &[u8; 48]) -> Self {
        let mut x_non_montgomery = fiat::FpNonMontgomeryDomainFieldElement([0; 6]);
        let mut x = fiat::FpMontgomeryDomainFieldElement([0; 6]);

        fiat::fp_from_bytes(&mut x_non_montgomery.0, &bytes);
        fiat::fp_to_montgomery(&mut x, &x_non_montgomery);

        Self(x)
    }

    fn to_bytes(&self) -> [u8; 48] {
        let mut x_non_montgomery = fiat::FpNonMontgomeryDomainFieldElement([0; 6]);
        let mut bytes = [0u8; 48];

        fiat::fp_from_montgomery(&mut x_non_montgomery, &self.0);
        fiat::fp_to_bytes(&mut bytes, &x_non_montgomery.0);

        bytes
    }

    fn zero() -> Self {
        Self(fiat::FpMontgomeryDomainFieldElement([0; 6]))
    }

    fn one() -> Self {
        let mut one = Self::zero();
        fiat::fp_set_one(&mut one.0);
        one
    }
}