use super::super::u64::{fiat, wrapper::Fp};
use ark_ff::FftField;
use ark_ff::{BigInt, Field, PrimeField, SqrtPrecomputation};
use ark_serialize::{
    CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, Compress, Flags, SerializationError, Valid, Validate,
};
use ark_std::{rand, str::FromStr, One, Zero};
use core::hash::Hash;
use core::{
    cmp::Ordering,
    fmt::{Display, Formatter},
    iter,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

impl PrimeField for Fr {
    /// A `BigInteger` type that can represent elements of this field.
    type BigInt = BigInt<4>;

    /// The Decaf377 scalar field modulus `r` (2111115437357092606062206234695386632838870926408408195193685246394721360383)
    const MODULUS: Self::BigInt = ark_ff::BigInt([
        13356249993388743167,
        5950279507993463550,
        10965441865914903552,
        336320092672043349,
    ]);

    /// The value `(p - 1)/ 2`.
    const MODULUS_MINUS_ONE_DIV_TWO: Self::BigInt = ark_ff::BigInt([
        6678124996694371583,
        2975139753996731775,
        14706092969812227584,
        168160046336021674,
    ]);

    /// The size of the modulus in bits.
    const MODULUS_BIT_SIZE: u32 = 251;

    /// The trace of the field is defined as the smallest integer `t` such that by
    /// `2^s * t = p - 1`, and `t` is coprime to 2.
    const TRACE: Self::BigInt = ark_ff::BigInt([
        6678124996694371583,
        2975139753996731775,
        14706092969812227584,
        168160046336021674,
    ]);

    /// The value `(t - 1)/ 2`.
    const TRACE_MINUS_ONE_DIV_TWO: Self::BigInt = ark_ff::BigInt([
        12562434535201961599,
        1487569876998365887,
        7353046484906113792,
        84080023168010837,
    ]);

    fn from_bigint(repr: Self::BigInt) -> Option<Self> {
        if repr >= Fr::MODULUS {
            None
        } else {
            Some(Fr(fiat::FrMontgomeryDomainFieldElement(repr.0)))
        }
    }

    fn into_bigint(self) -> Self::BigInt {
        BigInt(self.0 .0)
    }

    fn from_be_bytes_mod_order(bytes: &[u8]) -> Self {
        let mut bytes_copy = bytes.to_vec();
        bytes_copy.reverse();
        Self::from_le_bytes_mod_order(&bytes_copy)
    }

    fn from_le_bytes_mod_order(bytes: &[u8]) -> Self {
        assert!(bytes.len() == 32);

        let mut t = [0u8; 32];
        t.copy_from_slice(&bytes[..32]);
        let modulus_field_montgomery = Fr::from_bytes(&t);

        modulus_field_montgomery
    }
}

impl Field for Fr {
    type BasePrimeField = Self;
    type BasePrimeFieldIter = iter::Once<Self::BasePrimeField>;

    const SQRT_PRECOMP: Option<SqrtPrecomputation<Self>> =
        Some(SqrtPrecomputation::TonelliShanks {
            two_adicity: 1,
            quadratic_nonresidue_to_trace: Fr(fiat::FrMontgomeryDomainFieldElement([
                13356249993388743166,
                5950279507993463550,
                10965441865914903552,
                336320092672043349,
            ])),
            trace_of_modulus_minus_one_div_two: &[
                12562434535201961599,
                1487569876998365887,
                7353046484906113792,
                84080023168010837,
            ],
        });

    const ZERO: Self = Fr(fiat::FrMontgomeryDomainFieldElement([0, 0, 0, 0]));

    const ONE: Self = Fr(fiat::FrMontgomeryDomainFieldElement([
        16632263305389933622,
        10726299895124897348,
        16608693673010411502,
        285459069419210737,
    ]));

    fn extension_degree() -> u64 {
        1
    }

    fn to_base_prime_field_elements(&self) -> Self::BasePrimeFieldIter {
        iter::once(*self)
    }

    fn from_base_prime_field_elems(elems: &[Self::BasePrimeField]) -> Option<Self> {
        if elems.len() != (Self::extension_degree() as usize) {
            return None;
        }
        Some(elems[0])
    }

    fn from_base_prime_field(elem: Self::BasePrimeField) -> Self {
        elem
    }

    fn double(&self) -> Self {
        self.add(*self)
    }

    fn double_in_place(&mut self) -> &mut Self {
        *self = self.add(*self);
        self
    }

    fn neg_in_place(&mut self) -> &mut Self {
        *self = self.add(*self);
        self
    }

    fn from_random_bytes_with_flags<F: ark_serialize::Flags>(bytes: &[u8]) -> Option<(Self, F)> {
        Some((Self::from_le_bytes_mod_order(bytes), F::default()))
    }

    fn legendre(&self) -> ark_ff::LegendreSymbol {
        unimplemented!()
    }

    fn square(&self) -> Self {
        self.square()
    }

    fn square_in_place(&mut self) -> &mut Self {
        *self = self.square();
        self
    }

    fn inverse(&self) -> Option<Self> {
        self.inverse()
    }

    fn inverse_in_place(&mut self) -> Option<&mut Self> {
        if let Some(inverse) = self.inverse() {
            *self = inverse;
            Some(self)
        } else {
            None
        }
    }

    fn frobenius_map_in_place(&mut self, _power: usize) {
        // Because this is a prime field, we don't need to do anything,
        // the automorphism is trivial.
    }
}

impl FftField for Fr {
    const GENERATOR: Self = Fr(fiat::FrMontgomeryDomainFieldElement([8, 0, 0, 0]));
    const TWO_ADICITY: u32 = 1;
    const TWO_ADIC_ROOT_OF_UNITY: Self = unimplemented!();
    const SMALL_SUBGROUP_BASE: Option<u32> = None;
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = None;
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Self> = None;
}

impl From<u128> for Fr {
    fn from(mut other: u128) -> Self {
        let mut result = BigInt::default();
        result.0[0] = ((other << 64) >> 64) as u64;
        result.0[1] = (other >> 64) as u64;
        Self::from_bigint(result).unwrap()
    }
}

impl From<u64> for Fr {
    fn from(other: u64) -> Self {
        Self::from_bigint(BigInt::from(other)).unwrap()
    }
}

impl From<u32> for Fr {
    fn from(other: u32) -> Self {
        Self::from_bigint(BigInt::from(other)).unwrap()
    }
}

impl From<u16> for Fr {
    fn from(other: u16) -> Self {
        Self::from_bigint(BigInt::from(other)).unwrap()
    }
}

impl From<u8> for Fr {
    fn from(other: u8) -> Self {
        Self::from_bigint(BigInt::from(other)).unwrap()
    }
}

impl From<bool> for Fr {
    fn from(other: bool) -> Self {
        Self::from_bigint(BigInt::from(u64::from(other))).unwrap()
    }
}

impl Neg for Fr {
    type Output = Self;

    #[inline]
    #[must_use]
    fn neg(mut self) -> Self {
        let neg = self.neg();
        neg
    }
}

impl<'a> AddAssign<&'a Self> for Fr {
    #[inline]
    fn add_assign(&mut self, other: &Self) {
        *self = self.add(*other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::AddAssign<Self> for Fr {
    #[inline(always)]
    fn add_assign(&mut self, other: Self) {
        *self = self.add(other);
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::AddAssign<&'a mut Self> for Fr {
    #[inline(always)]
    fn add_assign(&mut self, other: &'a mut Self) {
        *self = self.add(*other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::Add<Self> for Fr {
    type Output = Self;

    #[inline]
    fn add(mut self, other: Self) -> Self {
        self.add(other)
    }
}

impl<'a> Add<&'a Fr> for Fr {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &Self) -> Self {
        self.add(*other)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::Add<&'a mut Self> for Fr {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &'a mut Self) -> Self {
        self.add(*other)
    }
}

impl<'a> SubAssign<&'a Self> for Fr {
    #[inline]
    fn sub_assign(&mut self, other: &Self) {
        *self = self.sub(*other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::SubAssign<Self> for Fr {
    #[inline(always)]
    fn sub_assign(&mut self, other: Self) {
        *self = self.sub(other);
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::SubAssign<&'a mut Self> for Fr {
    #[inline(always)]
    fn sub_assign(&mut self, other: &'a mut Self) {
        *self = self.sub(*other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::Sub<Self> for Fr {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: Self) -> Self {
        self.sub(other)
    }
}

impl<'a> Sub<&'a Fr> for Fr {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: &Self) -> Self {
        self.sub(*other)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::Sub<&'a mut Self> for Fr {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: &'a mut Self) -> Self {
        self.sub(*other)
    }
}

impl<'a> MulAssign<&'a Self> for Fr {
    fn mul_assign(&mut self, other: &Self) {
        *self = self.mul(*other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::MulAssign<Self> for Fr {
    #[inline(always)]
    fn mul_assign(&mut self, other: Self) {
        *self = self.mul(other);
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::MulAssign<&'a mut Self> for Fr {
    #[inline(always)]
    fn mul_assign(&mut self, other: &'a mut Self) {
        *self = self.mul(*other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::Mul<Self> for Fr {
    type Output = Self;

    #[inline(always)]
    fn mul(mut self, other: Self) -> Self {
        self.mul(other)
    }
}

impl<'a> Mul<&'a Fr> for Fr {
    type Output = Self;

    #[inline]
    fn mul(mut self, other: &Self) -> Self {
        self.mul(*other)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::Mul<&'a mut Self> for Fr {
    type Output = Self;

    #[inline(always)]
    fn mul(mut self, other: &'a mut Self) -> Self {
        self.mul(*other)
    }
}

impl<'a> DivAssign<&'a Self> for Fr {
    #[inline(always)]
    fn div_assign(&mut self, other: &Self) {
        self.mul_assign(&other.inverse().unwrap());
    }
}

#[allow(unused_qualifications)]
impl core::ops::DivAssign<Self> for Fr {
    #[inline(always)]
    fn div_assign(&mut self, other: Self) {
        self.div_assign(&other)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::DivAssign<&'a mut Self> for Fr {
    #[inline(always)]
    fn div_assign(&mut self, other: &'a mut Self) {
        self.div_assign(&*other)
    }
}

#[allow(unused_qualifications)]
impl core::ops::Div<Self> for Fr {
    type Output = Self;

    #[inline(always)]
    fn div(mut self, other: Self) -> Self {
        self.div_assign(&other);
        self
    }
}

impl<'a> Div<&'a Fr> for Fr {
    type Output = Self;

    #[inline]
    fn div(mut self, other: &Self) -> Self {
        self.mul_assign(&other.inverse().unwrap());
        self
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::Div<&'a mut Self> for Fr {
    type Output = Self;

    #[inline(always)]
    fn div(mut self, other: &'a mut Self) -> Self {
        self.div_assign(&*other);
        self
    }
}

impl Zero for Fr {
    #[inline]
    fn zero() -> Self {
        Fr::ZERO
    }

    #[inline]
    fn is_zero(&self) -> bool {
        *self == Fr::ZERO
    }
}

#[allow(unused_qualifications)]
impl core::iter::Sum<Self> for Fr {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::iter::Sum<&'a Self> for Fr {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

impl One for Fr {
    #[inline]
    fn one() -> Self {
        Fr::ONE
    }

    #[inline]
    fn is_one(&self) -> bool {
        *self == Fr::ONE
    }
}

#[allow(unused_qualifications)]
impl core::iter::Product<Self> for Fr {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::one(), core::ops::Mul::mul)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::iter::Product<&'a Self> for Fr {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::one(), Mul::mul)
    }
}

impl CanonicalDeserializeWithFlags for Fr {
    fn deserialize_with_flags<R: ark_std::io::Read, F: Flags>(
        reader: R,
    ) -> Result<(Self, F), SerializationError> {
        unimplemented!()
    }
}

impl Valid for Fr {
    fn check(&self) -> Result<(), SerializationError> {
        unimplemented!()
    }
}

impl CanonicalDeserialize for Fr {
    fn deserialize_with_mode<R: ark_std::io::Read>(
        reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        unimplemented!()
    }
}

impl CanonicalSerialize for Fr {
    #[inline]
    fn serialize_with_mode<W: ark_std::io::Write>(
        &self,
        writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        unimplemented!()
    }

    #[inline]
    fn serialized_size(&self, _compress: Compress) -> usize {
        unimplemented!()
    }
}

impl CanonicalSerializeWithFlags for Fr {
    fn serialize_with_flags<W: ark_std::io::Write, F: Flags>(
        &self,
        writer: W,
        flags: F,
    ) -> Result<(), SerializationError> {
        unimplemented!()
    }

    fn serialized_size_with_flags<F: Flags>(&self) -> usize {
        unimplemented!()
    }
}

impl ark_std::rand::distributions::Distribution<Fr> for ark_std::rand::distributions::Standard {
    fn sample<R: rand::prelude::Rng + ?Sized>(&self, rng: &mut R) -> Fr {
        todo!()
    }
}

impl Display for Fr {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        unimplemented!()
    }
}

impl zeroize::Zeroize for Fr {
    fn zeroize(&mut self) {
        unimplemented!()
    }
}

impl Ord for Fr {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        self.into_bigint().cmp(&other.into_bigint())
    }
}

impl PartialOrd for Fr {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl FromStr for Fr {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        unimplemented!()
    }
}

impl From<num_bigint::BigUint> for Fr {
    #[inline]
    fn from(val: num_bigint::BigUint) -> Fr {
        Fr::from_le_bytes_mod_order(&val.to_bytes_le())
    }
}

impl From<Fr> for num_bigint::BigUint {
    #[inline(always)]
    fn from(other: Fr) -> Self {
        other.into_bigint().into()
    }
}

impl From<Fr> for BigInt<4> {
    #[inline(always)]
    fn from(fr: Fr) -> Self {
        fr.into_bigint()
    }
}

impl From<BigInt<4>> for Fr {
    /// Converts `Self::BigInteger` into `Self`
    #[inline(always)]
    fn from(int: BigInt<4>) -> Self {
        Fr(fiat::FrMontgomeryDomainFieldElement(int.0))
    }
}

impl Hash for Fr {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        unimplemented!()
    }
}

impl PartialEq for Fr {
    fn eq(&self, other: &Fr) -> bool {
        let self_bytes = self.to_bytes();
        let other_bytes = other.to_bytes();
        self_bytes[..] == other_bytes[..]
    }
}

impl Eq for Fr {}

impl Default for Fr {
    fn default() -> Self {
        Fr(fiat::FrMontgomeryDomainFieldElement([0, 0, 0, 0]))
    }
}

impl core::fmt::Debug for Fr {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let bytes = self.to_bytes();
        write!(f, "Fr(0x{})", hex::encode(bytes))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    prop_compose! {
        fn arb_bls377()(
            z0 in 0..u64::MAX,
            z1 in 0..u64::MAX,
            z2 in 0..u64::MAX,
            z3 in 0..(1u64 << 61)
        ) -> [u64; 4] {
            [z0, z1, z2, z3]
        }
    }

    prop_compose! {
        fn arb_fr()(a in arb_bls377()) -> Fr {
            let a = fiat::FrNonMontgomeryDomainFieldElement(a);

            let mut a_to_mont = fiat::FrMontgomeryDomainFieldElement([0; 4]);
            fiat::fr_to_montgomery(&mut a_to_mont, &a);

            Fr(a_to_mont)
        }
    }

    proptest! {
        #[test]
        fn test_addition_commutative(a in arb_fr(), b in arb_fr()) {
            assert_eq!(a + b, b + a);
        }
    }

    proptest! {
        #[test]
        fn test_addition_associative(a in arb_fr(), b in arb_fr(), c in arb_fr()) {
            assert_eq!(a + (b + c), (a + b) + c);
        }
    }

    proptest! {
        #[test]
        fn test_add_zero_identity(a in arb_fr()) {
            let zero = Fr::zero();

            assert_eq!(a + zero, a);
            assert_eq!(zero + a, a);
        }
    }

    proptest! {
        #[test]
        fn test_subtract_self_is_zero(a in arb_fr()) {
            let zero = Fr::zero();

            assert_eq!(a - a, zero);
        }
    }

    proptest! {
        #[test]
        fn test_doubling_is_just_addition(a in arb_fr()) {
            let two = fiat::FrNonMontgomeryDomainFieldElement([2, 0, 0, 0]);

            let mut two_to_mont = fiat::FrMontgomeryDomainFieldElement([0; 4]);
            fiat::fr_to_montgomery(&mut two_to_mont, &two);

            assert_eq!(Fr(two_to_mont) * a, a + a);
            assert_eq!(a.double(), a + a);
            assert_eq!(*(a.clone().double_in_place()), a + a);
        }
    }

    proptest! {
        #[test]
        fn test_adding_negation(a in arb_bls377()) {
            let a = Fr(fiat::FrMontgomeryDomainFieldElement(a));

            assert_eq!(a + -a, Fr::ZERO)
        }
    }

    proptest! {
        #[test]
        fn test_multiplication_commutative(a in arb_fr(), b in arb_fr()) {
            assert_eq!(a * b, b * a);
        }
    }

    proptest! {
        #[test]
        fn test_multiplication_associative(a in arb_fr(), b in arb_fr(), c in arb_fr()) {
            assert_eq!(a * (b * c), (a * b) * c);
        }
    }

    proptest! {
        #[test]
        fn test_multiplication_distributive(a in arb_fr(), b in arb_fr(), c in arb_fr()) {
            assert_eq!(a * (b + c), a * b + a * c);
        }
    }

    proptest! {
        #[test]
        fn test_multiply_one_identity(a in arb_fr()) {
            assert_eq!(a * Fr::ONE, a);
            assert_eq!(Fr::ONE * a, a);
        }
    }

    proptest! {
        #[test]
        fn test_multiply_minus_one_is_negation(a in arb_fr()) {
            let minus_one = -Fr::ONE;

            assert_eq!(a * minus_one, a.neg());
        }
    }

    proptest! {
        #[test]
        fn test_square_is_multiply(a in arb_fr()) {
            assert_eq!(a.square(), a * a);
            assert_eq!(*(a.clone().square_in_place()), a * a);
        }
    }

    proptest! {
        #[test]
        fn test_inverse(a in arb_fr()) {
            assert_eq!(a * a.inverse().unwrap(), Fr::ONE);
            assert_eq!(a * *(a.clone().inverse_in_place().unwrap()), Fr::ONE);
        }
    }

    proptest! {
        #[test]
        fn test_sqrt(a in arb_fr()) {
            match a.sqrt() {
                Some(x) => assert_eq!(x * x, a),
                None => {}
            }
        }
    }

    #[test]
    fn test_addition_examples() {
        let z1 = Fr(fiat::FrMontgomeryDomainFieldElement([1, 1, 1, 1]));
        let z2 = Fr(fiat::FrMontgomeryDomainFieldElement([2, 2, 2, 2]));
        let z3 = Fr(fiat::FrMontgomeryDomainFieldElement([3, 3, 3, 3]));

        assert_eq!(z3, z1 + z2);
    }

    #[test]
    fn test_subtraction_examples() {
        let mut z1 = Fr(fiat::FrMontgomeryDomainFieldElement([1, 1, 1, 1]));
        z1 -= z1;

        assert_eq!(z1, Fr::ZERO);
    }

    #[test]
    fn test_small_multiplication_examples() {
        let z1 = fiat::FrNonMontgomeryDomainFieldElement([1, 0, 0, 0]);
        let z2 = fiat::FrNonMontgomeryDomainFieldElement([2, 0, 0, 0]);
        let z3 = fiat::FrNonMontgomeryDomainFieldElement([3, 0, 0, 0]);

        let mut z1_mont = fiat::FrMontgomeryDomainFieldElement([0; 4]);
        let mut z2_mont = fiat::FrMontgomeryDomainFieldElement([0; 4]);
        let mut z3_mont = fiat::FrMontgomeryDomainFieldElement([0; 4]);
        fiat::fr_to_montgomery(&mut z1_mont, &z1);
        fiat::fr_to_montgomery(&mut z2_mont, &z2);
        fiat::fr_to_montgomery(&mut z3_mont, &z3);

        assert_eq!(Fr(z1_mont) + Fr(z1_mont), Fr(z1_mont) * Fr(z2_mont));
        assert_eq!(
            Fr(z1_mont) + Fr(z1_mont) + Fr(z1_mont),
            Fr(z1_mont) * Fr(z3_mont)
        );
    }

    #[test]
    fn test_2192_times_zero() {
        let two192 = Fr(fiat::FrMontgomeryDomainFieldElement([0, 0, 0, 1]));
        assert_eq!(two192 * Fr::zero(), Fr::ZERO);
    }

    #[test]
    fn test_minus_one_squared() {
        let minus_one = Fr::zero() - Fr::one();
        assert_eq!(minus_one.square(), Fr::ONE);
    }

    #[test]
    fn test_modulus_from_le_bytes_mod_order() {
        // Field modulus - 1 in non-montgomery form that satisfies the fiat-crypto preconditions (< m)
        let modulus_minus_one = fiat::FrNonMontgomeryDomainFieldElement([
            13356249993388743167,
            5950279507993463550,
            10965441865914903552,
            336320092672043348,
        ]);

        // Convert bytes into montgomery domain
        let mut modulus_minus_one_montgomery = fiat::FrMontgomeryDomainFieldElement([0; 4]);
        fiat::fr_to_montgomery(&mut modulus_minus_one_montgomery, &modulus_minus_one);

        // Convert to [u8; 48] bytes out of montgomery domain
        let modulus_non_montgomery_bytes = Fr::to_bytes(&Fr(modulus_minus_one_montgomery));

        // Convert [u8; 48] bytes into field element in montgomery domain
        let modulus_field_montgomery = Fr::from_le_bytes_mod_order(&modulus_non_montgomery_bytes);

        // Convert field element out of montgomery domain
        let mut x_non_montgomery = fiat::FrNonMontgomeryDomainFieldElement([0; 4]);
        fiat::fr_from_montgomery(&mut x_non_montgomery, &modulus_field_montgomery.0);

        // Assertion check against original `FrNonMontgomeryDomainFieldElement`
        assert_eq!(x_non_montgomery.0, modulus_minus_one.0);
    }
}
