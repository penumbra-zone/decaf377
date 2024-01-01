use core::{ops::{Neg, Add, AddAssign, Sub, SubAssign, MulAssign, Mul, DivAssign, Div}, iter, fmt::{Formatter, Display}, cmp::Ordering};

use ark_ff::{PrimeField, BigInt, Field, SqrtPrecomputation};
use ark_serialize::{Flags, CanonicalDeserializeWithFlags, SerializationError, Compress, Validate, CanonicalDeserialize, Valid, CanonicalSerializeWithFlags, CanonicalSerialize};
use ark_std::{str::FromStr, Zero, One, rand};
use ark_ff::FftField;
use core::hash::Hash;

use super::wrapper::Fp;

impl PrimeField for Fp {
    type BigInt = BigInt<6>; // change from hardcoded
    const MODULUS: Self::BigInt = ark_ff::BigInt([0; 6]); // use Fp::Modulus
    const MODULUS_MINUS_ONE_DIV_TWO: Self::BigInt = unimplemented!(); // Fp::MODULUS.divide_by_2_round_down()
    const MODULUS_BIT_SIZE: u32 = unimplemented!(); // Fp::MODULUS.const_num_bits()
    const TRACE: Self::BigInt = unimplemented!(); // Fp::MODULUS.two_adic_coefficient()
    const TRACE_MINUS_ONE_DIV_TWO: Self::BigInt = unimplemented!(); // Self::TRACE.divide_by_2_round_down()

    fn from_bigint(repr: Self::BigInt) -> Option<Self> {
        unimplemented!()
    }

    fn into_bigint(self) -> Self::BigInt {
        unimplemented!()
    }

    fn from_be_bytes_mod_order(bytes: &[u8]) -> Self {
       unimplemented!()
    }

    fn from_le_bytes_mod_order(bytes: &[u8]) -> Self {
        unimplemented!()
    }
}

impl Field for Fp {
    type BasePrimeField = Self;
    type BasePrimeFieldIter = iter::Once<Self::BasePrimeField>;

    const SQRT_PRECOMP: Option<SqrtPrecomputation<Self>> = None; // use Fp::SQRT_PRECOMP
    const ZERO: Self = unimplemented!();
    const ONE: Self = unimplemented!();

    fn extension_degree() -> u64 {
        unimplemented!()
    }

    fn to_base_prime_field_elements(&self) -> Self::BasePrimeFieldIter {
        unimplemented!()
    }

    fn from_base_prime_field_elems(elems: &[Self::BasePrimeField]) -> Option<Self> {
        todo!()
    }

    fn from_base_prime_field(elem: Self::BasePrimeField) -> Self {
        unimplemented!()
    }

    fn double(&self) -> Self {
        unimplemented!()
    }

    fn double_in_place(&mut self) -> &mut Self {
        unimplemented!()
    }

    // Should this be FpTrait invocation?
    fn neg_in_place(&mut self) -> &mut Self {
        unimplemented!()
    }

    fn from_random_bytes_with_flags<F: ark_serialize::Flags>(bytes: &[u8]) -> Option<(Self, F)> {
        unimplemented!()
    }

    fn legendre(&self) -> ark_ff::LegendreSymbol {
        unimplemented!()
    }

    fn square(&self) -> Self {
        unimplemented!()
    }

    fn square_in_place(&mut self) -> &mut Self {
        unimplemented!()
    }

    fn inverse(&self) -> Option<Self> {
        unimplemented!()
    }

    fn inverse_in_place(&mut self) -> Option<&mut Self> {
        unimplemented!()
    }

    fn frobenius_map_in_place(&mut self, power: usize) {
        unimplemented!()
    }

    fn characteristic() -> &'static [u64] {
        unimplemented!()
    }

    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        unimplemented!()
    }

    fn sqrt(&self) -> Option<Self> {
        unimplemented!()
    }

    fn sqrt_in_place(&mut self) -> Option<&mut Self> {
        unimplemented!()
    }

    fn sum_of_products<const T: usize>(a: &[Self; T], b: &[Self; T]) -> Self {
        unimplemented!()
    }

    fn frobenius_map(&self, power: usize) -> Self {
        unimplemented!()
    }

    fn pow<S: AsRef<[u64]>>(&self, exp: S) -> Self {
        unimplemented!()
    }

    fn pow_with_table<S: AsRef<[u64]>>(powers_of_2: &[Self], exp: S) -> Option<Self> {
        unimplemented!()
    }
}

impl From<u128> for Fp {
    fn from(value: u128) -> Self {
        unimplemented!()
    }
}

impl From<u64> for Fp {
    fn from(value: u64) -> Self {
        unimplemented!()
    }
}

impl From<u32> for Fp {
    fn from(value: u32) -> Self {
        unimplemented!()
    }
}

impl From<u16> for Fp {
    fn from(value: u16) -> Self {
        unimplemented!()
    }
}

impl From<u8> for Fp {
    fn from(value: u8) -> Self {
        unimplemented!()
    }
}

impl From<bool> for Fp {
    fn from(value: bool) -> Self {
        unimplemented!()
    }
}

impl Neg for Fp {
    type Output = Self;

    #[inline]
    #[must_use]
    fn neg(mut self) -> Self {
        Fp::neg_in_place(&mut self);
        self
    }
}

//////////////////////

impl<'a> AddAssign<&'a Self> for Fp {
    #[inline]
    fn add_assign(&mut self, other: &Self) {
        Fp::add_assign(self, other)
    }
}

#[allow(unused_qualifications)]
impl core::ops::AddAssign<Self> for Fp {
    #[inline(always)]
    fn add_assign(&mut self, other: Self) {
        self.add_assign(&other)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::AddAssign<&'a mut Self> for Fp {
    #[inline(always)]
    fn add_assign(&mut self, other: &'a mut Self) {
        self.add_assign(&*other)
    }
}

//////////////////////

#[allow(unused_qualifications)]
impl core::ops::Add<Self> for Fp {
    type Output = Self;

    #[inline]
    fn add(mut self, other: Self) -> Self {
        self.add_assign(&other);
        self
    }
}

impl<'a> Add<&'a Fp> for Fp {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &Self) -> Self {
        self.add_assign(other);
        self
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::Add<&'a mut Self> for Fp {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &'a mut Self) -> Self {
        self.add_assign(&*other);
        self
    }
}

//////////////////////

impl<'a> SubAssign<&'a Self> for Fp {
    #[inline]
    fn sub_assign(&mut self, other: &Self) {
        Fp::sub_assign(self, other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::SubAssign<Self> for Fp {
    #[inline(always)]
    fn sub_assign(&mut self, other: Self) {
        self.sub_assign(&other)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::SubAssign<&'a mut Self> for Fp {
    #[inline(always)]
    fn sub_assign(&mut self, other: &'a mut Self) {
        self.sub_assign(&*other)
    }
}

//////////////////////

#[allow(unused_qualifications)]
impl core::ops::Sub<Self> for Fp {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: Self) -> Self {
        self.sub_assign(&other);
        self
    }
}

impl<'a> Sub<&'a Fp> for Fp {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: &Self) -> Self {
        self.sub_assign(other);
        self
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::Sub<&'a mut Self> for Fp {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: &'a mut Self) -> Self {
        self.sub_assign(&*other);
        self
    }
}

//////////////////////

impl<'a> MulAssign<&'a Self> for Fp {
    fn mul_assign(&mut self, other: &Self) {
        Fp::mul_assign(self, other)
    }
}

#[allow(unused_qualifications)]
impl core::ops::MulAssign<Self> for Fp {
    #[inline(always)]
    fn mul_assign(&mut self, other: Self) {
        self.mul_assign(&other)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::MulAssign<&'a mut Self> for Fp {
    #[inline(always)]
    fn mul_assign(&mut self, other: &'a mut Self) {
        self.mul_assign(&*other)
    }
}

//////////////////////

#[allow(unused_qualifications)]
impl core::ops::Mul<Self> for Fp {
    type Output = Self;

    #[inline(always)]
    fn mul(mut self, other: Self) -> Self {
        self.mul_assign(&other);
        self
    }
}

impl<'a> Mul<&'a Fp> for Fp {
    type Output = Self;

    #[inline]
    fn mul(mut self, other: &Self) -> Self {
        self.mul_assign(other);
        self
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::Mul<&'a mut Self> for Fp {
    type Output = Self;

    #[inline(always)]
    fn mul(mut self, other: &'a mut Self) -> Self {
        self.mul_assign(&*other);
        self
    }
}

//////////////////////

/// Computes `self *= other.inverse()` if `other.inverse()` is `Some`, and
/// panics otherwise.
impl<'a> DivAssign<&'a Self> for Fp {
    #[inline(always)]
    fn div_assign(&mut self, other: &Self) {
        self.mul_assign(&other.inverse().unwrap());
    }
}

#[allow(unused_qualifications)]
impl core::ops::DivAssign<Self> for Fp {
    #[inline(always)]
    fn div_assign(&mut self, other: Self) {
        self.div_assign(&other)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::DivAssign<&'a mut Self> for Fp {
    #[inline(always)]
    fn div_assign(&mut self, other: &'a mut Self) {
        self.div_assign(&*other)
    }
}

//////////////////////

#[allow(unused_qualifications)]
impl core::ops::Div<Self> for Fp {
    type Output = Self;

    #[inline(always)]
    fn div(mut self, other: Self) -> Self {
        self.div_assign(&other);
        self
    }
}

impl<'a> Div<&'a Fp> for Fp {
    type Output = Self;

    /// Returns `self * other.inverse()` if `other.inverse()` is `Some`, and
    /// panics otherwise.
    #[inline]
    fn div(mut self, other: &Self) -> Self {
        self.mul_assign(&other.inverse().unwrap());
        self
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::Div<&'a mut Self> for Fp {
    type Output = Self;

    #[inline(always)]
    fn div(mut self, other: &'a mut Self) -> Self {
        self.div_assign(&*other);
        self
    }
}

//////////////////////

impl Zero for Fp {
    #[inline]
    fn zero() -> Self {
        Fp::ZERO
    }

    #[inline]
    fn is_zero(&self) -> bool {
        *self == Fp::ZERO
    }
}

#[allow(unused_qualifications)]
impl core::iter::Sum<Self> for Fp {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::iter::Sum<&'a Self> for Fp {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

impl One for Fp {
    #[inline]
    fn one() -> Self {
        Fp::ONE
    }

    #[inline]
    fn is_one(&self) -> bool {
        *self == Fp::ONE
    }
}

#[allow(unused_qualifications)]
impl core::iter::Product<Self> for Fp {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::one(), core::ops::Mul::mul)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::iter::Product<&'a Self> for Fp {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::one(), Mul::mul)
    }
}

//////////////////////

impl CanonicalDeserializeWithFlags for Fp {
    fn deserialize_with_flags<R: ark_std::io::Read, F: Flags>(
        reader: R,
    ) -> Result<(Self, F), SerializationError> {
        unimplemented!()
    }
}

impl Valid for Fp {
    fn check(&self) -> Result<(), SerializationError> {
        unimplemented!()
    }
}

impl CanonicalDeserialize for Fp {
    fn deserialize_with_mode<R: ark_std::io::Read>(
        reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        unimplemented!()
    }
}

impl CanonicalSerialize for Fp {
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

impl CanonicalSerializeWithFlags for Fp {
    fn serialize_with_flags<W: ark_std::io::Write, F: Flags>(
        &self,
        writer: W,
        flags: F,
    ) -> Result<(), SerializationError> {
        unimplemented!()
    }

    // Let `m = 8 * n` for some `n` be the smallest multiple of 8 greater
    // than `Fp::MODULUS_BIT_SIZE`.
    // If `(m - Fp::MODULUS_BIT_SIZE) >= F::BIT_SIZE` , then this method returns `n`;
    // otherwise, it returns `n + 1`.
    fn serialized_size_with_flags<F: Flags>(&self) -> usize {
        unimplemented!()
    }
}

impl ark_std::rand::distributions::Distribution<Fp>
    for ark_std::rand::distributions::Standard
{
    fn sample<R: rand::prelude::Rng + ?Sized>(&self, rng: &mut R) -> Fp {
        todo!()
    }
}

//////////////////////

impl ark_std::fmt::Debug for Fp {
    fn fmt(&self, f: &mut Formatter<'_>) -> ark_std::fmt::Result {
        unimplemented!()
    }
}

/// Outputs a string containing the value of `self`,
/// represented as a decimal without leading zeroes.
impl Display for Fp {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        unimplemented!()
    }
}

impl zeroize::Zeroize for Fp {
    // The phantom data does not contain element-specific data
    // and thus does not need to be zeroized.
    fn zeroize(&mut self) {
        unimplemented!()
    }
}

/// Note that this implementation of `Ord` compares field elements viewing
/// them as integers in the range 0, 1, ..., Fp::MODULUS - 1. However, other
/// implementations of `PrimeField` might choose a different ordering, and
/// as such, users should use this `Ord` for applications where
/// any ordering suffices (like in a BTreeMap), and not in applications
/// where a particular ordering is required.
impl Ord for Fp {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        unimplemented!()
    }
}

/// Note that this implementation of `PartialOrd` compares field elements
/// viewing them as integers in the range 0, 1, ..., `Fp::MODULUS` - 1. However,
/// other implementations of `PrimeField` might choose a different ordering, and
/// as such, users should use this `PartialOrd` for applications where
/// any ordering suffices (like in a BTreeMap), and not in applications
/// where a particular ordering is required.
impl PartialOrd for Fp {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        unimplemented!()
    }
}

//////////////////////

impl FromStr for Fp {
    type Err = ();

    /// Interpret a string of numbers as a (congruent) prime field element.
    /// Does not accept unnecessary leading zeroes or a blank string.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        unimplemented!()
    }
}

impl From<num_bigint::BigUint> for Fp {
    #[inline]
    fn from(val: num_bigint::BigUint) -> Fp {
        unimplemented!()
    }
}

impl From<Fp> for num_bigint::BigUint {
    #[inline(always)]
    fn from(other: Fp) -> Self {
        unimplemented!()
    }
}

impl From<Fp> for BigInt<6> {
    #[inline(always)]
    fn from(fp: Fp) -> Self {
        unimplemented!()
    }
}

impl From<BigInt<6>> for Fp {
    /// Converts `Self::BigInteger` into `Self`
    #[inline(always)]
    fn from(int: BigInt<6>) -> Self {
        unimplemented!()
    }
}

impl FftField for Fp {
    const GENERATOR: Self = unimplemented!(); // use Fp::GENERATOR
    const TWO_ADICITY: u32 = unimplemented!(); // use Fp::TWO_ADICITY
    const TWO_ADIC_ROOT_OF_UNITY: Self = unimplemented!(); // Fp::TWO_ADIC_ROOT_OF_UNITY
    const SMALL_SUBGROUP_BASE: Option<u32> = unimplemented!(); // Fp::SMALL_SUBGROUP_BASE
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = unimplemented!(); // Fp::SMALL_SUBGROUP_BASE_ADICITY
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Self> = unimplemented!(); // Fp::LARGE_SUBGROUP_ROOT_OF_UNITY

    fn get_root_of_unity(n: u64) -> Option<Self> {
        unimplemented!()
    }
}

impl Hash for Fp {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        unimplemented!()
    }
}

impl PartialEq for Fp {
    fn eq(&self, other: &Self) -> bool {
        unimplemented!()
    }
}

impl Eq for Fp {}

impl Default for Fp {
    fn default() -> Self {
        unimplemented!()
    }
}