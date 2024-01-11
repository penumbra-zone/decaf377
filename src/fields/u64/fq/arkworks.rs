use super::{fiat, wrapper::Fq};
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

impl PrimeField for Fq {
    /// A `BigInteger` type that can represent elements of this field.
    type BigInt = BigInt<4>;

    /// The BLS12-377 scalar field modulus `q` (8444461749428370424248824938781546531375899335154063827935233455917409239041)
    const MODULUS: Self::BigInt = ark_ff::BigInt([
        725501752471715841,
        6461107452199829505,
        6968279316240510977,
        1345280370688173398,
    ]);

    /// The value `(p - 1)/ 2`.
    const MODULUS_MINUS_ONE_DIV_TWO: Self::BigInt = BigInt([
        9586122913090633728,
        12453925762954690560,
        3484139658120255488,
        672640185344086699,
    ]);

    /// The size of the modulus in bits.
    const MODULUS_BIT_SIZE: u32 = 253;

    /// The trace of the field is defined as the smallest integer `t` such that by
    /// `2^s * t = p - 1`, and `t` is coprime to 2.
    const TRACE: Self::BigInt = BigInt([
        17149038877957297187,
        11113960768935211860,
        14608890324369326440,
        9558,
    ]);

    /// The value `(t - 1)/ 2`.
    const TRACE_MINUS_ONE_DIV_TWO: Self::BigInt = BigInt([
        8574519438978648593,
        5556980384467605930,
        7304445162184663220,
        4779,
    ]);

    fn from_bigint(repr: Self::BigInt) -> Option<Self> {
        if repr >= Fq::MODULUS {
            None
        } else {
            Some(Fq(fiat::FqMontgomeryDomainFieldElement(repr.0)))
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
        let modulus_field_montgomery = Fq::from_bytes(&t);

        modulus_field_montgomery
    }
}

impl Field for Fq {
    type BasePrimeField = Self;
    type BasePrimeFieldIter = iter::Once<Self::BasePrimeField>;

    const SQRT_PRECOMP: Option<SqrtPrecomputation<Self>> =
        Some(SqrtPrecomputation::TonelliShanks {
            two_adicity: 47,
            quadratic_nonresidue_to_trace: Fq(fiat::FqMontgomeryDomainFieldElement([
                4340692304772210610,
                11102725085307959083,
                15540458298643990566,
                944526744080888988,
            ])),
            trace_of_modulus_minus_one_div_two: &[
                8574519438978648593,
                5556980384467605930,
                7304445162184663220,
                4779,
            ],
        });

    const ZERO: Self = Fq(fiat::FqMontgomeryDomainFieldElement([0, 0, 0, 0]));

    const ONE: Self = Fq(fiat::FqMontgomeryDomainFieldElement([
        9015221291577245683,
        8239323489949974514,
        1646089257421115374,
        958099254763297437,
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

impl FftField for Fq {
    const GENERATOR: Self = Fq(fiat::FqMontgomeryDomainFieldElement([22, 0, 0, 0]));
    const TWO_ADICITY: u32 = 47;
    const TWO_ADIC_ROOT_OF_UNITY: Self = Fq(fiat::FqMontgomeryDomainFieldElement([
        5147320413305080158,
        11191566996928196682,
        6973424315369300271,
        1284854061110734017,
    ]));
    const SMALL_SUBGROUP_BASE: Option<u32> = None;
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = None;
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Self> = None;
}

impl From<u128> for Fq {
    fn from(mut other: u128) -> Self {
        let mut result = BigInt::default();
        result.0[0] = ((other << 64) >> 64) as u64;
        result.0[1] = (other >> 64) as u64;
        Self::from_bigint(result).unwrap()
    }
}

impl From<u64> for Fq {
    fn from(other: u64) -> Self {
        Self::from_bigint(BigInt::from(other)).unwrap()
    }
}

impl From<u32> for Fq {
    fn from(other: u32) -> Self {
        Self::from_bigint(BigInt::from(other)).unwrap()
    }
}

impl From<u16> for Fq {
    fn from(other: u16) -> Self {
        Self::from_bigint(BigInt::from(other)).unwrap()
    }
}

impl From<u8> for Fq {
    fn from(other: u8) -> Self {
        Self::from_bigint(BigInt::from(other)).unwrap()
    }
}

impl From<bool> for Fq {
    fn from(other: bool) -> Self {
        Self::from_bigint(BigInt::from(u64::from(other))).unwrap()
    }
}

impl Neg for Fq {
    type Output = Self;

    #[inline]
    #[must_use]
    fn neg(mut self) -> Self {
        let neg = self.neg();
        neg
    }
}

impl<'a> AddAssign<&'a Self> for Fq {
    #[inline]
    fn add_assign(&mut self, other: &Self) {
        *self = self.add(*other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::AddAssign<Self> for Fq {
    #[inline(always)]
    fn add_assign(&mut self, other: Self) {
        *self = self.add(other);
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::AddAssign<&'a mut Self> for Fq {
    #[inline(always)]
    fn add_assign(&mut self, other: &'a mut Self) {
        *self = self.add(*other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::Add<Self> for Fq {
    type Output = Self;

    #[inline]
    fn add(mut self, other: Self) -> Self {
        self.add(other)
    }
}

impl<'a> Add<&'a Fq> for Fq {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &Self) -> Self {
        self.add(*other)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::Add<&'a mut Self> for Fq {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &'a mut Self) -> Self {
        self.add(*other)
    }
}

impl<'a> SubAssign<&'a Self> for Fq {
    #[inline]
    fn sub_assign(&mut self, other: &Self) {
        *self = self.sub(*other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::SubAssign<Self> for Fq {
    #[inline(always)]
    fn sub_assign(&mut self, other: Self) {
        *self = self.sub(other);
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::SubAssign<&'a mut Self> for Fq {
    #[inline(always)]
    fn sub_assign(&mut self, other: &'a mut Self) {
        *self = self.sub(*other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::Sub<Self> for Fq {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: Self) -> Self {
        self.sub(other)
    }
}

impl<'a> Sub<&'a Fq> for Fq {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: &Self) -> Self {
        self.sub(*other)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::Sub<&'a mut Self> for Fq {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: &'a mut Self) -> Self {
        self.sub(*other)
    }
}

impl<'a> MulAssign<&'a Self> for Fq {
    fn mul_assign(&mut self, other: &Self) {
        *self = self.mul(*other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::MulAssign<Self> for Fq {
    #[inline(always)]
    fn mul_assign(&mut self, other: Self) {
        *self = self.mul(other);
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::MulAssign<&'a mut Self> for Fq {
    #[inline(always)]
    fn mul_assign(&mut self, other: &'a mut Self) {
        *self = self.mul(*other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::Mul<Self> for Fq {
    type Output = Self;

    #[inline(always)]
    fn mul(mut self, other: Self) -> Self {
        self.mul(other)
    }
}

impl<'a> Mul<&'a Fq> for Fq {
    type Output = Self;

    #[inline]
    fn mul(mut self, other: &Self) -> Self {
        self.mul(*other)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::Mul<&'a mut Self> for Fq {
    type Output = Self;

    #[inline(always)]
    fn mul(mut self, other: &'a mut Self) -> Self {
        self.mul(*other)
    }
}

impl<'a> DivAssign<&'a Self> for Fq {
    #[inline(always)]
    fn div_assign(&mut self, other: &Self) {
        self.mul_assign(&other.inverse().unwrap());
    }
}

#[allow(unused_qualifications)]
impl core::ops::DivAssign<Self> for Fq {
    #[inline(always)]
    fn div_assign(&mut self, other: Self) {
        self.div_assign(&other)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::DivAssign<&'a mut Self> for Fq {
    #[inline(always)]
    fn div_assign(&mut self, other: &'a mut Self) {
        self.div_assign(&*other)
    }
}

#[allow(unused_qualifications)]
impl core::ops::Div<Self> for Fq {
    type Output = Self;

    #[inline(always)]
    fn div(mut self, other: Self) -> Self {
        self.div_assign(&other);
        self
    }
}

impl<'a> Div<&'a Fq> for Fq {
    type Output = Self;

    #[inline]
    fn div(mut self, other: &Self) -> Self {
        self.mul_assign(&other.inverse().unwrap());
        self
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::Div<&'a mut Self> for Fq {
    type Output = Self;

    #[inline(always)]
    fn div(mut self, other: &'a mut Self) -> Self {
        self.div_assign(&*other);
        self
    }
}

impl Zero for Fq {
    #[inline]
    fn zero() -> Self {
        Fq::ZERO
    }

    #[inline]
    fn is_zero(&self) -> bool {
        *self == Fq::ZERO
    }
}

#[allow(unused_qualifications)]
impl core::iter::Sum<Self> for Fq {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::iter::Sum<&'a Self> for Fq {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

impl One for Fq {
    #[inline]
    fn one() -> Self {
        Fq::ONE
    }

    #[inline]
    fn is_one(&self) -> bool {
        *self == Fq::ONE
    }
}

#[allow(unused_qualifications)]
impl core::iter::Product<Self> for Fq {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::one(), core::ops::Mul::mul)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::iter::Product<&'a Self> for Fq {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::one(), Mul::mul)
    }
}

impl CanonicalDeserializeWithFlags for Fq {
    fn deserialize_with_flags<R: ark_std::io::Read, F: Flags>(
        reader: R,
    ) -> Result<(Self, F), SerializationError> {
        unimplemented!()
    }
}

impl Valid for Fq {
    fn check(&self) -> Result<(), SerializationError> {
        unimplemented!()
    }
}

impl CanonicalDeserialize for Fq {
    fn deserialize_with_mode<R: ark_std::io::Read>(
        reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        unimplemented!()
    }
}

impl CanonicalSerialize for Fq {
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

impl CanonicalSerializeWithFlags for Fq {
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

impl ark_std::rand::distributions::Distribution<Fq> for ark_std::rand::distributions::Standard {
    fn sample<R: rand::prelude::Rng + ?Sized>(&self, rng: &mut R) -> Fq {
        todo!()
    }
}

impl Display for Fq {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        unimplemented!()
    }
}

impl zeroize::Zeroize for Fq {
    fn zeroize(&mut self) {
        unimplemented!()
    }
}

impl Ord for Fq {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        self.into_bigint().cmp(&other.into_bigint())
    }
}

impl PartialOrd for Fq {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl FromStr for Fq {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        unimplemented!()
    }
}

impl From<num_bigint::BigUint> for Fq {
    #[inline]
    fn from(val: num_bigint::BigUint) -> Fq {
        Fq::from_le_bytes_mod_order(&val.to_bytes_le())
    }
}

impl From<Fq> for num_bigint::BigUint {
    #[inline(always)]
    fn from(other: Fq) -> Self {
        other.into_bigint().into()
    }
}

impl From<Fq> for BigInt<4> {
    #[inline(always)]
    fn from(fq: Fq) -> Self {
        fq.into_bigint()
    }
}

impl From<BigInt<4>> for Fq {
    /// Converts `Self::BigInteger` into `Self`
    #[inline(always)]
    fn from(int: BigInt<4>) -> Self {
        Fq(fiat::FqMontgomeryDomainFieldElement(int.0))
    }
}

impl Hash for Fq {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        unimplemented!()
    }
}

impl PartialEq for Fq {
    fn eq(&self, other: &Fq) -> bool {
        let self_bytes = self.to_bytes();
        let other_bytes = other.to_bytes();
        self_bytes[..] == other_bytes[..]
    }
}

impl Eq for Fq {}

impl Default for Fq {
    fn default() -> Self {
        Fq(fiat::FqMontgomeryDomainFieldElement([0, 0, 0, 0]))
    }
}

impl core::fmt::Debug for Fq {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let bytes = self.to_bytes();
        write!(f, "Fq(0x{})", hex::encode(bytes))
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
        fn arb_fq()(a in arb_bls377()) -> Fq {
            let a = fiat::FqNonMontgomeryDomainFieldElement(a);

            let mut a_to_mont = fiat::FqMontgomeryDomainFieldElement([0; 4]);
            fiat::fq_to_montgomery(&mut a_to_mont, &a);

            Fq(a_to_mont)
        }
    }

    proptest! {
        #[test]
        fn test_addition_commutative(a in arb_fq(), b in arb_fq()) {
            assert_eq!(a + b, b + a);
        }
    }

    proptest! {
        #[test]
        fn test_addition_associative(a in arb_fq(), b in arb_fq(), c in arb_fq()) {
            assert_eq!(a + (b + c), (a + b) + c);
        }
    }

    proptest! {
        #[test]
        fn test_add_zero_identity(a in arb_fq()) {
            let zero = Fq::zero();

            assert_eq!(a + zero, a);
            assert_eq!(zero + a, a);
        }
    }

    proptest! {
        #[test]
        fn test_subtract_self_is_zero(a in arb_fq()) {
            let zero = Fq::zero();

            assert_eq!(a - a, zero);
        }
    }

    proptest! {
        #[test]
        fn test_doubling_is_just_addition(a in arb_fq()) {
            let two = fiat::FqNonMontgomeryDomainFieldElement([2, 0, 0, 0]);

            let mut two_to_mont = fiat::FqMontgomeryDomainFieldElement([0; 4]);
            fiat::fq_to_montgomery(&mut two_to_mont, &two);

            assert_eq!(Fq(two_to_mont) * a, a + a);
            assert_eq!(a.double(), a + a);
            assert_eq!(*(a.clone().double_in_place()), a + a);
        }
    }

    proptest! {
        #[test]
        fn test_adding_negation(a in arb_bls377()) {
            let a = Fq(fiat::FqMontgomeryDomainFieldElement(a));

            assert_eq!(a + -a, Fq::ZERO)
        }
    }

    proptest! {
        #[test]
        fn test_multiplication_commutative(a in arb_fq(), b in arb_fq()) {
            assert_eq!(a * b, b * a);
        }
    }

    proptest! {
        #[test]
        fn test_multiplication_associative(a in arb_fq(), b in arb_fq(), c in arb_fq()) {
            assert_eq!(a * (b * c), (a * b) * c);
        }
    }

    proptest! {
        #[test]
        fn test_multiplication_distributive(a in arb_fq(), b in arb_fq(), c in arb_fq()) {
            assert_eq!(a * (b + c), a * b + a * c);
        }
    }

    proptest! {
        #[test]
        fn test_multiply_one_identity(a in arb_fq()) {
            assert_eq!(a * Fq::ONE, a);
            assert_eq!(Fq::ONE * a, a);
        }
    }

    proptest! {
        #[test]
        fn test_multiply_minus_one_is_negation(a in arb_fq()) {
            let minus_one = -Fq::ONE;

            assert_eq!(a * minus_one, a.neg());
        }
    }

    proptest! {
        #[test]
        fn test_square_is_multiply(a in arb_fq()) {
            assert_eq!(a.square(), a * a);
            assert_eq!(*(a.clone().square_in_place()), a * a);
        }
    }

    proptest! {
        #[test]
        fn test_inverse(a in arb_fq()) {
            assert_eq!(a * a.inverse().unwrap(), Fq::ONE);
            assert_eq!(a * *(a.clone().inverse_in_place().unwrap()), Fq::ONE);
        }
    }

    proptest! {
        #[test]
        fn test_sqrt(a in arb_fq()) {
            match a.sqrt() {
                Some(x) => assert_eq!(x * x, a),
                None => {}
            }
        }
    }

    #[test]
    fn test_addition_examples() {
        let z1 = Fq(fiat::FqMontgomeryDomainFieldElement([1, 1, 1, 1]));
        let z2 = Fq(fiat::FqMontgomeryDomainFieldElement([2, 2, 2, 2]));
        let z3 = Fq(fiat::FqMontgomeryDomainFieldElement([3, 3, 3, 3]));

        assert_eq!(z3, z1 + z2);
    }

    #[test]
    fn test_subtraction_examples() {
        let mut z1 = Fq(fiat::FqMontgomeryDomainFieldElement([1, 1, 1, 1]));
        z1 -= z1;

        assert_eq!(z1, Fq::ZERO);
    }

    #[test]
    fn test_small_multiplication_examples() {
        let z1 = fiat::FqNonMontgomeryDomainFieldElement([1, 0, 0, 0]);
        let z2 = fiat::FqNonMontgomeryDomainFieldElement([2, 0, 0, 0]);
        let z3 = fiat::FqNonMontgomeryDomainFieldElement([3, 0, 0, 0]);

        let mut z1_mont = fiat::FqMontgomeryDomainFieldElement([0; 4]);
        let mut z2_mont = fiat::FqMontgomeryDomainFieldElement([0; 4]);
        let mut z3_mont = fiat::FqMontgomeryDomainFieldElement([0; 4]);
        fiat::fq_to_montgomery(&mut z1_mont, &z1);
        fiat::fq_to_montgomery(&mut z2_mont, &z2);
        fiat::fq_to_montgomery(&mut z3_mont, &z3);

        assert_eq!(Fq(z1_mont) + Fq(z1_mont), Fq(z1_mont) * Fq(z2_mont));
        assert_eq!(
            Fq(z1_mont) + Fq(z1_mont) + Fq(z1_mont),
            Fq(z1_mont) * Fq(z3_mont)
        );
    }

    #[test]
    fn test_2192_times_zero() {
        let two192 = Fq(fiat::FqMontgomeryDomainFieldElement([0, 0, 0, 1]));
        assert_eq!(two192 * Fq::zero(), Fq::ZERO);
    }

    #[test]
    fn test_minus_one_squared() {
        let minus_one = Fq::zero() - Fq::one();
        assert_eq!(minus_one.square(), Fq::ONE);
    }

    #[test]
    fn test_modulus_from_le_bytes_mod_order() {
        // Field modulus - 1 in non-montgomery form that satisfies the fiat-crypto preconditions (< m)
        let modulus_minus_one = fiat::FqNonMontgomeryDomainFieldElement([
            9586122913090633728,
            12453925762954690560,
            3484139658120255488,
            672640185344086698,
        ]);

        // Convert bytes into montgomery domain
        let mut modulus_minus_one_montgomery = fiat::FqMontgomeryDomainFieldElement([0; 4]);
        fiat::fq_to_montgomery(&mut modulus_minus_one_montgomery, &modulus_minus_one);

        // Convert to [u8; 48] bytes out of montgomery domain
        let modulus_non_montgomery_bytes = Fq::to_bytes(&Fq(modulus_minus_one_montgomery));

        // Convert [u8; 48] bytes into field element in montgomery domain
        let modulus_field_montgomery = Fq::from_le_bytes_mod_order(&modulus_non_montgomery_bytes);

        // Convert field element out of montgomery domain
        let mut x_non_montgomery = fiat::FqNonMontgomeryDomainFieldElement([0; 4]);
        fiat::fq_from_montgomery(&mut x_non_montgomery, &modulus_field_montgomery.0);

        // Assertion check against original `FqNonMontgomeryDomainFieldElement`
        assert_eq!(x_non_montgomery.0, modulus_minus_one.0);
    }
}
