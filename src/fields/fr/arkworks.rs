use super::{arkworks_constants::*, Fr};
use ark_ff::{BigInt, Field, PrimeField, SqrtPrecomputation};
use ark_ff::{BigInteger, FftField};
use ark_serialize::{
    CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, Compress, EmptyFlags, Flags, SerializationError, Valid, Validate,
};
use ark_std::{rand, str::FromStr, string::ToString, One, Zero};
use core::convert::TryInto;
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

    /// The BLS12-377 base field modulus `p` = 0x4aad957a68b2955982d1347970dec005293a3afc43c8afeb95aee9ac33fd9ff
    const MODULUS: Self::BigInt = ark_ff::BigInt(MODULUS_LIMBS);

    /// The value `(p - 1)/ 2`.
    const MODULUS_MINUS_ONE_DIV_TWO: Self::BigInt = BigInt(MODULUS_MINUS_ONE_DIV_TWO_LIMBS);

    /// The size of the modulus in bits.
    const MODULUS_BIT_SIZE: u32 = MODULUS_BIT_SIZE;

    /// The trace of the field is defined as the smallest integer `t` such that by
    /// `2^s * t = p - 1`, and `t` is coprime to 2.
    const TRACE: Self::BigInt = BigInt(TRACE_LIMBS);

    /// The value `(t - 1)/ 2`.
    const TRACE_MINUS_ONE_DIV_TWO: Self::BigInt = BigInt(TRACE_MINUS_ONE_DIV_TWO_LIMBS);

    fn from_bigint(repr: Self::BigInt) -> Option<Self> {
        if repr >= Fr::MODULUS {
            None
        } else {
            // Assuming BigInt is little endian
            Some(Self::from_le_limbs(repr.0))
        }
    }

    fn into_bigint(self) -> Self::BigInt {
        BigInt(self.to_le_limbs())
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
        let modulus_field_montgomery = Fr::from_raw_bytes(&t);

        modulus_field_montgomery
    }
}

impl Field for Fr {
    type BasePrimeField = Self;
    type BasePrimeFieldIter = iter::Once<Self::BasePrimeField>;

    const SQRT_PRECOMP: Option<SqrtPrecomputation<Self>> = Some(SqrtPrecomputation::Case3Mod4 {
        modulus_plus_one_div_four: &[
            12562434535201961600,
            1487569876998365887,
            7353046484906113792,
            84080023168010837,
        ],
    });

    const ZERO: Self = Self::zero();

    // Montomgery representation of one
    const ONE: Self = Self::one();

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
        self.add(self)
    }

    fn double_in_place(&mut self) -> &mut Self {
        *self = self.add(self);
        self
    }

    fn neg_in_place(&mut self) -> &mut Self {
        *self = self.add(self);
        self
    }

    fn from_random_bytes_with_flags<F: ark_serialize::Flags>(bytes: &[u8]) -> Option<(Self, F)> {
        Some((Self::from_le_bytes_mod_order(bytes), F::default()))
    }

    fn legendre(&self) -> ark_ff::LegendreSymbol {
        use ark_ff::LegendreSymbol::*;

        if self.is_zero() {
            return Zero;
        }
        if self.pow(&Self::MODULUS_MINUS_ONE_DIV_TWO.0).is_one() {
            return QuadraticResidue;
        }
        return QuadraticNonResidue;
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
    const GENERATOR: Self = MULTIPLICATIVE_GENERATOR;
    const TWO_ADICITY: u32 = TWO_ADICITY;
    const TWO_ADIC_ROOT_OF_UNITY: Self = TWO_ADIC_ROOT_OF_UNITY;
    const SMALL_SUBGROUP_BASE: Option<u32> = None;
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = None;
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Self> = None;
}

impl From<u128> for Fr {
    fn from(other: u128) -> Self {
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
    fn neg(self) -> Self {
        let neg = self.neg();
        neg
    }
}

impl<'a> AddAssign<&'a Self> for Fr {
    #[inline]
    fn add_assign(&mut self, other: &Self) {
        *self = self.add(other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::AddAssign<Self> for Fr {
    #[inline(always)]
    fn add_assign(&mut self, other: Self) {
        *self = self.add(&other);
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::AddAssign<&'a mut Self> for Fr {
    #[inline(always)]
    fn add_assign(&mut self, other: &'a mut Self) {
        *self = self.add(other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::Add<Self> for Fr {
    type Output = Self;

    #[inline]
    fn add(self, other: Self) -> Self {
        self.add(&other)
    }
}

impl<'a> Add<&'a Fr> for Fr {
    type Output = Self;

    #[inline]
    fn add(self, other: &Self) -> Self {
        self.add(other)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::Add<&'a mut Self> for Fr {
    type Output = Self;

    #[inline]
    fn add(self, other: &'a mut Self) -> Self {
        self.add(other)
    }
}

impl<'a> SubAssign<&'a Self> for Fr {
    #[inline]
    fn sub_assign(&mut self, other: &Self) {
        *self = self.sub(other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::SubAssign<Self> for Fr {
    #[inline(always)]
    fn sub_assign(&mut self, other: Self) {
        *self = self.sub(&other);
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::SubAssign<&'a mut Self> for Fr {
    #[inline(always)]
    fn sub_assign(&mut self, other: &'a mut Self) {
        *self = self.sub(other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::Sub<Self> for Fr {
    type Output = Self;

    #[inline]
    fn sub(self, other: Self) -> Self {
        self.sub(&other)
    }
}

impl<'a> Sub<&'a Fr> for Fr {
    type Output = Self;

    #[inline]
    fn sub(self, other: &Self) -> Self {
        self.sub(other)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::Sub<&'a mut Self> for Fr {
    type Output = Self;

    #[inline]
    fn sub(self, other: &'a mut Self) -> Self {
        self.sub(other)
    }
}

impl<'a> MulAssign<&'a Self> for Fr {
    fn mul_assign(&mut self, other: &Self) {
        *self = self.mul(other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::MulAssign<Self> for Fr {
    #[inline(always)]
    fn mul_assign(&mut self, other: Self) {
        *self = self.mul(&other);
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::MulAssign<&'a mut Self> for Fr {
    #[inline(always)]
    fn mul_assign(&mut self, other: &'a mut Self) {
        *self = self.mul(other);
    }
}

#[allow(unused_qualifications)]
impl core::ops::Mul<Self> for Fr {
    type Output = Self;

    #[inline(always)]
    fn mul(self, other: Self) -> Self {
        self.mul(&other)
    }
}

impl<'a> Mul<&'a Fr> for Fr {
    type Output = Self;

    #[inline]
    fn mul(self, other: &Self) -> Self {
        self.mul(other)
    }
}

#[allow(unused_qualifications)]
impl<'a> core::ops::Mul<&'a mut Self> for Fr {
    type Output = Self;

    #[inline(always)]
    fn mul(self, other: &'a mut Self) -> Self {
        self.mul(other)
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
        mut reader: R,
    ) -> Result<(Self, F), SerializationError> {
        // Enough for the field element + 8 bits of flags. The last byte may or may not contain flags.
        let mut bytes = [0u8; (Self::MODULUS_BIT_SIZE as usize + 8 + 7) / 8];

        let expected_len = (Self::MODULUS_BIT_SIZE as usize + F::BIT_SIZE + 7) / 8;
        reader.read_exact(&mut bytes[..expected_len])?;
        let flags = F::from_u8(bytes[bytes.len() - 1] & !(!0 >> F::BIT_SIZE))
            .ok_or(SerializationError::UnexpectedFlags)?;
        // Then, convert the bytes to limbs, to benefit from the canonical check we have for
        // bigint.
        let mut limbs = [0u64; 4];
        for (limb, chunk) in limbs.iter_mut().zip(bytes[..32].chunks_exact(8)) {
            *limb = u64::from_le_bytes(chunk.try_into().expect("chunk will have the right size"));
        }
        let out = Self::from_bigint(BigInt(limbs)).ok_or(SerializationError::InvalidData)?;
        Ok((out, flags))
    }
}

impl Valid for Fr {
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}

impl CanonicalDeserialize for Fr {
    fn deserialize_with_mode<R: ark_std::io::Read>(
        reader: R,
        _compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let (out, _) = Self::deserialize_with_flags::<R, EmptyFlags>(reader)?;
        match validate {
            Validate::Yes => out.check(),
            Validate::No => Ok(()),
        }?;
        Ok(out)
    }
}

impl CanonicalSerialize for Fr {
    #[inline]
    fn serialize_with_mode<W: ark_std::io::Write>(
        &self,
        writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        self.serialize_with_flags(writer, EmptyFlags)
    }

    #[inline]
    fn serialized_size(&self, _compress: Compress) -> usize {
        self.serialized_size_with_flags::<EmptyFlags>()
    }
}

impl CanonicalSerializeWithFlags for Fr {
    fn serialize_with_flags<W: ark_std::io::Write, F: Flags>(
        &self,
        mut writer: W,
        flags: F,
    ) -> Result<(), SerializationError> {
        // Arkworks imposes this constraint
        if F::BIT_SIZE > 8 {
            return Err(SerializationError::NotEnoughSpace);
        }

        // We can't just write the bytes out, because the last byte might be masked by flags.
        let mut bytes = self.to_bytes_le();
        // Either the flags fit into the last byte...
        if bytes.len() == self.serialized_size_with_flags::<F>() {
            // In which case we have to mask the last byte
            bytes[bytes.len() - 1] |= flags.u8_bitmask();
            writer.write_all(&bytes)?;
        } else {
            // Or else we create a new byte
            writer.write_all(&bytes)?;
            writer.write_all(&[flags.u8_bitmask()])?;
        }
        Ok(())
    }

    fn serialized_size_with_flags<F: Flags>(&self) -> usize {
        (Self::MODULUS_BIT_SIZE as usize + F::BIT_SIZE + 7) / 8
    }
}

impl ark_std::rand::distributions::Distribution<Fr> for ark_std::rand::distributions::Standard {
    #[inline]
    fn sample<R: rand::prelude::Rng + ?Sized>(&self, rng: &mut R) -> Fr {
        //unimplemented!("boom 3")
        use ark_std::dbg;
        let num_attempts = 5;
        let mut i = 0;
        let mut repr: [u64; 4];
        let shave_bits = 64 * 4 - (MODULUS_BIT_SIZE as usize);

        while i < num_attempts {
            repr = rng.sample(ark_std::rand::distributions::Standard);
            dbg!(shave_bits);
            assert!(shave_bits <= 64);

            // Mask away the unused bits at the beginning.
            let mask = if shave_bits == 64 {
                0
            } else {
                u64::MAX >> shave_bits
            };
            dbg!(mask);
            dbg!(repr);

            if let Some(val) = repr.last_mut() {
                *val &= mask
            }
            dbg!(repr);
            dbg!(Fr::from_bigint(BigInt(repr)));
            //dbg!(BigInt(repr) <= BigInt::from_bigint(MODULUS_LIMBS));

            if let Some(small_enough) = Fr::from_bigint(BigInt(repr)) {
                dbg!("found one");
                return small_enough;
            }
            i += 1;
        }
        unreachable!("didn't find Fr");
    }
}

impl Display for Fr {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let string = self.into_bigint().to_string();
        write!(f, "{}", string.trim_start_matches('0'))
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

    fn from_str(_s: &str) -> Result<Self, Self::Err> {
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
        Fr::from_le_bytes_mod_order(&int.to_bytes_le())
    }
}

impl Hash for Fr {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        state.write(&self.to_bytes_le())
    }
}

impl Default for Fr {
    fn default() -> Self {
        Fr::zero()
    }
}

impl core::fmt::Debug for Fr {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let bytes = self.into_bigint().to_bytes_be();
        write!(f, "Fr(0x{})", hex::encode(bytes))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate alloc;
    use alloc::vec::Vec;
    use proptest::prelude::*;

    prop_compose! {
        // Technically this might overflow, but we won't miss any values,
        // just return 0 if you overflow when consuming.
        fn arb_fr_limbs()(
            z0 in 0..u64::MAX,
            z1 in 0..u64::MAX,
            z2 in 0..u64::MAX,
            z3 in 0..336320092672043349u64
        ) -> [u64; 4] {
            [z0, z1, z2, z3]
        }
    }

    prop_compose! {
        fn arb_fr()(a in arb_fr_limbs()) -> Fr {
            // Will be fine because of the bounds in the arb_fr_limbs
            Fr::from_bigint(BigInt(a)).unwrap_or(Fr::zero())
        }
    }

    prop_compose! {
        fn arb_nonzero_fr()(a in arb_fr()) -> Fr {
            if a == Fr::zero() { Fr::one() } else { a }
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
            let two = Fr::from(2u64);

            assert_eq!(two * a, a + a);
            assert_eq!(a.double(), a + a);
            assert_eq!(*(a.clone().double_in_place()), a + a);
        }
    }

    proptest! {
        #[test]
        fn test_adding_negation(a in arb_fr()) {
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
        fn test_inverse(a in arb_nonzero_fr()) {
            assert_eq!(a * a.inverse().unwrap(), Fr::ONE);
            assert_eq!(a * *(a.clone().inverse_in_place().unwrap()), Fr::ONE);
        }
    }

    fn naive_inverse(a: Fr) -> Fr {
        a.pow(&(-Fr::from(2u64)).into_bigint().0)
    }

    proptest! {
        #[test]
        fn test_inverse_vs_naive_inverse(a in arb_nonzero_fr()) {
            assert_eq!(a.inverse().unwrap(), naive_inverse(a));
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

    proptest! {
        #[test]
        fn test_into_bigint_monomorphism(a in arb_fr()) {
            let as_bigint = a.into_bigint();
            let roundtrip = Fr::from_bigint(as_bigint);

            assert_eq!(Some(a), roundtrip);
        }
    }

    proptest! {
        #[test]
        fn test_conversion_to_bytes_via_bigint(a in arb_fr()) {
            let way1 = a.to_bytes_le();
            let way2 = a.into_bigint().to_bytes_le();
            assert_eq!(way1.as_slice(), way2.as_slice());
        }
    }

    proptest! {
        #[test]
        fn test_legendre_symbol(a in arb_nonzero_fr()) {
            assert_eq!((a * a).legendre(), ark_ff::LegendreSymbol::QuadraticResidue);
        }
    }

    proptest! {
        #[test]
        fn test_canonical_serialize_monomorphism(a in arb_fr()) {
            let mut bytes: Vec<u8> = Vec::new();
            let roundtrip = a.serialize_compressed(&mut bytes).and_then(|_| Fr::deserialize_compressed(&*bytes));
            assert!(roundtrip.is_ok());
            assert_eq!(*roundtrip.as_ref().clone().unwrap(), a);
        }
    }

    fn naive_from_le_bytes_mod_order(bytes: &[u8]) -> Fr {
        let mut acc = Fr::zero();
        let mut insert = Fr::one();
        for byte in bytes {
            for i in 0..8 {
                if (byte >> i) & 1 == 1 {
                    acc += insert;
                }
                insert.double_in_place();
            }
        }
        acc
    }

    proptest! {
        #[test]
        fn test_from_le_bytes_mod_order_vs_naive(bytes in any::<[u8; 32]>()) {
            let way1 = Fr::from_le_bytes_mod_order(&bytes);
            let way2 = naive_from_le_bytes_mod_order(&bytes);
            assert_eq!(way1, way2);
        }
    }

    #[test]
    fn test_from_le_bytes_mod_order_examples() {
        let p_plus_1_bytes: [u8; 32] = [
            0, 218, 63, 195, 154, 238, 90, 185, 254, 138, 60, 196, 175, 163, 147, 82, 0, 236, 13,
            151, 71, 19, 45, 152, 85, 41, 139, 166, 87, 217, 170, 4,
        ];
        let bytes_for_1 = {
            let mut out = [0u8; 32];
            out[0] = 1;
            out
        };
        assert_eq!(Fr::from_le_bytes_mod_order(&p_plus_1_bytes), Fr::one());
        assert_eq!(
            Fr::from_le_bytes_mod_order(&p_plus_1_bytes).to_bytes_le(),
            bytes_for_1
        );
    }

    #[test]
    fn test_addition_examples() {
        let z1: Fr = BigInt([1, 1, 1, 1]).into();
        let z2: Fr = BigInt([2, 2, 2, 2]).into();
        let z3: Fr = BigInt([3, 3, 3, 3]).into();

        assert_eq!(z3, z1 + z2);
    }

    #[test]
    fn test_subtraction_examples() {
        let mut z1: Fr = BigInt([1, 1, 1, 1]).into();
        z1 -= z1;

        assert_eq!(z1, Fr::ZERO);
    }

    #[test]
    fn test_small_multiplication_examples() {
        let z1: Fr = BigInt([1, 0, 0, 0]).into();
        let z2: Fr = BigInt([2, 0, 0, 0]).into();
        let z3: Fr = BigInt([3, 0, 0, 0]).into();

        assert_eq!(z1 + z1, z1 * z2);
        assert_eq!(z1 + z1 + z1, z1 * z3);
    }

    #[test]
    fn test_2192_times_zero() {
        let two192: Fr = BigInt([0, 0, 0, 1]).into();
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
        let modulus_minus_one: Fr = BigInt([
            13356249993388743166,
            5950279507993463550,
            10965441865914903552,
            336320092672043349,
        ])
        .into();

        assert_eq!(modulus_minus_one, -Fr::one());
    }
}
