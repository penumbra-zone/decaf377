use super::{arkworks_constants::*, Fq};
use ark_ff::{BigInt, Field, PrimeField, SqrtPrecomputation};
use ark_ff::{BigInteger, FftField};
use ark_serialize::{
    CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, Compress, EmptyFlags, Flags, SerializationError, Valid, Validate,
};
use ark_std::iterable::Iterable;
use ark_std::{rand, str::FromStr, string::ToString, One, Zero};
use core::convert::TryInto;
use core::{
    fmt::{Display, Formatter},
    iter,
};

impl PrimeField for Fq {
    /// A `BigInteger` type that can represent elements of this field.
    type BigInt = BigInt<4>;

    /// The BLS12-377 base field modulus `p` = 0x12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001
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
        if repr >= Fq::MODULUS {
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
        bytes
            .chunks(32)
            .map(|x| {
                let mut padded = [0u8; 32];
                padded[..x.len()].copy_from_slice(x);
                Self::from_raw_bytes(&padded)
            }) // [X, 2^256 * X, ...]
            .rev()
            .fold(Self::zero(), |acc, x| acc * (FIELD_SIZE_POWER_OF_TWO) + x) // let acc =
    }
}

impl Field for Fq {
    type BasePrimeField = Self;
    type BasePrimeFieldIter = iter::Once<Self::BasePrimeField>;

    const SQRT_PRECOMP: Option<SqrtPrecomputation<Self>> =
        Some(SqrtPrecomputation::TonelliShanks {
            two_adicity: TWO_ADICITY,
            quadratic_nonresidue_to_trace: QUADRATIC_NON_RESIDUE_TO_TRACE,
            trace_of_modulus_minus_one_div_two: &TRACE_MINUS_ONE_DIV_TWO_LIMBS,
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
        *self = Self::ZERO.sub(self);
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

    fn characteristic() -> &'static [u64] {
        &MODULUS_LIMBS
    }
}

impl FftField for Fq {
    const GENERATOR: Self = MULTIPLICATIVE_GENERATOR;
    const TWO_ADICITY: u32 = TWO_ADICITY;
    const TWO_ADIC_ROOT_OF_UNITY: Self = TWO_ADIC_ROOT_OF_UNITY;
    const SMALL_SUBGROUP_BASE: Option<u32> = None;
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = None;
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Self> = None;
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
impl CanonicalDeserializeWithFlags for Fq {
    fn deserialize_with_flags<R: ark_std::io::Read, F: Flags>(
        mut reader: R,
    ) -> Result<(Self, F), SerializationError> {
        // Enough for the field element + 8 bits of flags. The last byte may or may not contain flags.
        let mut bytes = [0u8; (Self::MODULUS_BIT_SIZE as usize + 7) / 8];

        let expected_len = (Self::MODULUS_BIT_SIZE as usize + F::BIT_SIZE + 7) / 8;
        reader.read_exact(&mut bytes[..expected_len])?;
        let flags = F::from_u8_remove_flags(&mut bytes[bytes.len() - 1])
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

impl Valid for Fq {
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}

impl CanonicalDeserialize for Fq {
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

impl CanonicalSerialize for Fq {
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

impl CanonicalSerializeWithFlags for Fq {
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

impl ark_std::rand::distributions::Distribution<Fq> for ark_std::rand::distributions::Standard {
    fn sample<R: rand::prelude::Rng + ?Sized>(&self, rng: &mut R) -> Fq {
        loop {
            let mut repr: [u64; 4] = rng.sample(ark_std::rand::distributions::Standard);
            let shave_bits = 64 * 4 - (MODULUS_BIT_SIZE as usize);
            // Mask away the unused bits at the beginning.
            let mask = if shave_bits == 64 {
                0
            } else {
                u64::MAX >> shave_bits
            };

            if let Some(val) = repr.last_mut() {
                *val &= mask
            }

            if let Some(small_enough) = Fq::from_bigint(BigInt(repr)) {
                return small_enough;
            }
        }
    }
}

impl Display for Fq {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let string = self.into_bigint().to_string();
        write!(f, "{}", string.trim_start_matches('0'))
    }
}
impl FromStr for Fq {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // CANDO: a more efficient method accumulating into 64 bits first.
        let mut acc = Self::zero();

        let ten = Self::from(10u8);

        for c in s.chars() {
            match c.to_digit(10) {
                Some(c) => {
                    acc = ten * acc + Self::from(u64::from(c));
                }
                None => {
                    return Err(());
                }
            }
        }
        Ok(acc)
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
    fn from(fp: Fq) -> Self {
        fp.into_bigint()
    }
}

impl From<BigInt<4>> for Fq {
    /// Converts `Self::BigInteger` into `Self`
    #[inline(always)]
    fn from(int: BigInt<4>) -> Self {
        Fq::from_le_bytes_mod_order(&int.to_bytes_le())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate alloc;
    use alloc::{format, vec::Vec};
    use ark_bls12_377::Fr as ArkFq;
    use proptest::prelude::*;

    prop_compose! {
        // Technically this might overflow, but we won't miss any values,
        // just return 0 if you overflow when consuming.
        fn arb_fp_limbs()(
            z0 in 0..u64::MAX,
            z1 in 0..u64::MAX,
            z2 in 0..u64::MAX,
            z3 in 0..1345280370688173398u64
        ) -> [u64; 4] {
            [z0, z1, z2, z3]
        }
    }

    prop_compose! {
        fn arb_fq()(a in arb_fp_limbs()) -> Fq {
            // Will be fine because of the bounds in the arb_fp_limbs
            Fq::from_bigint(BigInt(a)).unwrap_or(Fq::zero())
        }
    }

    prop_compose! {
        fn arb_nonzero_fq()(a in arb_fq()) -> Fq {
            if a == Fq::zero() { Fq::one() } else { a }
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
            let two = Fq::from(2u64);

            assert_eq!(two * a, a + a);
            assert_eq!(a.double(), a + a);
            assert_eq!(*(a.clone().double_in_place()), a + a);
        }
    }

    proptest! {
        #[test]
        fn test_adding_negation(a in arb_fq()) {
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
        fn test_inverse(a in arb_nonzero_fq()) {
            assert_eq!(a * a.inverse().unwrap(), Fq::ONE);
            assert_eq!(a * *(a.clone().inverse_in_place().unwrap()), Fq::ONE);
        }
    }

    fn naive_inverse(a: Fq) -> Fq {
        a.pow(&(-Fq::from(2u64)).into_bigint().0)
    }

    proptest! {
        #[test]
        fn test_inverse_vs_naive_inverse(a in arb_nonzero_fq()) {
            assert_eq!(a.inverse().unwrap(), naive_inverse(a));
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

    proptest! {
        #[test]
        fn test_into_bigint_monomorphism(a in arb_fq()) {
            let as_bigint = a.into_bigint();
            let roundtrip = Fq::from_bigint(as_bigint);

            assert_eq!(Some(a), roundtrip);
        }
    }

    proptest! {
        #[test]
        fn test_conversion_to_bytes_via_bigint(a in arb_fq()) {
            let way1 = a.to_bytes_le();
            let way2 = a.into_bigint().to_bytes_le();
            assert_eq!(way1.as_slice(), way2.as_slice());
        }
    }

    proptest! {
        #[test]
        fn test_legendre_symbol(a in arb_nonzero_fq()) {
            assert_eq!((a * a).legendre(), ark_ff::LegendreSymbol::QuadraticResidue);
        }
    }

    proptest! {
        #[test]
        fn test_canonical_serialize_monomorphism(a in arb_fq()) {
            let mut bytes: Vec<u8> = Vec::new();
            let roundtrip = a.serialize_compressed(&mut bytes).and_then(|_| Fq::deserialize_compressed(&*bytes));
            assert!(roundtrip.is_ok());
            assert_eq!(*roundtrip.as_ref().clone().unwrap(), a);
        }
    }

    proptest! {
        #[test]
        fn test_serialize_matches_arkworks(a in arb_fp_limbs()) {
            let our_value: Fq = BigInt(a).into();
            let their_value: ArkFq = BigInt(a).into();

            let mut our_bytes: Vec<u8> = Vec::new();
            assert!(our_value.serialize_compressed(&mut our_bytes).is_ok());

            let mut their_bytes: Vec<u8> = Vec::new();
            assert!(their_value.serialize_compressed(&mut their_bytes).is_ok());

            assert_eq!(our_bytes, their_bytes);
        }
    }

    fn naive_from_le_bytes_mod_order(bytes: &[u8]) -> Fq {
        let mut acc = Fq::zero();
        let mut insert = Fq::one();
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
        fn test_from_le_bytes_mod_order_vs_naive(bytes in any::<[u8; 80]>()) {
            let way1 = Fq::from_le_bytes_mod_order(&bytes);
            let way2 = naive_from_le_bytes_mod_order(&bytes);
            assert_eq!(way1, way2);
        }
    }

    proptest! {
        #[test]
        fn test_from_str(a in arb_fq()) {
            let x = <Fq as PrimeField>::BigInt::from(a);
            assert_eq!(Ok(a), Fq::from_str(&format!("{}", x)));
        }
    }

    #[test]
    fn test_from_le_bytes_mod_order_examples() {
        let p_plus_1_bytes: [u8; 32] = [
            2, 0, 0, 0, 0, 128, 17, 10, 1, 0, 0, 208, 254, 118, 170, 89, 1, 176, 55, 92, 30, 77,
            180, 96, 86, 165, 44, 154, 94, 101, 171, 18,
        ];
        let bytes_for_1 = {
            let mut out = [0u8; 32];
            out[0] = 1;
            out
        };

        assert_eq!(Fq::from_le_bytes_mod_order(&p_plus_1_bytes), Fq::one());
        assert_eq!(
            Fq::from_le_bytes_mod_order(&p_plus_1_bytes).to_bytes_le(),
            bytes_for_1
        );
    }

    #[test]
    fn test_addition_examples() {
        let z1: Fq = BigInt([1, 1, 1, 1]).into();
        let z2: Fq = BigInt([2, 2, 2, 2]).into();
        let z3: Fq = BigInt([3, 3, 3, 3]).into();

        assert_eq!(z3, z1 + z2);
    }

    #[test]
    fn test_subtraction_examples() {
        let mut z1: Fq = BigInt([1, 1, 1, 1]).into();
        z1 -= z1;

        assert_eq!(z1, Fq::ZERO);
    }

    #[test]
    fn test_small_multiplication_examples() {
        let z1: Fq = BigInt([1, 0, 0, 0]).into();
        let z2: Fq = BigInt([2, 0, 0, 0]).into();
        let z3: Fq = BigInt([3, 0, 0, 0]).into();

        assert_eq!(z1 + z1, z1 * z2);
        assert_eq!(z1 + z1 + z1, z1 * z3);
    }

    #[test]
    fn test_2192_times_zero() {
        let two192: Fq = BigInt([0, 0, 0, 1]).into();
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
        let modulus_minus_one: Fq = BigInt([
            725501752471715840,
            6461107452199829505,
            6968279316240510977,
            1345280370688173398,
        ])
        .into();

        assert_eq!(modulus_minus_one, -Fq::one());
    }
}
