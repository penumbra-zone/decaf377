use core::{
    cmp::Ordering,
    hash::Hash,
    iter::{Product, Sum},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use crate::Fr;

impl From<u128> for Fr {
    fn from(other: u128) -> Self {
        Self::from_le_limbs([other as u64, (other >> 64) as u64, 0, 0])
    }
}

impl From<u64> for Fr {
    fn from(other: u64) -> Self {
        u128::from(other).into()
    }
}

impl From<u32> for Fr {
    fn from(other: u32) -> Self {
        u128::from(other).into()
    }
}

impl From<u16> for Fr {
    fn from(other: u16) -> Self {
        u128::from(other).into()
    }
}

impl From<u8> for Fr {
    fn from(other: u8) -> Self {
        u128::from(other).into()
    }
}

impl From<bool> for Fr {
    fn from(other: bool) -> Self {
        u128::from(other).into()
    }
}

impl From<i8> for Fr {
    fn from(other: i8) -> Self {
        i128::from(other).into()
    }
}

impl From<i16> for Fr {
    fn from(other: i16) -> Self {
        i128::from(other).into()
    }
}

impl From<i32> for Fr {
    fn from(other: i32) -> Self {
        i128::from(other).into()
    }
}

impl From<i64> for Fr {
    fn from(other: i64) -> Self {
        i128::from(other).into()
    }
}

impl From<i128> for Fr {
    fn from(other: i128) -> Self {
        i128::from(other).into()
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

impl AddAssign<Self> for Fr {
    #[inline(always)]
    fn add_assign(&mut self, other: Self) {
        *self = self.add(&other);
    }
}

impl<'a> AddAssign<&'a mut Self> for Fr {
    #[inline(always)]
    fn add_assign(&mut self, other: &'a mut Self) {
        *self = self.add(other);
    }
}

impl Add<Self> for Fr {
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

impl<'a> Add<&'a mut Self> for Fr {
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

impl SubAssign<Self> for Fr {
    #[inline(always)]
    fn sub_assign(&mut self, other: Self) {
        *self = self.sub(&other);
    }
}

impl<'a> SubAssign<&'a mut Self> for Fr {
    #[inline(always)]
    fn sub_assign(&mut self, other: &'a mut Self) {
        *self = self.sub(other);
    }
}

impl Sub<Self> for Fr {
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

impl<'a> Sub<&'a mut Self> for Fr {
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

impl core::ops::MulAssign<Self> for Fr {
    #[inline(always)]
    fn mul_assign(&mut self, other: Self) {
        *self = self.mul(&other);
    }
}

impl<'a> core::ops::MulAssign<&'a mut Self> for Fr {
    #[inline(always)]
    fn mul_assign(&mut self, other: &'a mut Self) {
        *self = self.mul(other);
    }
}

impl Mul<Self> for Fr {
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

impl<'a> Mul<&'a mut Self> for Fr {
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

impl DivAssign<Self> for Fr {
    #[inline(always)]
    fn div_assign(&mut self, other: Self) {
        self.div_assign(&other)
    }
}

impl<'a> DivAssign<&'a mut Self> for Fr {
    #[inline(always)]
    fn div_assign(&mut self, other: &'a mut Self) {
        self.div_assign(&*other)
    }
}

impl Div<Self> for Fr {
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

impl<'a> Div<&'a mut Self> for Fr {
    type Output = Self;

    #[inline(always)]
    fn div(mut self, other: &'a mut Self) -> Self {
        self.div_assign(&*other);
        self
    }
}

impl Sum<Self> for Fr {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, Add::add)
    }
}

impl<'a> Sum<&'a Self> for Fr {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, Add::add)
    }
}

impl Product<Self> for Fr {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, Mul::mul)
    }
}

impl<'a> Product<&'a Self> for Fr {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, Mul::mul)
    }
}

impl Ord for Fr {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        let mut left = self.to_le_limbs();
        let mut right = other.to_le_limbs();
        left.reverse();
        right.reverse();
        left.cmp(&right)
    }
}

impl PartialOrd for Fr {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for Fr {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        state.write(&self.to_bytes_le())
    }
}

impl Default for Fr {
    fn default() -> Self {
        Self::ZERO
    }
}

impl core::fmt::Debug for Fr {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let bytes = {
            let mut out = self.to_bytes_le();
            out.reverse();
            out
        };
        let mut hex_chars = [0u8; 64];
        hex::encode_to_slice(&bytes, &mut hex_chars)
            .expect("not enough space to write hex characters");
        // Safety: hex characters will be valid UTF8.
        write!(f, "Fr(0x{})", unsafe {
            core::str::from_utf8_unchecked(&hex_chars)
        })
    }
}
