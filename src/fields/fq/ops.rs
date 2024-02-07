use core::{
    cmp::Ordering,
    hash::Hash,
    iter::{Product, Sum},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use crate::Fq;

impl From<u128> for Fq {
    fn from(other: u128) -> Self {
        Self::from_le_limbs([other as u64, (other >> 64) as u64, 0, 0])
    }
}

impl From<u64> for Fq {
    fn from(other: u64) -> Self {
        u128::from(other).into()
    }
}

impl From<u32> for Fq {
    fn from(other: u32) -> Self {
        u128::from(other).into()
    }
}

impl From<u16> for Fq {
    fn from(other: u16) -> Self {
        u128::from(other).into()
    }
}

impl From<u8> for Fq {
    fn from(other: u8) -> Self {
        u128::from(other).into()
    }
}

impl From<bool> for Fq {
    fn from(other: bool) -> Self {
        u128::from(other).into()
    }
}

impl Neg for Fq {
    type Output = Self;

    #[inline]
    #[must_use]
    fn neg(self) -> Self {
        let neg = self.neg();
        neg
    }
}

impl<'a> AddAssign<&'a Self> for Fq {
    #[inline]
    fn add_assign(&mut self, other: &Self) {
        *self = self.add(other);
    }
}

impl AddAssign<Self> for Fq {
    #[inline(always)]
    fn add_assign(&mut self, other: Self) {
        *self = self.add(&other);
    }
}

impl<'a> AddAssign<&'a mut Self> for Fq {
    #[inline(always)]
    fn add_assign(&mut self, other: &'a mut Self) {
        *self = self.add(other);
    }
}

impl Add<Self> for Fq {
    type Output = Self;

    #[inline]
    fn add(self, other: Self) -> Self {
        self.add(&other)
    }
}

impl<'a> Add<&'a Fq> for Fq {
    type Output = Self;

    #[inline]
    fn add(self, other: &Self) -> Self {
        self.add(other)
    }
}

impl<'a> Add<&'a mut Self> for Fq {
    type Output = Self;

    #[inline]
    fn add(self, other: &'a mut Self) -> Self {
        self.add(other)
    }
}

impl<'a> SubAssign<&'a Self> for Fq {
    #[inline]
    fn sub_assign(&mut self, other: &Self) {
        *self = self.sub(other);
    }
}

impl SubAssign<Self> for Fq {
    #[inline(always)]
    fn sub_assign(&mut self, other: Self) {
        *self = self.sub(&other);
    }
}

impl<'a> SubAssign<&'a mut Self> for Fq {
    #[inline(always)]
    fn sub_assign(&mut self, other: &'a mut Self) {
        *self = self.sub(other);
    }
}

impl Sub<Self> for Fq {
    type Output = Self;

    #[inline]
    fn sub(self, other: Self) -> Self {
        self.sub(&other)
    }
}

impl<'a> Sub<&'a Fq> for Fq {
    type Output = Self;

    #[inline]
    fn sub(self, other: &Self) -> Self {
        self.sub(other)
    }
}

impl<'a> Sub<&'a mut Self> for Fq {
    type Output = Self;

    #[inline]
    fn sub(self, other: &'a mut Self) -> Self {
        self.sub(other)
    }
}

impl<'a> MulAssign<&'a Self> for Fq {
    fn mul_assign(&mut self, other: &Self) {
        *self = self.mul(other);
    }
}

impl core::ops::MulAssign<Self> for Fq {
    #[inline(always)]
    fn mul_assign(&mut self, other: Self) {
        *self = self.mul(&other);
    }
}

impl<'a> core::ops::MulAssign<&'a mut Self> for Fq {
    #[inline(always)]
    fn mul_assign(&mut self, other: &'a mut Self) {
        *self = self.mul(other);
    }
}

impl Mul<Self> for Fq {
    type Output = Self;

    #[inline(always)]
    fn mul(self, other: Self) -> Self {
        self.mul(&other)
    }
}

impl<'a> Mul<&'a Fq> for Fq {
    type Output = Self;

    #[inline]
    fn mul(self, other: &Self) -> Self {
        self.mul(other)
    }
}

impl<'a> Mul<&'a mut Self> for Fq {
    type Output = Self;

    #[inline(always)]
    fn mul(self, other: &'a mut Self) -> Self {
        self.mul(other)
    }
}

impl<'a> DivAssign<&'a Self> for Fq {
    #[inline(always)]
    fn div_assign(&mut self, other: &Self) {
        self.mul_assign(&other.inverse().unwrap());
    }
}

impl DivAssign<Self> for Fq {
    #[inline(always)]
    fn div_assign(&mut self, other: Self) {
        self.div_assign(&other)
    }
}

impl<'a> DivAssign<&'a mut Self> for Fq {
    #[inline(always)]
    fn div_assign(&mut self, other: &'a mut Self) {
        self.div_assign(&*other)
    }
}

impl Div<Self> for Fq {
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

impl<'a> Div<&'a mut Self> for Fq {
    type Output = Self;

    #[inline(always)]
    fn div(mut self, other: &'a mut Self) -> Self {
        self.div_assign(&*other);
        self
    }
}

impl Sum<Self> for Fq {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, Add::add)
    }
}

impl<'a> Sum<&'a Self> for Fq {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, Add::add)
    }
}

impl Product<Self> for Fq {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ONE, Mul::mul)
    }
}

impl<'a> Product<&'a Self> for Fq {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::ONE, Mul::mul)
    }
}

impl Ord for Fq {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        let mut left = self.to_le_limbs();
        let mut right = other.to_le_limbs();
        left.reverse();
        right.reverse();
        left.cmp(&right)
    }
}

impl PartialOrd for Fq {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for Fq {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        state.write(&self.to_bytes_le())
    }
}

impl Default for Fq {
    fn default() -> Self {
        Self::ZERO
    }
}

impl core::fmt::Debug for Fq {
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
        write!(f, "Fq(0x{})", unsafe {
            core::str::from_utf8_unchecked(&hex_chars)
        })
    }
}
