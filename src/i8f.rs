use ::core::fmt;
use ::core::ops;

use crate::U8F;

/// An 8-bit signed fixed-point type.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct I8F<const E: i32>(pub(crate) i8);

impl<const E: i32> I8F<E> {
    /// The smallest value that can be represented by this fixed-point type, equal to -2<sup>7</sup> ⋅ 2<sup>E</sup>.
    pub const MIN: Self = Self(i8::MIN);

    /// The largest value that can be represented by this fixed-point type, equal to (2<sup>7</sup> - 1) ⋅ 2<sup>E</sup>.
    pub const MAX: Self = Self(i8::MAX);

    /// The size of this type in bits.
    pub const BITS: u32 = i8::BITS;

    /// Creates a new fixed-point number from an integer significand, equal to `s` ⋅ 2<sup>E</sup>.
    #[inline(always)]
    #[must_use]
    pub const fn new(significand: i8) -> Self {
        Self(significand)
    }

    /// Raw transutation from [`u8`].
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u8) -> Self {
        Self(bits.cast_signed())
    }

    /// Creates a fixed-point number from its memory representation as a byte array in native endian byte order.
    ///
    /// As the target platform's native endianness is used, portable code likely wants to use [`from_be_bytes`](Self::from_be_bytes) or [`from_le_bytes`](Self::from_le_bytes), as appropriate, instead.
    #[inline(always)]
    #[must_use]
    pub const fn from_ne_bytes(bytes: [u8; 1]) -> Self {
        Self(i8::from_ne_bytes(bytes))
    }

    /// Creates a fixed-point number from its memory representation as a byte array in big endian byte order.
    #[inline(always)]
    #[must_use]
    pub const fn from_be_bytes(bytes: [u8; 1]) -> Self {
        Self(i8::from_be_bytes(bytes))
    }

    /// Creates a fixed-point number from its memory representation as a byte array in little endian byte order.
    #[inline(always)]
    #[must_use]
    pub const fn from_le_bytes(bytes: [u8; 1]) -> Self {
        Self(i8::from_le_bytes(bytes))
    }

    /// Raw transmutation to [`u8`].
    #[inline(always)]
    #[must_use]
    pub const fn to_bits(self) -> u8 {
        self.0.cast_unsigned()
    }

    /// Returns the memory representation of this fixed-point number as a byte array in native byte order.
    #[inline(always)]
    #[must_use]
    pub const fn to_ne_bytes(self) -> [u8; 1] {
        self.0.to_ne_bytes()
    }

    /// Returns the memory representation of this fixed-point number as a byte array in big-endian (network) byte order.
    #[inline(always)]
    #[must_use]
    pub const fn to_be_bytes(self) -> [u8; 1] {
        self.0.to_be_bytes()
    }

    /// Returns the memory representation of this fixed-point number as a byte array in little-endian byte order.
    #[inline(always)]
    #[must_use]
    pub const fn to_le_bytes(self) -> [u8; 1] {
        self.0.to_le_bytes()
    }

    /// Reinterprets as an unsigned fixed-point number of the same size.
    #[inline(always)]
    #[must_use]
    pub const fn cast_unsigned(self) -> U8F<E> {
        U8F(self.0.cast_unsigned())
    }

    /// Returns the fixed-point significand, equal to `self` ⋅ 2<sup>-E</sup>.
    #[inline(always)]
    #[must_use]
    pub const fn significand(self) -> i8 {
        self.0
    }

    /// Returns the fixed-point exponent.
    #[inline(always)]
    #[must_use]
    pub const fn exponent(self) -> i32 {
        E
    }

    /// Returns the base 2 logarithm of the number, rounded down.
    ///
    /// # Panics
    ///
    /// This function will panic if `self` is zero or negative.
    #[must_use]
    pub const fn ilog2(self) -> i32 {
        self.0.ilog2().cast_signed() + E
    }

    /// Returns the base 2 logarithm of the number, rounded down, returning None if `self` is zero or negative.
    #[must_use]
    pub const fn checked_ilog2(self) -> Option<i32> {
        let Some(x) = self.0.checked_ilog2() else {
            return None;
        };

        let x = x.cast_signed() + E;

        Some(x)
    }

    /// Returns `true` if `self` is positive and `false` if the number is zero or negative.
    #[inline(always)]
    #[must_use]
    pub const fn is_positive(self) -> bool {
        self.0.is_positive()
    }

    /// Returns `true` if `self` is negative and `false` if the number is zero or positive.
    #[inline(always)]
    #[must_use]
    pub const fn is_negative(self) -> bool {
        self.0.is_negative()
    }

    /// Returns a number representing the sign of `self`.
    ///
    ///  - `0` if the number is zero.
    ///  - `1` if the number is positive.
    ///  - `-1` if the number is negative.
    #[inline(always)]
    #[must_use]
    pub const fn signum(self) -> i8 {
        self.0.signum()
    }

    /// Computes `-self`.
    ///
    /// # Panics
    ///
    /// This function will panic on overflow for debug builds, or return a wrapping result for release builds.
    #[inline(always)]
    #[must_use]
    pub const fn neg(self) -> Self {
        Self(-self.0)
    }

    /// Computes `-self`, wrapping around at numeric bounds.
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_neg(self) -> Self {
        Self(self.0.wrapping_neg())
    }

    /// Computes `-self`.
    ///
    /// # Panics
    ///
    /// This function will always panic on overflow, regardless of whether debug assertions are enabled.
    #[inline(always)]
    #[must_use]
    pub const fn strict_neg(self) -> Self {
        Self(self.0.strict_neg())
    }

    /// Computes `-self`, saturating at numeric bounds instead of overflowing.
    #[inline(always)]
    #[must_use]
    pub const fn saturating_neg(self) -> Self {
        Self(self.0.saturating_neg())
    }

    /// Computes `-self`, returning a tuple with a wrapped result and a boolean indicating whether an overflow occurred.
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_neg(self) -> (Self, bool) {
        let (x, overflow) = self.0.overflowing_neg();

        (Self(x), overflow)
    }

    /// Computes `-self`, returning None if overflow occurred.
    #[inline(always)]
    #[must_use]
    pub const fn checked_neg(self) -> Option<Self> {
        let Some(x) = self.0.checked_neg() else {
            return None;
        };

        Some(Self(x))
    }
}

impl<const E: i32> fmt::Debug for I8F<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "I8F<{E}")?;

        f.debug_tuple(">").field(&self.0).finish()
    }
}

impl<const E: i32> fmt::Binary for I8F<E> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Binary::fmt(&self.to_bits(), f)
    }
}

impl<const E: i32> fmt::LowerHex for I8F<E> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::LowerHex::fmt(&self.to_bits(), f)
    }
}

impl<const E: i32> fmt::Octal for I8F<E> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Octal::fmt(&self.to_bits(), f)
    }
}

impl<const E: i32> fmt::UpperHex for I8F<E> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperHex::fmt(&self.to_bits(), f)
    }
}

impl<const E: i32> ops::Neg for I8F<E> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::neg(self)
    }
}
