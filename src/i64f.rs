use ::core::fmt;
use ::core::ops;

use crate::U64F;
use crate::error::TryFromFloatError;

/// A 64-bit signed fixed-point type.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct I64F<const E: i32>(pub(crate) i64);

impl<const E: i32> I64F<E> {
    /// The smallest value that can be represented by this fixed-point type, equal to -2<sup>63</sup> ⋅ 2<sup>E</sup>.
    pub const MIN: Self = Self(i64::MIN);

    /// The largest value that can be represented by this fixed-point type, equal to (2<sup>63</sup> - 1) ⋅ 2<sup>E</sup>.
    pub const MAX: Self = Self(i64::MAX);

    /// The size of this type in bits.
    pub const BITS: u32 = i64::BITS;

    /// Creates a new fixed-point number from an integer significand, equal to `s` ⋅ 2<sup>E</sup>.
    #[inline(always)]
    #[must_use]
    pub const fn new(significand: i64) -> Self {
        Self(significand)
    }

    /// Tries to create a new fixed-point number from [`f32`]. Returns the nearest multiple of 2<sup>E</sup> to `value`, rounded to the number with even least significant digits if `value` is halfway between two multiples of 2<sup>E</sup>. This returns an error if the source value is not a number, rounds to less than [`Self::MIN`], or rounds to greater than [`Self::MAX`].
    #[must_use]
    pub const fn try_from_f32(value: f32) -> Result<Self, TryFromFloatError> {
        const fn _try_from_f32(value: f32, e: i32) -> Result<i64, TryFromFloatError> {
            const BIAS: i32 = 127;
            const EXPONENT_BITS: i32 = 8;
            const SIGNIFICAND_BITS: i32 = 23;

            const EXPONENT_MASK: u32 = !(!0 << EXPONENT_BITS) << SIGNIFICAND_BITS;
            const IMPLICIT_BIT: u32 = 1 << SIGNIFICAND_BITS;
            const SIGNIFICAND_MASK: u32 = !(!0 << SIGNIFICAND_BITS);
            const SIGN_MASK: u32 = 1 << EXPONENT_BITS + SIGNIFICAND_BITS;
            const ZERO_MASK: u32 = !(!0 << EXPONENT_BITS + SIGNIFICAND_BITS);

            let bits = value.to_bits();

            if bits & ZERO_MASK == 0 {
                return Ok(0);
            }

            let mut significand = bits & SIGNIFICAND_MASK;
            let mut exponent = bits & EXPONENT_MASK;
            let sign = bits & SIGN_MASK;

            if exponent == EXPONENT_MASK {
                if significand != 0 {
                    return Err(TryFromFloatError::Nan);
                } else if sign != 0 {
                    return Err(TryFromFloatError::Underflow);
                } else {
                    return Err(TryFromFloatError::Overflow);
                }
            }

            if exponent != 0 {
                significand |= IMPLICIT_BIT;
                exponent >>= SIGNIFICAND_BITS;
            } else {
                exponent = 1;
            }

            let mut shift = exponent as i32;
            shift = shift.wrapping_sub(const { BIAS + SIGNIFICAND_BITS });
            shift = e.saturating_sub(shift);

            let mut significand = if shift > const { SIGNIFICAND_BITS + 1 } {
                0
            } else if shift > 0 {
                let mut round = !(!0u32 << shift.wrapping_sub(1));
                round = round.wrapping_add(significand >> shift & 1);
                significand = significand.wrapping_add(round);
                significand >>= shift;

                significand as u64
            } else {
                let shift = shift.wrapping_neg().cast_unsigned();
                let significand = significand as u64;

                if shift > significand.leading_zeros() {
                    if sign != 0 {
                        return Err(TryFromFloatError::Underflow);
                    } else {
                        return Err(TryFromFloatError::Overflow);
                    }
                }

                significand << shift
            };

            if sign != 0 {
                if significand > const { i64::MIN.unsigned_abs() as u64 } {
                    return Err(TryFromFloatError::Underflow);
                }

                significand = significand.wrapping_neg();
            } else {
                if significand > const { i64::MAX.unsigned_abs() as u64 } {
                    return Err(TryFromFloatError::Overflow);
                }
            }

            let significand = significand.cast_signed();

            Ok(significand)
        }

        match _try_from_f32(value, E) {
            Ok(s) => Ok(Self(s)),
            Err(err) => Err(err),
        }
    }

    /// Tries to create a new fixed-point number from [`f64`]. Returns the nearest multiple of 2<sup>E</sup> to `value`, rounded to the number with even least significant digits if `value` is halfway between two multiples of 2<sup>E</sup>. This returns an error if the source value is not a number, rounds to less than [`Self::MIN`], or rounds to greater than [`Self::MAX`].
    #[must_use]
    pub const fn try_from_f64(value: f64) -> Result<Self, TryFromFloatError> {
        const fn _try_from_f64(value: f64, e: i32) -> Result<i64, TryFromFloatError> {
            const BIAS: i32 = 1023;
            const EXPONENT_BITS: i32 = 11;
            const SIGNIFICAND_BITS: i32 = 52;

            const EXPONENT_MASK: u64 = !(!0 << EXPONENT_BITS) << SIGNIFICAND_BITS;
            const IMPLICIT_BIT: u64 = 1 << SIGNIFICAND_BITS;
            const SIGNIFICAND_MASK: u64 = !(!0 << SIGNIFICAND_BITS);
            const SIGN_MASK: u64 = 1 << EXPONENT_BITS + SIGNIFICAND_BITS;
            const ZERO_MASK: u64 = !(!0 << EXPONENT_BITS + SIGNIFICAND_BITS);

            let bits = value.to_bits();

            if bits & ZERO_MASK == 0 {
                return Ok(0);
            }

            let mut significand = bits & SIGNIFICAND_MASK;
            let mut exponent = bits & EXPONENT_MASK;
            let sign = bits & SIGN_MASK;

            if exponent == EXPONENT_MASK {
                if significand != 0 {
                    return Err(TryFromFloatError::Nan);
                } else if sign != 0 {
                    return Err(TryFromFloatError::Underflow);
                } else {
                    return Err(TryFromFloatError::Overflow);
                }
            }

            if exponent != 0 {
                significand |= IMPLICIT_BIT;
                exponent >>= SIGNIFICAND_BITS;
            } else {
                exponent = 1;
            }

            let mut shift = exponent as i32;
            shift = shift.wrapping_sub(const { BIAS + SIGNIFICAND_BITS });
            shift = e.saturating_sub(shift);

            if shift > const { SIGNIFICAND_BITS + 1 } {
                significand = 0;
            } else if shift > 0 {
                let mut round = !(!0u64 << shift.wrapping_sub(1));
                round = round.wrapping_add(significand >> shift & 1);
                significand = significand.wrapping_add(round);
                significand >>= shift;
            } else {
                let shift = shift.wrapping_neg().cast_unsigned();

                if shift > significand.leading_zeros() {
                    if sign != 0 {
                        return Err(TryFromFloatError::Underflow);
                    } else {
                        return Err(TryFromFloatError::Overflow);
                    }
                }

                significand <<= shift;
            }

            if sign != 0 {
                if significand > const { i64::MIN.unsigned_abs() } {
                    return Err(TryFromFloatError::Underflow);
                }

                significand = significand.wrapping_neg();
            } else {
                if significand > const { i64::MAX.unsigned_abs() } {
                    return Err(TryFromFloatError::Overflow);
                }
            }

            let significand = significand.cast_signed();

            Ok(significand)
        }

        match _try_from_f64(value, E) {
            Ok(s) => Ok(Self(s)),
            Err(err) => Err(err),
        }
    }

    /// Raw transutation from [`u64`].
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u64) -> Self {
        Self(bits.cast_signed())
    }

    /// Creates a native endian fixed-point number from its memory representation as a byte array in native endian byte order.
    ///
    /// As the target platform's native endianness is used, portable code likely wants to use [`from_be_bytes`](Self::from_be_bytes) or [`from_le_bytes`](Self::from_le_bytes), as appropriate, instead.
    #[inline(always)]
    #[must_use]
    pub const fn from_ne_bytes(bytes: [u8; 8]) -> Self {
        Self(i64::from_ne_bytes(bytes))
    }

    /// Creates a fixed-point number from its memory representation as a byte array in big endian byte order.
    #[inline(always)]
    #[must_use]
    pub const fn from_be_bytes(bytes: [u8; 8]) -> Self {
        Self(i64::from_be_bytes(bytes))
    }

    /// Creates a fixed-point number from its memory representation as a byte array in little endian byte order.
    #[inline(always)]
    #[must_use]
    pub const fn from_le_bytes(bytes: [u8; 8]) -> Self {
        Self(i64::from_le_bytes(bytes))
    }

    /// Raw transmutation to [`u64`].
    #[inline(always)]
    #[must_use]
    pub const fn to_bits(self) -> u64 {
        self.0.cast_unsigned()
    }

    /// Returns the memory representation of this fixed-point number as a byte array in native byte order.
    #[inline(always)]
    #[must_use]
    pub const fn to_ne_bytes(self) -> [u8; 8] {
        self.0.to_ne_bytes()
    }

    /// Returns the memory representation of this fixed-point number as a byte array in big-endian (network) byte order.
    #[inline(always)]
    #[must_use]
    pub const fn to_be_bytes(self) -> [u8; 8] {
        self.0.to_be_bytes()
    }

    /// Returns the memory representation of this fixed-point number as a byte array in little-endian byte order.
    #[inline(always)]
    #[must_use]
    pub const fn to_le_bytes(self) -> [u8; 8] {
        self.0.to_le_bytes()
    }

    /// Reinterprets as an unsigned fixed-point number of the same size.
    #[inline(always)]
    #[must_use]
    pub const fn cast_unsigned(self) -> U64F<E> {
        U64F(self.0.cast_unsigned())
    }

    /// Returns the fixed-point significand, equal to `self` ⋅ 2<sup>-E</sup>.
    #[inline(always)]
    #[must_use]
    pub const fn significand(self) -> i64 {
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
    pub const fn signum(self) -> i64 {
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

impl<const E: i32> fmt::Debug for I64F<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "I64F<{E}")?;

        f.debug_tuple(">").field(&self.0).finish()
    }
}

impl<const E: i32> fmt::Binary for I64F<E> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Binary::fmt(&self.to_bits(), f)
    }
}

impl<const E: i32> fmt::LowerHex for I64F<E> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::LowerHex::fmt(&self.to_bits(), f)
    }
}

impl<const E: i32> fmt::Octal for I64F<E> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Octal::fmt(&self.to_bits(), f)
    }
}

impl<const E: i32> fmt::UpperHex for I64F<E> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperHex::fmt(&self.to_bits(), f)
    }
}

impl<const E: i32> ops::Neg for I64F<E> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::neg(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn try_from_f32_infinity() {
        assert_eq!(
            I64F::<{ i32::MIN }>::try_from_f32(f32::INFINITY),
            Err(TryFromFloatError::Overflow)
        );
        assert_eq!(
            I64F::<0>::try_from_f32(f32::INFINITY),
            Err(TryFromFloatError::Overflow)
        );
        assert_eq!(
            I64F::<{ i32::MAX }>::try_from_f32(f32::INFINITY),
            Err(TryFromFloatError::Overflow)
        );
    }

    #[test]
    fn try_from_f32_max() {
        assert_eq!(
            I64F::<{ f32::MAX_EXP }>::try_from_f32(f32::MAX),
            Ok(I64F::new(1))
        );
    }

    #[test]
    fn try_from_f32_max_negative() {
        assert_eq!(
            I64F::<{ f32::MIN_EXP - 1 }>::try_from_f32(-f32::MIN_POSITIVE),
            Ok(I64F::new(-1))
        );
    }

    #[test]
    fn try_from_f32_max_negative_subnormal() {
        assert_eq!(
            I64F::<{ f32::MIN_EXP - f32::MANTISSA_DIGITS.cast_signed() }>::try_from_f32(
                (-0.0f32).next_down()
            ),
            Ok(I64F::new(-1))
        );
    }

    #[test]
    fn try_from_f32_min() {
        assert_eq!(
            I64F::<{ f32::MAX_EXP }>::try_from_f32(f32::MIN),
            Ok(I64F::new(-1))
        );
    }

    #[test]
    fn try_from_f32_min_positive() {
        assert_eq!(
            I64F::<{ f32::MIN_EXP - 1 }>::try_from_f32(f32::MIN_POSITIVE),
            Ok(I64F::new(1))
        );
    }

    #[test]
    fn try_from_f32_min_positive_subnormal() {
        assert_eq!(
            I64F::<{ f32::MIN_EXP - f32::MANTISSA_DIGITS.cast_signed() }>::try_from_f32(
                0.0f32.next_up()
            ),
            Ok(I64F::new(1))
        );
    }

    #[test]
    fn try_from_f32_nan() {
        assert_eq!(
            I64F::<{ i32::MIN }>::try_from_f32(f32::NAN),
            Err(TryFromFloatError::Nan)
        );
        assert_eq!(
            I64F::<0>::try_from_f32(f32::NAN),
            Err(TryFromFloatError::Nan)
        );
        assert_eq!(
            I64F::<{ i32::MAX }>::try_from_f32(f32::NAN),
            Err(TryFromFloatError::Nan)
        );
    }

    #[test]
    fn try_from_f32_neg_infinity() {
        assert_eq!(
            I64F::<{ i32::MIN }>::try_from_f32(f32::NEG_INFINITY),
            Err(TryFromFloatError::Underflow)
        );
        assert_eq!(
            I64F::<0>::try_from_f32(f32::NEG_INFINITY),
            Err(TryFromFloatError::Underflow)
        );
        assert_eq!(
            I64F::<{ i32::MAX }>::try_from_f32(f32::NEG_INFINITY),
            Err(TryFromFloatError::Underflow)
        );
    }

    #[test]
    fn try_from_f32_round_ties_even() {
        assert_eq!(I64F::<-1>::try_from_f32(-1.25), Ok(I64F::new(-2)));
        assert_eq!(I64F::<-1>::try_from_f32(-0.75), Ok(I64F::new(-2)));
        assert_eq!(I64F::<-1>::try_from_f32(-0.25), Ok(I64F::new(0)));
        assert_eq!(I64F::<-1>::try_from_f32(0.25), Ok(I64F::new(0)));
        assert_eq!(I64F::<-1>::try_from_f32(0.75), Ok(I64F::new(2)));
        assert_eq!(I64F::<-1>::try_from_f32(1.25), Ok(I64F::new(2)));

        assert_eq!(I64F::<0>::try_from_f32(-2.5), Ok(I64F::new(-2)));
        assert_eq!(I64F::<0>::try_from_f32(-1.5), Ok(I64F::new(-2)));
        assert_eq!(I64F::<0>::try_from_f32(-0.5), Ok(I64F::new(0)));
        assert_eq!(I64F::<0>::try_from_f32(0.5), Ok(I64F::new(0)));
        assert_eq!(I64F::<0>::try_from_f32(1.5), Ok(I64F::new(2)));
        assert_eq!(I64F::<0>::try_from_f32(2.5), Ok(I64F::new(2)));

        assert_eq!(I64F::<1>::try_from_f32(-5.0), Ok(I64F::new(-2)));
        assert_eq!(I64F::<1>::try_from_f32(-3.0), Ok(I64F::new(-2)));
        assert_eq!(I64F::<1>::try_from_f32(-1.0), Ok(I64F::new(0)));
        assert_eq!(I64F::<1>::try_from_f32(1.0), Ok(I64F::new(0)));
        assert_eq!(I64F::<1>::try_from_f32(3.0), Ok(I64F::new(2)));
        assert_eq!(I64F::<1>::try_from_f32(5.0), Ok(I64F::new(2)));
    }

    #[test]
    fn try_from_f32_zero() {
        assert_eq!(I64F::<{ i32::MIN }>::try_from_f32(0.0), Ok(I64F::new(0)));
        assert_eq!(I64F::<0>::try_from_f32(0.0), Ok(I64F::new(0)));
        assert_eq!(I64F::<{ i32::MAX }>::try_from_f32(0.0), Ok(I64F::new(0)));
    }

    #[test]
    fn try_from_f64_infinity() {
        assert_eq!(
            I64F::<{ i32::MIN }>::try_from_f64(f64::INFINITY),
            Err(TryFromFloatError::Overflow)
        );
        assert_eq!(
            I64F::<0>::try_from_f64(f64::INFINITY),
            Err(TryFromFloatError::Overflow)
        );
        assert_eq!(
            I64F::<{ i32::MAX }>::try_from_f64(f64::INFINITY),
            Err(TryFromFloatError::Overflow)
        );
    }

    #[test]
    fn try_from_f64_max() {
        assert_eq!(
            I64F::<{ f64::MAX_EXP }>::try_from_f64(f64::MAX),
            Ok(I64F::new(1))
        );
    }

    #[test]
    fn try_from_f64_max_negative() {
        assert_eq!(
            I64F::<{ f64::MIN_EXP - 1 }>::try_from_f64(-f64::MIN_POSITIVE),
            Ok(I64F::new(-1))
        );
    }

    #[test]
    fn try_from_f64_max_negative_subnormal() {
        assert_eq!(
            I64F::<{ f64::MIN_EXP - f64::MANTISSA_DIGITS.cast_signed() }>::try_from_f64(
                (-0.0f64).next_down()
            ),
            Ok(I64F::new(-1))
        );
    }

    #[test]
    fn try_from_f64_min() {
        assert_eq!(
            I64F::<{ f64::MAX_EXP }>::try_from_f64(f64::MIN),
            Ok(I64F::new(-1))
        );
    }

    #[test]
    fn try_from_f64_min_positive() {
        assert_eq!(
            I64F::<{ f64::MIN_EXP - 1 }>::try_from_f64(f64::MIN_POSITIVE),
            Ok(I64F::new(1))
        );
    }

    #[test]
    fn try_from_f64_min_positive_subnormal() {
        assert_eq!(
            I64F::<{ f64::MIN_EXP - f64::MANTISSA_DIGITS.cast_signed() }>::try_from_f64(
                0.0f64.next_up()
            ),
            Ok(I64F::new(1))
        );
    }

    #[test]
    fn try_from_f64_nan() {
        assert_eq!(
            I64F::<{ i32::MIN }>::try_from_f64(f64::NAN),
            Err(TryFromFloatError::Nan)
        );
        assert_eq!(
            I64F::<0>::try_from_f64(f64::NAN),
            Err(TryFromFloatError::Nan)
        );
        assert_eq!(
            I64F::<{ i32::MAX }>::try_from_f64(f64::NAN),
            Err(TryFromFloatError::Nan)
        );
    }

    #[test]
    fn try_from_f64_neg_infinity() {
        assert_eq!(
            I64F::<{ i32::MIN }>::try_from_f64(f64::NEG_INFINITY),
            Err(TryFromFloatError::Underflow)
        );
        assert_eq!(
            I64F::<0>::try_from_f64(f64::NEG_INFINITY),
            Err(TryFromFloatError::Underflow)
        );
        assert_eq!(
            I64F::<{ i32::MAX }>::try_from_f64(f64::NEG_INFINITY),
            Err(TryFromFloatError::Underflow)
        );
    }

    #[test]
    fn try_from_f64_round_ties_even() {
        assert_eq!(I64F::<-1>::try_from_f64(-1.25), Ok(I64F::new(-2)));
        assert_eq!(I64F::<-1>::try_from_f64(-0.75), Ok(I64F::new(-2)));
        assert_eq!(I64F::<-1>::try_from_f64(-0.25), Ok(I64F::new(0)));
        assert_eq!(I64F::<-1>::try_from_f64(0.25), Ok(I64F::new(0)));
        assert_eq!(I64F::<-1>::try_from_f64(0.75), Ok(I64F::new(2)));
        assert_eq!(I64F::<-1>::try_from_f64(1.25), Ok(I64F::new(2)));

        assert_eq!(I64F::<0>::try_from_f64(-2.5), Ok(I64F::new(-2)));
        assert_eq!(I64F::<0>::try_from_f64(-1.5), Ok(I64F::new(-2)));
        assert_eq!(I64F::<0>::try_from_f64(-0.5), Ok(I64F::new(0)));
        assert_eq!(I64F::<0>::try_from_f64(0.5), Ok(I64F::new(0)));
        assert_eq!(I64F::<0>::try_from_f64(1.5), Ok(I64F::new(2)));
        assert_eq!(I64F::<0>::try_from_f64(2.5), Ok(I64F::new(2)));

        assert_eq!(I64F::<1>::try_from_f64(-5.0), Ok(I64F::new(-2)));
        assert_eq!(I64F::<1>::try_from_f64(-3.0), Ok(I64F::new(-2)));
        assert_eq!(I64F::<1>::try_from_f64(-1.0), Ok(I64F::new(0)));
        assert_eq!(I64F::<1>::try_from_f64(1.0), Ok(I64F::new(0)));
        assert_eq!(I64F::<1>::try_from_f64(3.0), Ok(I64F::new(2)));
        assert_eq!(I64F::<1>::try_from_f64(5.0), Ok(I64F::new(2)));
    }

    #[test]
    fn try_from_f64_zero() {
        assert_eq!(I64F::<{ i32::MIN }>::try_from_f64(0.0), Ok(I64F::new(0)));
        assert_eq!(I64F::<0>::try_from_f64(0.0), Ok(I64F::new(0)));
        assert_eq!(I64F::<{ i32::MAX }>::try_from_f64(0.0), Ok(I64F::new(0)));
    }
}
