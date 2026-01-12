use crate::I8F;

/// An 8-bit unsigned fixed-point type.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct U8F<const E: i32>(pub(crate) u8);

impl<const E: i32> U8F<E> {
    /// The smallest value that can be represented by this fixed-point type, equal to 0.
    pub const MIN: Self = Self(u8::MIN);

    /// The largest value that can be represented by this fixed-point type, equal to (2<sup>8</sup> - 1) ⋅ 2<sup>E</sup>.
    pub const MAX: Self = Self(u8::MAX);

    /// The size of this type in bits.
    pub const BITS: u32 = u8::BITS;

    /// Creates a new fixed-point number from an integer significand, equal to `s` ⋅ 2<sup>E</sup>.
    #[inline(always)]
    #[must_use]
    pub const fn new(significand: u8) -> Self {
        Self(significand)
    }

    /// Raw transutation from [`u8`].
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u8) -> Self {
        Self(bits)
    }

    /// Creates a native endian fixed-point number from its memory representation as a byte array in native endian byte order.
    ///
    /// As the target platform's native endianness is used, portable code likely wants to use [`from_be_bytes`](Self::from_be_bytes) or [`from_le_bytes`](Self::from_le_bytes), as appropriate, instead.
    #[inline(always)]
    #[must_use]
    pub const fn from_ne_bytes(bytes: [u8; 1]) -> Self {
        Self(u8::from_ne_bytes(bytes))
    }

    /// Creates a fixed-point number from its memory representation as a byte array in big endian byte order.
    #[inline(always)]
    #[must_use]
    pub const fn from_be_bytes(bytes: [u8; 1]) -> Self {
        Self(u8::from_be_bytes(bytes))
    }

    /// Creates a fixed-point number from its memory representation as a byte array in little endian byte order.
    #[inline(always)]
    #[must_use]
    pub const fn from_le_bytes(bytes: [u8; 1]) -> Self {
        Self(u8::from_le_bytes(bytes))
    }

    /// Raw transmutation to [`u8`].
    #[inline(always)]
    #[must_use]
    pub const fn to_bits(self) -> u8 {
        self.0
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

    /// Reinterprets as a signed fixed-point number of the same size.
    #[inline(always)]
    #[must_use]
    pub const fn cast_signed(self) -> I8F<E> {
        I8F(self.0.cast_signed())
    }

    /// Returns the fixed-point significand, equal to `self` ⋅ 2<sup>-E</sup>.
    #[inline(always)]
    #[must_use]
    pub const fn significand(self) -> u8 {
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
    /// This function will panic if `self` is zero.
    #[must_use]
    pub const fn ilog2(self) -> i32 {
        self.0.ilog2().cast_signed() + E
    }

    /// Returns the base 2 logarithm of the number, rounded down, returning None if `self` is zero.
    #[must_use]
    pub const fn checked_ilog2(self) -> Option<i32> {
        let Some(x) = self.0.checked_ilog2() else {
            return None;
        };

        let x = x.cast_signed() + E;

        Some(x)
    }
}
