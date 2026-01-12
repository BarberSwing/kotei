use crate::U16F;

/// A 16-bit signed fixed-point type.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct I16F<const E: i32>(pub(crate) i16);

impl<const E: i32> I16F<E> {
    /// The smallest value that can be represented by this fixed-point type, equal to -2<sup>15</sup> ⋅ 2<sup>E</sup>.
    pub const MIN: Self = Self(i16::MIN);

    /// The largest value that can be represented by this fixed-point type, equal to (2<sup>15</sup> - 1) ⋅ 2<sup>E</sup>.
    pub const MAX: Self = Self(i16::MAX);

    /// The size of this type in bits.
    pub const BITS: u32 = i16::BITS;

    /// Creates a new fixed-point number from an integer significand, equal to `s` ⋅ 2<sup>E</sup>.
    #[inline(always)]
    #[must_use]
    pub const fn new(significand: i16) -> Self {
        Self(significand)
    }

    /// Raw transutation from [`u16`].
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u16) -> Self {
        Self(bits.cast_signed())
    }

    /// Creates a native endian fixed-point number from its memory representation as a byte array in native endian byte order.
    ///
    /// As the target platform's native endianness is used, portable code likely wants to use [`from_be_bytes`](Self::from_be_bytes) or [`from_le_bytes`](Self::from_le_bytes), as appropriate, instead.
    #[inline(always)]
    #[must_use]
    pub const fn from_ne_bytes(bytes: [u8; 2]) -> Self {
        Self(i16::from_ne_bytes(bytes))
    }

    /// Creates a fixed-point number from its memory representation as a byte array in big endian byte order.
    #[inline(always)]
    #[must_use]
    pub const fn from_be_bytes(bytes: [u8; 2]) -> Self {
        Self(i16::from_be_bytes(bytes))
    }

    /// Creates a fixed-point number from its memory representation as a byte array in little endian byte order.
    #[inline(always)]
    #[must_use]
    pub const fn from_le_bytes(bytes: [u8; 2]) -> Self {
        Self(i16::from_le_bytes(bytes))
    }

    /// Raw transmutation to [`u16`].
    #[inline(always)]
    #[must_use]
    pub const fn to_bits(self) -> u16 {
        self.0.cast_unsigned()
    }

    /// Returns the memory representation of this fixed-point number as a byte array in native byte order.
    #[inline(always)]
    #[must_use]
    pub const fn to_ne_bytes(self) -> [u8; 2] {
        self.0.to_ne_bytes()
    }

    /// Returns the memory representation of this fixed-point number as a byte array in big-endian (network) byte order.
    #[inline(always)]
    #[must_use]
    pub const fn to_be_bytes(self) -> [u8; 2] {
        self.0.to_be_bytes()
    }

    /// Returns the memory representation of this fixed-point number as a byte array in little-endian byte order.
    #[inline(always)]
    #[must_use]
    pub const fn to_le_bytes(self) -> [u8; 2] {
        self.0.to_le_bytes()
    }

    /// Reinterprets as an unsigned fixed-point number of the same size.
    #[inline(always)]
    #[must_use]
    pub const fn cast_unsigned(self) -> U16F<E> {
        U16F(self.0.cast_unsigned())
    }

    /// Returns the fixed-point significand, equal to `self` ⋅ 2<sup>-E</sup>.
    #[inline(always)]
    #[must_use]
    pub const fn significand(self) -> i16 {
        self.0
    }

    /// Returns the fixed-point exponent.
    #[inline(always)]
    #[must_use]
    pub const fn exponent(self) -> i32 {
        E
    }
}
