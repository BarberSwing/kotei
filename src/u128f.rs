/// A 128-bit unsigned fixed-point type.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct U128F<const E: i32>(pub(crate) u128);

impl<const E: i32> U128F<E> {
    /// The smallest value that can be represented by this fixed-point type, equal to 0.
    pub const MIN: Self = Self(u128::MIN);

    /// The largest value that can be represented by this fixed-point type, equal to (2<sup>128</sup> - 1) ⋅ 2<sup>E</sup>.
    pub const MAX: Self = Self(u128::MAX);

    /// The size of this type in bits.
    pub const BITS: u32 = u128::BITS;

    /// Creates a new fixed-point number from an integer significand, equal to `s` ⋅ 2<sup>E</sup>.
    #[inline(always)]
    #[must_use]
    pub const fn new(significand: u128) -> Self {
        Self(significand)
    }

    /// Raw transutation from [`u128`].
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u128) -> Self {
        Self(bits)
    }

    /// Creates a native endian fixed-point number from its memory representation as a byte array in native endian byte order.
    ///
    /// As the target platform's native endianness is used, portable code likely wants to use [`from_be_bytes`](Self::from_be_bytes) or [`from_le_bytes`](Self::from_le_bytes), as appropriate, instead.
    #[inline(always)]
    #[must_use]
    pub const fn from_ne_bytes(bytes: [u8; 16]) -> Self {
        Self(u128::from_ne_bytes(bytes))
    }

    /// Creates a fixed-point number from its memory representation as a byte array in big endian byte order.
    #[inline(always)]
    #[must_use]
    pub const fn from_be_bytes(bytes: [u8; 16]) -> Self {
        Self(u128::from_be_bytes(bytes))
    }

    /// Creates a fixed-point number from its memory representation as a byte array in little endian byte order.
    #[inline(always)]
    #[must_use]
    pub const fn from_le_bytes(bytes: [u8; 16]) -> Self {
        Self(u128::from_le_bytes(bytes))
    }

    /// Raw transmutation to [`u128`].
    #[inline(always)]
    #[must_use]
    pub const fn to_bits(self) -> u128 {
        self.0
    }

    /// Returns the memory representation of this fixed-point number as a byte array in native byte order.
    #[inline(always)]
    #[must_use]
    pub const fn to_ne_bytes(self) -> [u8; 16] {
        self.0.to_ne_bytes()
    }

    /// Returns the memory representation of this fixed-point number as a byte array in big-endian (network) byte order.
    #[inline(always)]
    #[must_use]
    pub const fn to_be_bytes(self) -> [u8; 16] {
        self.0.to_be_bytes()
    }

    /// Returns the memory representation of this fixed-point number as a byte array in little-endian byte order.
    #[inline(always)]
    #[must_use]
    pub const fn to_le_bytes(self) -> [u8; 16] {
        self.0.to_le_bytes()
    }
}
