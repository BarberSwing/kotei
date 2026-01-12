/// A 32-bit unsigned fixed-point type.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct U32F<const E: i32>(pub(crate) u32);

impl<const E: i32> U32F<E> {
    /// The smallest value that can be represented by this fixed-point type, equal to 0.
    pub const MIN: Self = Self(u32::MIN);

    /// The largest value that can be represented by this fixed-point type, equal to (2<sup>32</sup> - 1) ⋅ 2<sup>E</sup>.
    pub const MAX: Self = Self(u32::MAX);

    /// The size of this type in bits.
    pub const BITS: u32 = u32::BITS;

    /// Creates a new fixed-point number from an integer significand, equal to `s` ⋅ 2<sup>E</sup>.
    #[inline(always)]
    #[must_use]
    pub const fn new(significand: u32) -> Self {
        Self(significand)
    }
}
