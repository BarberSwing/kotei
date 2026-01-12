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
}
