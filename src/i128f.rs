/// A 128-bit signed fixed-point type.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct I128F<const E: i32>(pub(crate) i128);

impl<const E: i32> I128F<E> {
    /// The smallest value that can be represented by this fixed-point type, equal to -2<sup>127</sup> ⋅ 2<sup>E</sup>.
    pub const MIN: Self = Self(i128::MIN);

    /// The largest value that can be represented by this fixed-point type, equal to (2<sup>127</sup> - 1) ⋅ 2<sup>E</sup>.
    pub const MAX: Self = Self(i128::MAX);

    /// The size of this type in bits.
    pub const BITS: u32 = i128::BITS;
}
