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
}
