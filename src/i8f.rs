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
}
