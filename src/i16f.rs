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
}
