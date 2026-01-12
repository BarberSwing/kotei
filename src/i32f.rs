/// A 32-bit signed fixed-point type.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct I32F<const E: i32>(pub(crate) i32);

impl<const E: i32> I32F<E> {
    /// The smallest value that can be represented by this fixed-point type, equal to -2<sup>31</sup> ⋅ 2<sup>E</sup>.
    pub const MIN: Self = Self(i32::MIN);

    /// The largest value that can be represented by this fixed-point type, equal to (2<sup>31</sup> - 1) ⋅ 2<sup>E</sup>.
    pub const MAX: Self = Self(i32::MAX);

    /// The size of this type in bits.
    pub const BITS: u32 = i32::BITS;
}
