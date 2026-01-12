/// A 64-bit signed fixed-point type.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct I64F<const E: i32>(pub(crate) i64);

impl<const E: i32> I64F<E> {
    /// The smallest value that can be represented by this fixed-point type, equal to -2<sup>63</sup> ⋅ 2<sup>E</sup>.
    pub const MIN: Self = Self(i64::MIN);

    /// The largest value that can be represented by this fixed-point type, equal to (2<sup>63</sup> - 1) ⋅ 2<sup>E</sup>.
    pub const MAX: Self = Self(i64::MAX);

    /// The size of this type in bits.
    pub const BITS: u32 = i64::BITS;
}
