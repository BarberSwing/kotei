/// A 64-bit unsigned fixed-point type.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct U64F<const E: i32>(pub(crate) u64);

impl<const E: i32> U64F<E> {
    /// The smallest value that can be represented by this fixed-point type, equal to 0.
    pub const MIN: Self = Self(u64::MIN);

    /// The largest value that can be represented by this fixed-point type, equal to (2<sup>64</sup> - 1) ⋅ 2<sup>E</sup>.
    pub const MAX: Self = Self(u64::MAX);

    /// The size of this type in bits.
    pub const BITS: u32 = u64::BITS;
}
