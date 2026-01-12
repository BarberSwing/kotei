/// A 64-bit signed fixed-point type.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct I64F<const E: i32>(pub(crate) i64);
