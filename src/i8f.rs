/// An 8-bit signed fixed-point type.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct I8F<const E: i32>(pub(crate) i8);
