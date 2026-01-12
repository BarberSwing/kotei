/// A 16-bit signed fixed-point type.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct I16F<const E: i32>(pub(crate) i16);
