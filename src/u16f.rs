/// A 16-bit unsigned fixed-point type.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct U16F<const E: i32>(pub(crate) u16);
