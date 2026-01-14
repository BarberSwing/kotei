//! Error-handling API.

/// The error type returned when a floating-point number type conversion fails.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TryFromFloatError {
    /// Value was less than the minimum value for the target fixed-point type.
    Underflow,
    /// Value was greater than the maximum value for the target fixed-point type.
    Overflow,
    /// Value was not a number.
    Nan,
}
