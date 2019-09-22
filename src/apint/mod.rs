mod constructors;
mod casting;
mod utils;
mod bitwise;
mod relational;
mod arithmetic;
mod shift;
mod serialization;
mod to_primitive;

#[cfg(feature = "rand_support")]
mod rand_impl;

#[cfg(feature = "serde_support")]
mod serde_impl;

use crate::digit::{Digit};
use crate::bitwidth::{BitWidth};

pub use self::shift::{ShiftAmount};
pub(crate) use self::to_primitive::{PrimitiveTy};

use std::ptr::NonNull;

/// An arbitrary precision integer with modulo arithmetics similar to machine integers.
pub struct ApInt {
    /// The width in bits of this `ApInt`.
    len : BitWidth,
    /// The actual data (bits) of this `ApInt`.
    data: ApIntData
}

union ApIntData {
    /// Inline storage (up to 64 bits) for small-space optimization.
    inl: Digit,
    /// Extern storage (>64 bits) for larger `ApInt`s.
    ext: NonNull<Digit>
}

/// `ApInt` is safe to send between threads since it does not own
/// aliasing memory and has no reference counting mechanism like `Rc`.
unsafe impl Send for ApInt {}

/// `ApInt` is safe to share between threads since it does not own
/// aliasing memory and has no mutable internal state like `Cell` or `RefCell`.
unsafe impl Sync for ApInt {}
