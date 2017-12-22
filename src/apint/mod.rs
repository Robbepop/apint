mod constructors;
mod casting;
mod utils;
mod bitwise;
mod relational;
mod arithmetic;
mod shift;
mod serialization;

#[cfg(feature = "rand_support")]
mod rand_impl;

#[cfg(feature = "serde_support")]
mod serde_impl;

use digit::{Digit};
use bitwidth::{BitWidth};

pub(crate) use self::shift::{ShiftAmount};

use std::ptr::Unique;

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
	ext: Unique<Digit>
}

/// `ApInt` as defined is safe to implement `Send` since it does not own
/// aliasing memory and has no reference counting mechanism like `Rc`.
unsafe impl Send for ApInt {}

/// `ApInt` as defined is safe to implement `Sync` since it does not own
/// aliasing memory and has no mutable internal state like `Cell` or `RefCell`.
unsafe impl Sync for ApInt {}
