mod constructors;
mod casting;
mod utils;
mod bitwise;
mod relational;
mod arithmetic;
mod shift;
mod serialization;

use digit::{Digit};
use bitwidth::{BitWidth};

/// An arbitrary precision integer with modulo arithmetics similar to machine integers.
pub struct APInt {
	/// The width in bits of this `APInt`.
	len : BitWidth,
	/// The actual data (bits) of this `APInt`.
	data: APIntData
}

union APIntData {
	/// Inline storage (up to 64 bits) for small-space optimization.
	inl: Digit,
	/// Extern storage (>64 bits) for larger `APInt`s.
	ext: *mut Digit
}
