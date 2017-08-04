mod constructors;
mod casting;
mod utils;
mod bitwise;
mod relational;
mod arithmetic;
mod shift;
// mod serialization;

use digit::{Digit};
use bitwidth::{BitWidth};

pub struct APInt {
	len : BitWidth,
	data: APIntData
}

union APIntData {
	inl: Digit,
	ext: *mut Digit
}
