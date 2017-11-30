
use apint::{APInt, APIntData};
use bitwidth::{BitWidth};
use errors::{Error, Result};
use storage::{Storage};
use digit::{Digit};
use digit;

impl Drop for APInt {
	fn drop(&mut self) {
		if self.len.storage() == Storage::Ext {
			let len = self.len_blocks();
			unsafe{
				drop(Vec::from_raw_parts(self.data.ext, len, len))
			}
		}
	}
}


//  =======================================================================
///  Constructors
/// =======================================================================
impl APInt {

	/// Creates a new `APInt` from a given `i8` value with a bit-width of 8.
	#[inline]
	pub fn from_i8(val: i8) -> APInt {
		APInt::from_u8(val as u8)
	}

	/// Creates a new `APInt` from a given `i8` value with a bit-width of 8.
	#[inline]
	pub fn from_u8(val: u8) -> APInt {
		APInt{len: BitWidth::w8(), data: APIntData{inl: Digit(u64::from(val))}}
	}

	/// Creates a new `APInt` from a given `i16` value with a bit-width of 16.
	#[inline]
	pub fn from_i16(val: i16) -> APInt {
		APInt::from_u16(val as u16)
	}

	/// Creates a new `APInt` from a given `i16` value with a bit-width of 16.
	#[inline]
	pub fn from_u16(val: u16) -> APInt {
		APInt{len: BitWidth::w16(), data: APIntData{inl: Digit(u64::from(val))}}
	}

	/// Creates a new `APInt` from a given `i32` value with a bit-width of 32.
	#[inline]
	pub fn from_i32(val: i32) -> APInt {
		APInt::from_u32(val as u32)
	}

	/// Creates a new `APInt` from a given `i32` value with a bit-width of 32.
	#[inline]
	pub fn from_u32(val: u32) -> APInt {
		APInt{len: BitWidth::w32(), data: APIntData{inl: Digit(u64::from(val))}}
	}

	/// Creates a new `APInt` from a given `i64` value with a bit-width of 64.
	#[inline]
	pub fn from_i64(val: i64) -> APInt {
		APInt::from_u64(val as u64)
	}

	/// Creates a new `APInt` from a given `i64` value with a bit-width of 64.
	#[inline]
	pub fn from_u64(val: u64) -> APInt {
		APInt{len: BitWidth::w64(), data: APIntData{inl: Digit(val)}}
	}

	fn from_iter<I, D>(digits: I) -> Result<APInt>
		where I: IntoIterator<Item=Digit, IntoIter=D>,
		      D: Iterator<Item=Digit>
	{
		let buffer = digits.into_iter().collect::<Vec<_>>();
		match buffer.len() {
			0 => {
				Err(Error::expected_non_empty_digits())
			}
			1 => {
				let first_and_only = *buffer
					.first()
					.expect("We have already asserted that `digits.len()` must be at exactly `1`.");
				Ok(APInt{
					len: BitWidth::w64(),
					data: APIntData{inl: first_and_only}
				})
			}
			n => {
				use std::mem;
				let bitwidth = BitWidth::new(n * digit::BITS)
					.expect("We have already asserted that the number of items the given Iterator \
						     iterates over is greater than `1` and thus non-zero and thus a valid `BitWidth`.");
				let ptr_buffer = buffer.as_ptr() as *mut Digit;
				mem::forget(buffer);
				Ok(APInt{len: bitwidth, data: APIntData{ext: ptr_buffer}})
			}
		}
	}
	/// Creates a new `APInt` that represents the repetition of the given digit
	/// up to the given bitwidth.
	/// 
	/// Note: The last digit in the generated sequence is truncated to make the `APInt`'s
	///       value representation fit the given bit-width.
	fn repeat_digit<D>(bitwidth: BitWidth, digit: D) -> APInt
		where D: Into<Digit>
	{
		let digit = digit.into();
		match bitwidth.storage() {
			Storage::Inl => {
				APInt{len: bitwidth, data: APIntData{inl: digit.truncated(bitwidth).unwrap()}}
			}
			Storage::Ext => {
				use std::mem;
				let req_blocks = bitwidth.required_blocks();
				let mut buffer = vec![digit; req_blocks];
				let last_width = bitwidth.to_usize() % digit::BITS;
				buffer.last_mut().unwrap().truncate(last_width).unwrap();
				assert_eq!(buffer.capacity(), req_blocks);
				let ptr_buffer = buffer.as_ptr() as *mut Digit;
				mem::forget(buffer);
				APInt{len: bitwidth, data: APIntData{ext: ptr_buffer}}
			}
		}
	}

	/// Creates a new `APInt` with the given bit-width that represents zero.
	pub fn zero(width: BitWidth) -> APInt {
		APInt::repeat_digit(width, digit::ZERO)
	}

	/// Creates a new `APInt` with the given bit-width that represents one.
	pub fn one(width: BitWidth) -> APInt {
		APInt::from_u64(1).zero_extend(width).unwrap()
	}

	/// Creates a new `APInt` with the given bit-width that has all bits set.
	pub fn zeros(width: BitWidth) -> APInt {
		APInt::zero(width)
	}

	/// Creates a new `APInt` with the given bit-width that has all bits set.
	pub fn ones(width: BitWidth) -> APInt
	{
		APInt::repeat_digit(width, Digit::ones())
	}
}
