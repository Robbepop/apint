
use apint::{APInt, APIntData};
use bitwidth::{BitWidth};
use storage::{Storage};
use digit::{Digit};
use digit;

impl Drop for APInt {
	fn drop(&mut self) {
		use std::mem;
		if self.len.storage() == Storage::Ext {
			let len = self.len_blocks();
			unsafe{
				mem::drop(Vec::from_raw_parts(self.data.ext, len, len))
			}
		}
	}
}

/// Used to construct an `APInt` from raw parts while staying type safe.
#[derive(Debug, Clone, PartialEq, Eq)]
enum RawData {
	/// Used in case of an inline, single-digit `APInt`
	Inl(Digit),
	/// Used in case of a multi-digit `APInt`
	Ext(Vec<Digit>)
}

//  =======================================================================
///  Constructors
/// =======================================================================
impl APInt {

	/// Creates a new `APInt` from a given `i8` value with a bit-width of 8.
	#[inline]
	pub fn from_i8(val: i8) -> APInt {
		APInt{len: BitWidth::w8(), data: APIntData{inl: Digit(val as u64)}}
	}

	/// Creates a new `APInt` from a given `i8` value with a bit-width of 8.
	#[inline]
	pub fn from_u8(val: u8) -> APInt {
		APInt{len: BitWidth::w8(), data: APIntData{inl: Digit(val as u64)}}
	}

	/// Creates a new `APInt` from a given `i16` value with a bit-width of 16.
	#[inline]
	pub fn from_i16(val: i16) -> APInt {
		APInt{len: BitWidth::w16(), data: APIntData{inl: Digit(val as u64)}}
	}

	/// Creates a new `APInt` from a given `i16` value with a bit-width of 16.
	#[inline]
	pub fn from_u16(val: u16) -> APInt {
		APInt{len: BitWidth::w16(), data: APIntData{inl: Digit(val as u64)}}
	}

	/// Creates a new `APInt` from a given `i32` value with a bit-width of 32.
	#[inline]
	pub fn from_i32(val: i32) -> APInt {
		APInt{len: BitWidth::w32(), data: APIntData{inl: Digit(val as u64)}}
	}

	/// Creates a new `APInt` from a given `i32` value with a bit-width of 32.
	#[inline]
	pub fn from_u32(val: u32) -> APInt {
		APInt{len: BitWidth::w32(), data: APIntData{inl: Digit(val as u64)}}
	}

	/// Creates a new `APInt` from a given `i64` value with a bit-width of 64.
	#[inline]
	pub fn from_i64(val: i64) -> APInt {
		APInt{len: BitWidth::w64(), data: APIntData{inl: Digit(val as u64)}}
	}

	/// Creates a new `APInt` from a given `i64` value with a bit-width of 64.
	#[inline]
	pub fn from_u64(val: u64) -> APInt {
		APInt{len: BitWidth::w64(), data: APIntData{inl: Digit(val)}}
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
		APInt::repeat_digit(width, 0)
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
