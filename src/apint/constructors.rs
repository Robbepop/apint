
use apint::{APInt, APIntData};

use bitwidth::{BitWidth, Model, Storage};
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

//  =======================================================================
///  Constructors
/// =======================================================================
impl APInt {

	/// Creates a new `APInt` from a given `i8` value with a bit-width of 8.
	#[inline]
	pub fn from_i8(val: i8) -> APInt {
		APInt{len: BitWidth(8), data: APIntData{inl: Digit(val as u64)}}
	}

	/// Creates a new `APInt` from a given `i8` value with a bit-width of 8.
	#[inline]
	pub fn from_u8(val: u8) -> APInt {
		APInt{len: BitWidth(8), data: APIntData{inl: Digit(val as u64)}}
	}

	/// Creates a new `APInt` from a given `i16` value with a bit-width of 16.
	#[inline]
	pub fn from_i16(val: i16) -> APInt {
		APInt{len: BitWidth(16), data: APIntData{inl: Digit(val as u64)}}
	}

	/// Creates a new `APInt` from a given `i16` value with a bit-width of 16.
	#[inline]
	pub fn from_u16(val: u16) -> APInt {
		APInt{len: BitWidth(16), data: APIntData{inl: Digit(val as u64)}}
	}

	/// Creates a new `APInt` from a given `i32` value with a bit-width of 32.
	#[inline]
	pub fn from_i32(val: i32) -> APInt {
		APInt{len: BitWidth(32), data: APIntData{inl: Digit(val as u64)}}
	}

	/// Creates a new `APInt` from a given `i32` value with a bit-width of 32.
	#[inline]
	pub fn from_u32(val: u32) -> APInt {
		APInt{len: BitWidth(32), data: APIntData{inl: Digit(val as u64)}}
	}

	/// Creates a new `APInt` from a given `i64` value with a bit-width of 64.
	#[inline]
	pub fn from_i64(val: i64) -> APInt {
		APInt{len: BitWidth(64), data: APIntData{inl: Digit(val as u64)}}
	}

	/// Creates a new `APInt` from a given `i64` value with a bit-width of 64.
	#[inline]
	pub fn from_u64(val: u64) -> APInt {
		APInt{len: BitWidth(64), data: APIntData{inl: Digit(val as u64)}}
	}

	fn from_pattern<W, P>(bitwidth: W, pattern: P) -> APInt
		where W: Into<BitWidth>,
		      P: Into<Digit>
	{
		let bitwidth = bitwidth.into();
		let pattern  = pattern.into();
		if bitwidth.to_usize() == 0 { panic!("APInt::from_pattern(0) cannot be instantiated with a bit-width of zero (0).") }
		match BitWidth::from(bitwidth).storage() {
			Storage::Inl => {
				APInt{len: bitwidth, data: APIntData{inl: pattern.truncated(bitwidth).unwrap()}}
			}
			Storage::Ext => {
				use std::mem;
				let req_blocks = bitwidth.required_blocks();
				let mut buffer = vec![pattern; req_blocks];
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
	///
	/// **Error** Returns `InvalidZeroBitWidth` in case of a given target bit-width of zero.
	pub fn zero<W>(bitwidth: W) -> APInt
		where W: Into<BitWidth>
	{
		use self::Model::*;
		let bitwidth = bitwidth.into();
		match bitwidth.model() {
			C8  => APInt::from_u8(0),
			C16 => APInt::from_u16(0),
			C32 => APInt::from_u32(0),
			C64 => APInt::from_u64(0),
			Inl |
			Ext => APInt::from_pattern(bitwidth, 0)
		}
	}

	/// Creates a new `APInt` with the given bit-width that represents one.
	///
	/// **Error** Returns `InvalidZeroBitWidth` in case of a given target bit-width of zero.
	pub fn one<W>(bitwidth: W) -> APInt
		where W: Into<BitWidth>
	{
		use self::Model::*;
		let bitwidth = bitwidth.into();
		match bitwidth.model() {
			C8  => APInt::from_u8(1),
			C16 => APInt::from_u16(1),
			C32 => APInt::from_u32(1),
			C64 => APInt::from_u64(1),
			Inl => APInt::from_pattern(bitwidth, 1),
			Ext => APInt::from_u64(1).zero_extend(bitwidth).unwrap()
		}
	}

	/// Creates a new `APInt` with the given bit-width that has all bits set.
	///
	/// **Error** Returns `InvalidZeroBitWidth` in case of a given target bit-width of zero.
	pub fn zeros<W>(bitwidth: W) -> APInt
		where W: Into<BitWidth>
	{
		APInt::zero(bitwidth)
	}

	/// Creates a new `APInt` with the given bit-width that has all bits set.
	///
	/// **Error** Returns `InvalidZeroBitWidth` in case of a given target bit-width of zero.
	pub fn ones<W>(bitwidth: W) -> APInt
		where W: Into<BitWidth>
	{
		use self::Model::*;
		let bitwidth = bitwidth.into();
		match bitwidth.model() {
			C8  => APInt::from_u8(0xFF),
			C16 => APInt::from_u16(0xFFFF),
			C32 => APInt::from_u32(0xFFFF_FFFF),
			C64 => APInt::from_u64(0xFFFF_FFFF_FFFF_FFFF),
			Inl |
			Ext => APInt::from_pattern(bitwidth, 0xFFFF_FFFF_FFFF_FFFF)
		}
	}

}
