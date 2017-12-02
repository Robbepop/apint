
use apint::{APInt, APIntData};
use bitwidth::{BitWidth};
use errors::{Error, Result};
use storage::{Storage};
use digit::{Digit};
use digit;

impl Drop for APInt {
	fn drop(&mut self) {
		if self.len.storage() == Storage::Ext {
			let len = self.len_digits();
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

	/// Creates a new `APInt` from a given `i64` value with a bit-width of 64.
	#[inline]
	pub fn from_i128(val: i128) -> APInt {
		APInt::from_u128(val as u128)
	}

	/// Creates a new `APInt` from a given `i64` value with a bit-width of 64.
	#[inline]
	pub fn from_u128(val: u128) -> APInt {
		let buffer = vec![
			Digit((val & 0xFFFF_FFFF_FFFF_FFFF) as u64),
			Digit((val >> digit::BITS) as u64)
		];
		assert_eq!(buffer.len(), 2);
		APInt::from_iter(buffer)
			.expect("We just asserted that `buffer.len()` is exactly 2 \
				     so we can expect `APInt::from_iter` to be successful.")
	}

	/// Creates a new `APInt` from the given iterator over `Digit`s.
	/// 
	/// This results in `APInt` instances with bitwidths that are a multiple
	/// of a `Digit`s bitwidth (e.g. 64 bit).
	/// 
	/// Users of this API may truncate, extend or simply resize the resulting
	/// `APInt` afterwards to obtain the desired bitwidth. This may be very cheap
	/// depending on the difference between the actual and target bitwidths.
	/// For example, `move_truncate`ing a `128` bitwidth `APInt` to `100` is
	/// relatively cheap and won't allocate memory since both `APInt` instances can use
	/// the same amount of `Digit`s.
	/// 
	/// # Errors
	/// 
	/// - If the iterator yields no elements.
	pub(crate) fn from_iter<I>(digits: I) -> Result<APInt>
		where I: IntoIterator<Item=Digit>,
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
	/// 
	/// This is equal to calling `APInt::zero(..)` with the given `width`.
	pub fn zeros(width: BitWidth) -> APInt {
		APInt::zero(width)
	}

	/// Creates a new `APInt` with the given bit-width that has all bits set.
	pub fn ones(width: BitWidth) -> APInt
	{
		APInt::repeat_digit(width, Digit::ones())
	}
}

impl From<u8> for APInt {
	fn from(val: u8) -> APInt {
		APInt::from_u8(val)
	}
}

impl From<i8> for APInt {
	fn from(val: i8) -> APInt {
		APInt::from_i8(val)
	}
}

impl From<u16> for APInt {
	fn from(val: u16) -> APInt {
		APInt::from_u16(val)
	}
}

impl From<i16> for APInt {
	fn from(val: i16) -> APInt {
		APInt::from_i16(val)
	}
}

impl From<u32> for APInt {
	fn from(val: u32) -> APInt {
		APInt::from_u32(val)
	}
}

impl From<i32> for APInt {
	fn from(val: i32) -> APInt {
		APInt::from_i32(val)
	}
}

impl From<u64> for APInt {
	fn from(val: u64) -> APInt {
		APInt::from_u64(val)
	}
}

impl From<i64> for APInt {
	fn from(val: i64) -> APInt {
		APInt::from_i64(val)
	}
}

impl From<u128> for APInt {
	fn from(val: u128) -> APInt {
		APInt::from_u128(val)
	}
}

impl From<i128> for APInt {
	fn from(val: i128) -> APInt {
		APInt::from_i128(val)
	}
}
