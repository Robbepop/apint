
use apint::{ApInt, ApIntData};
use errors::{Error, Result};

use bitwidth::{BitWidth};
use storage::{Storage};
use digit::{Bit, Digit};
use traits::Width;
use digit_seq::AsDigitSeq;

use std::ptr::Unique;

impl Clone for ApInt {
	fn clone(&self) -> Self {
		match self.len.storage() {
			Storage::Inl => {
				ApInt{len: self.len, data: ApIntData{inl: unsafe{self.data.inl}}}
			}
			Storage::Ext => {
				let req_digits = self.len_digits();
				let mut buffer = Vec::with_capacity(req_digits);
				buffer.extend_from_slice(self.as_digit_slice());
				debug_assert_eq!(buffer.capacity(), req_digits);
				let dst = buffer.as_mut_ptr();
				::std::mem::forget(buffer);
				ApInt{len: self.len, data: ApIntData{ext: unsafe{ Unique::new_unchecked(dst) }}}
			}
		}
	}
}

//  =======================================================================
///  Casting: Truncation & Extension
/// =======================================================================
impl ApInt {
	/// Tries to truncate this `ApInt` inplace to the given `target_width`
	/// or creates a new `ApInt` with a width of the given `target_width`
	/// if this is not possible.
	/// 
	/// *Note:* This may be a cheap operation if it can reuse the memory of
	///         the old (`self`) instance.
	/// 
	/// *Note:* Truncation is inplace as long as `self` and the resulting
	///         `ApInt` require the same amount of `Digit`s.
	/// 
	/// # Errors
	/// 
	/// - If the `target_width` is *not* less than the current width.
	pub fn into_truncate<W>(self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		let target_width = target_width.into();

		if !(target_width < self.width()) {
			if target_width == self.width() {
				warn!("ApInt::into_truncate: Tried to truncate to the same \
					   bit width as the origin. Do you mean to `clone` or \
					   resize the `ApInt` instance instead?")
			}
			return Err(
				Error::truncation_bitwidth_too_large(target_width, self.width())
					.with_annotation(format!(
						"Cannot truncate `ApInt` with a width of {:?}
						 to an `ApInt` with a width of {:?} bits. \
						 Do you mean to extend the instance instead?",
						self.width().to_usize(),
						target_width.to_usize()))
			)
		}

		let actual_req_digits = self.width().required_digits();
		let target_req_digits = target_width.required_digits();

		if actual_req_digits == target_req_digits {
			// We can do a cheap truncation, here!
			// 
			// For example this could be a truncation from `128` bits
			// to `100` bits which just has to truncate the bits of the
			// most significant digits since both bit width require
			// exactly `2` digits for the representation.
			// The same applies to all bit widths that require the same
			// amount of digits for their representation.
			let excess_width = target_width.excess_bits()
				.expect("We already filtered cases where `excess_bits` may return `None` \
					     by requiring that `self.width() > target_width`.");
			let mut this = self;
			this.most_significant_digit_mut()
				.truncate(excess_width)
				.expect("Excess bits are guaranteed to be within the bounds for valid \
					     truncation of a single `Digit`.");
			Ok(this)
		}
		else {
			// We need to copy the digits for a correct truncation, here!
			// 
			// For example this could be a truncation from `196` bits
			// to `100` bits. The former requires `3` digits whereas the 
			// latter requires only `2`. So allocation of a new sequence
			// is required since no memory can be reused.
			// The same applies to all bit widths that require a different
			// amount of digits for their representation.
			let req_digits = self.digits().take(target_req_digits);
			let truncated_digits = ApInt::from_iter(req_digits).unwrap();
			// We just truncated with digit precision, not with bit precision.
			// The next step is to recursively truncate `truncated_digits`
			// with bit precision.
			// This will simply call the `then` branch of this method.
			if truncated_digits.width() == target_width {
				return Ok(truncated_digits)
			}
			truncated_digits.into_truncate(target_width)
		}
	}

	/// Creates a new `ApInt` that represents this `ApInt` truncated to 
	/// the given target bit-width.
	///
	/// # Panics
	/// 
	/// - If `target_bitwidth` is greater than the `ApInt`'s current bit-width.
	/// - If `target_bitwidth` is zero (`0`).
	/// 
	/// # Note
	/// 
	/// Equal to a call to `clone()` if `target_bitwidth` is equal to this `ApInt`'s bit-width.
	pub fn truncate<W>(&self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		self.clone().into_truncate(target_width)
	}

	/// Creates a new `ApInt` that represents the zero-extension of this `ApInt` to the given target bit-width.
	///
	/// # Semantics (from LLVM)
	/// 
	/// The zext fills the high order bits of the value with zero bits until it reaches the size of the destination bit-width.
	/// When zero extending from `i1`, the result will always be either `0` or `1`.
	/// 
	/// # Panics
	/// 
	/// - If `target_bitwidth` is less than the `ApInt`'s current bit-width.
	/// 
	/// # Note
	/// 
	/// Equal to a call to `clone()` if `target_bitwidth` is equal to this `ApInt`'s bit-width.
	pub fn zero_extend<W>(&self, target_bitwidth: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		let target_bitwidth = target_bitwidth.into();
		let len_bitwidth    = target_bitwidth.to_usize();

		if len_bitwidth < self.len_bits() {
			return Error::extension_bitwidth_too_small(len_bitwidth, self.len_bits())
				.with_annotation(format!(
					"Cannot zero-extend bit-width of {:?} to {:?} bits. \
					 Do you mean to truncate the instance instead?",
					self.len_bits(), target_bitwidth))
				.into()
		}
		if len_bitwidth == self.len_bits() {
			warn!("Zero-extending to the same bit-width is equal to cloning. \
				   Do you mean to clone the object instead?");
			return Ok(self.clone())
		}

		match (target_bitwidth.storage(), self.len.storage()) {
			(Storage::Inl, Storage::Inl) => Ok(ApInt{
				len : target_bitwidth,
				data: ApIntData{
					inl: unsafe{self.data.inl.truncated(target_bitwidth).unwrap()}
				}
			}),
			(Storage::Inl, Storage::Ext) => Ok(ApInt{
				len : target_bitwidth,
				data: ApIntData{
					inl: unsafe{(*self.data.ext.as_ptr()).truncated(target_bitwidth).unwrap()}
				}
			}),
			(Storage::Ext, Storage::Ext) => {
				let req_blocks     = target_bitwidth.required_digits();
				let present_blocks = self.len_digits();
				assert!(present_blocks <= req_blocks);
				let mut buffer: Vec<Digit> = Vec::with_capacity(req_blocks);
				buffer.extend_from_slice(&self.as_digit_slice()[0..present_blocks]);
				let rest = req_blocks - present_blocks;
				buffer.resize(rest, Digit::zero());
				debug_assert_eq!(buffer.capacity(), req_blocks);
				debug_assert_eq!(buffer.len()     , req_blocks);
				Ok(ApInt::from_iter(buffer).unwrap())
			}
			_ => unreachable!()
		}
	}

	/// Creates a new `ApInt` that represents the sign-extension of this `ApInt` to the given target bit-width.
	/// 
	/// 
	/// # Semantic (from LLVM)
	/// 
	/// The ‘sext‘ instruction performs a sign extension by copying the sign bit (highest order bit) of the value until it reaches the target bit-width.
	/// When sign extending from `i1`, the extension always results in `-1` or `0`.
	///
	/// # Panics
	/// 
	/// - If `target_bitwidth` is less than the `ApInt`'s current bit-width.
	/// 
	/// # Note
	/// 
	/// Equal to a call to `clone()` if `target_bitwidth` is equal to this `ApInt`'s bit-width.
	pub fn sign_extend<W>(&self, target_bitwidth: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		let target_bitwidth = target_bitwidth.into();
		let len_bitwidth    = target_bitwidth.to_usize();

		if len_bitwidth < self.len_bits() {
			return Error::extension_bitwidth_too_small(len_bitwidth, self.len_bits())
				.with_annotation(format!(
					"Cannot sign-extend bit-width of {:?} to {:?} bits. \
					 Do you mean to truncate the instance instead?",
					self.len_bits(), target_bitwidth))
				.into()
		}
		if len_bitwidth == self.len_bits() {
			warn!("Sign-extending to the same bit-width is equal to cloning. \
				   Do you mean to clone the object instead?");
			return Ok(self.clone())
		}

		match self.sign_bit() {
			Bit::Set => {
				unimplemented!();
				// if let Some(excess_bits) = target_bitwidth.excess_bits() {
				// 	buffer.last_mut().unwrap().truncate(excess_bits);
				// }
			}
			Bit::Unset => {
				self.zero_extend(target_bitwidth)
			}
		}
	}

	/// TODO: Missing documentation.
	pub fn zero_resize<W>(&self, target_bitwidth: W) -> ApInt
		where W: Into<BitWidth>
	{
		let target_bitwidth = target_bitwidth.into();
		let len_bitwidth    = target_bitwidth.to_usize();

		if len_bitwidth <= self.len_bits() {
			self.truncate(target_bitwidth)
			    .expect("truncate cannot fail if the target bitwidth is smaller than the current")
		}
		else {
			self.zero_extend(target_bitwidth)
			    .expect("zero_extend cannot fail if the target bitwidth is larger than the current")
		}
	}

	/// TODO: Missing documentation.
	pub fn sign_resize<W>(&self, target_bitwidth: W) -> ApInt
		where W: Into<BitWidth>
	{
		let target_bitwidth = target_bitwidth.into();
		let len_bitwidth    = target_bitwidth.to_usize();

		if len_bitwidth <= self.len_bits() {
			self.truncate(target_bitwidth)
			    .expect("truncate cannot fail if the target bitwidth is smaller than the current")
		}
		else {
			self.sign_extend(target_bitwidth)
			    .expect("zero_extend cannot fail if the target bitwidth is larger than the current")
		}
	}
}
