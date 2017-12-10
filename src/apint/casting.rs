
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
		match self.storage() {
			Storage::Inl => {
				ApInt{
					len: self.len,
					data: ApIntData{inl: unsafe{self.data.inl}}
				}
			}
			Storage::Ext => {
				use std::mem;
				let req_digits = self.len_digits();
				let mut buffer = self.as_digit_slice().to_vec();
				debug_assert_eq!(buffer.len(), buffer.capacity());
				debug_assert_eq!(buffer.len(), req_digits);
				let dst = buffer.as_mut_ptr();
				mem::forget(buffer);
				ApInt{
					len: self.len,
					data: ApIntData {
						ext: unsafe{ Unique::new_unchecked(dst) }
					}
				}
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
		let actual_width = self.width();
		let target_width = target_width.into();

		if target_width == actual_width {
			return Ok(self)
		}

		if !(target_width < self.width()) {
			return
				Error::truncation_bitwidth_too_large(target_width, actual_width)
					.with_annotation(format!(
						"Cannot truncate `ApInt` with a width of {:?}
						 to an `ApInt` with a width of {:?} bits. \
						 Do you mean to extend the instance instead?",
						actual_width.to_usize(),
						target_width.to_usize()))
					.into()
		}

		let actual_req_digits = actual_width.required_digits();
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

	pub fn into_strict_truncate<W>(self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		let actual_width = self.width();
		let target_width = target_width.into();

		if target_width == actual_width {
			return
				Error::truncation_bitwidth_too_large(target_width, actual_width)
					.with_annotation(
						"Cannot strictly truncate an `ApInt` to the same bitwidth.")
					.into()
		}

		assert!(target_width < actual_width);
		self.into_truncate(target_width)
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

	pub fn strict_truncate<W>(&self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		self.clone().into_strict_truncate(target_width)
	}

	// ========================================================================

	pub fn into_zero_extend<W>(self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		let actual_width = self.width();
		let target_width = target_width.into();

		if target_width == actual_width {
			return Ok(self)
		}

		if !(target_width > actual_width) {
			return Error::extension_bitwidth_too_small(target_width, actual_width)
				.with_annotation(format!(
					"Cannot zero-extend bit-width of {:?} to {:?} bits. \
					 Do you mean to truncate the instance instead?",
					actual_width, target_width))
				.into()
		}

		let actual_req_digits = actual_width.required_digits();
		let target_req_digits = target_width.required_digits();

		if actual_req_digits == target_req_digits {
			// We can do a cheap zero-extension here.
			// 
			// In this case we can reuse the heap memory of the consumed `ApInt`.
			// 
			// For example when given an `ApInt` with a `BitWidth` of `100` bits
			// and we want to zero-extend it to `120` bits then both `BitWidth`
			// require exactly `2` digits for their representation and we can simply
			// set the `BitWidth` of the consumed `ApInt` to the target width 
			// and we are done.
			let mut this = self;
			this.len = target_width;
			Ok(this)
		}
		else {
			// In this case we cannot reuse the consumed `ApInt`'s heap memory but
			// must allocate a new buffer that fits for the required amount of digits
			// for the target width. Also we need to `memcpy` the digits of the
			// extended `ApInt` to the newly allocated buffer.
			use digit;
			use std::iter;
			assert!(target_req_digits > actual_req_digits);
			let additional_digits = target_req_digits - actual_req_digits;
			ApInt::from_iter(self.digits().chain(iter::repeat(digit::ZERO)))
		}
	}

	pub fn into_strict_zero_extend<W>(self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		let actual_width = self.width();
		let target_width = target_width.into();

		if target_width == actual_width {
			return
				Error::extension_bitwidth_too_small(target_width, actual_width)
					.with_annotation(
						"Cannot strictly zero-extend an `ApInt` to the same bitwidth.")
					.into()
		}

		assert!(target_width > actual_width);
		self.into_zero_extend(target_width)
	}


	pub fn zero_extend<W>(&self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		self.clone().into_zero_extend(target_width)
	}

	pub fn strict_zero_extend<W>(&self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		self.clone().into_strict_zero_extend(target_width)
	}

	// ========================================================================

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
	pub fn into_sign_extend<W>(self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		let actual_width = self.width();
		let target_width = target_width.into();

		if target_width == actual_width {
			return Ok(self)
		}

		if !(target_width > actual_width) {
			return Error::extension_bitwidth_too_small(target_width, actual_width)
				.with_annotation(
					format!(
						"Cannot sign-extend bit-width of {:?} to {:?} bits. \
						 Do you mean to truncate the instance instead?",
						actual_width, target_width
					)
				)
				.into()
		}

		if self.most_significant_bit() == Bit::Unset {
			return self.into_zero_extend(target_width)
		}

		unimplemented!()
	}

	pub fn into_strict_sign_extend<W>(self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		let actual_width = self.width();
		let target_width = target_width.into();

		if target_width == actual_width {
			return
				Error::extension_bitwidth_too_small(target_width, actual_width)
					.with_annotation(
						"Cannot strictly sign-extend an `ApInt` to the same bitwidth.")
					.into()
		}

		assert!(target_width > actual_width);
		self.into_sign_extend(target_width)
	}

	pub fn sign_extend<W>(&self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		self.clone().into_sign_extend(target_width)
	}

	pub fn strict_sign_extend<W>(&self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		self.clone().into_strict_sign_extend(target_width)
	}

	// ========================================================================

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
