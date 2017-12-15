
use apint::{ApInt, ApIntData};
use errors::{Error, Result};

use bitwidth::{BitWidth};
use storage::{Storage};
use digit::{Bit};
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
				let mut buffer = self.as_digit_slice()
					.to_vec()
					.into_boxed_slice();
				assert_eq!(buffer.len(), req_digits);
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

impl ApInt {
	// Assigns `rhs` to this `ApInt`.
	//
	// This mutates digits and may affect the bitwidth of `self`
	// which **might result in an expensive operations**.
	//
	// After this operation `rhs` and `self` are equal to each other.
	pub fn assign(&mut self, rhs: &ApInt) {
		if self.len_digits() == rhs.len_digits() {
			// If `self` and `rhs` require the same amount of digits
			// for their representation we can simply utilize `ApInt`
			// invariants and basically `memcpy` from `rhs` to `self`.
			// Afterwards a simple adjustment of the length is sufficient.
			// (At the end of this method.)
			self.as_digit_slice_mut()
			    .copy_from_slice(rhs.as_digit_slice());
		}
		else {
			// In this case `rhs` and `self` require an unequal amount
			// of digits for their representation which means that the
			// digits that may be allocated by `self` must be dropped.
			//
			// Note that `ApInt::drop_digits` only deallocates if possible.
			unsafe{ self.drop_digits(); }

			match rhs.storage() {
				Storage::Inl => {
					// If `rhs` is a small `ApInt` we can simply update
					// the `digit` field of `self` and we are done.
					self.data.inl = unsafe{ rhs.data.inl };
				}
				Storage::Ext => {
					// If `rhs` is a large heap-allocated `ApInt` we first
					// need to expensively clone its buffer and feed it to `self`.
					let cloned = rhs.clone();
					self.data.ext = unsafe{ cloned.data.ext };
					use std::mem;
					mem::forget(cloned);
				}
			}
		}
		// Since all cases may need bit width adjustment we outsourced it
		// to the end of this method.
		self.len = rhs.len;
	}

	/// Strictly assigns `rhs` to this `ApInt`.
	/// 
	/// After this operation `rhs` and `self` are equal to each other.
	/// 
	/// **Note:** Strict assigns protect against mutating the bit width
	/// of `self` and thus return an error instead of executing a probably
	/// expensive `assign` operation.
	/// 
	/// # Errors
	/// 
	/// - If `rhs` and `self` have unmatching bit widths.
	pub fn strict_assign(&mut self, rhs: &ApInt) -> Result<()> {
		if self.width() != rhs.width() {
			return Error::unmatching_bitwidths(self.width(), rhs.width())
				.with_annotation(format!(
					"Occured while trying to `strict_assign` {:?} to {:?}.", self, rhs))
				.into()
		}
		self.as_digit_slice_mut()
			.copy_from_slice(rhs.as_digit_slice());
		Ok(())
	}
}

//  =======================================================================
///  Casting: Truncation & Extension
/// =======================================================================
impl ApInt {
	/// Tries to truncate this `ApInt` inplace to the given `target_width`
	/// or creates a new `ApInt` with a width of `target_width` otherwise.
	/// 
	/// # Note
	/// 
	/// - This may be a cheap operation if it can reuse the memory of
	///   the old (`self`) instance. Truncation is inplace as long as `self` and the resulting
	///   `ApInt` require the same amount of `Digit`s.
	/// - This is equal to a simple `move` operation if `target_width`
	///   is equal to the given `ApInt` bitwidth.
	/// 
	/// # Errors
	/// 
	/// - If the `target_width` is greater than the current width.
	pub fn into_truncate<W>(self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		let actual_width = self.width();
		let target_width = target_width.into();

		if target_width == actual_width {
			return Ok(self)
		}

		if target_width > self.width() {
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

	/// Tries to truncate this `ApInt` inplace to the given `target_width`
	/// or creates a new `ApInt` with a width of `target_width` otherwise.
	/// 
	/// [For more information look into `into_truncate`](struct.ApInt.html#method.into_truncate).
	/// 
	/// # Errors
	/// 
	/// - If `target_width` is equal to or greater than the bitwidth of the given `ApInt`.
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

	/// Creates a new `ApInt` that represents the given `ApInt` truncated
	/// to the given target `BitWidth`.
	/// 
	/// # Note
	/// 
	/// - This will never reuse memory inplace and may even
	///   heap-allocate if the given `ApInt` is larger than what
	///   can be space-optimized.
	/// - This is equal to a call to `clone()` if `target_width`
	///   is equal to the bitwidth of the given `ApInt`.
	/// - This will always perform worse than `into_truncate`.
	/// 
	/// # Errors
	/// 
	/// - If the `target_width` is greater than the current width.
	pub fn truncate<W>(&self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		self.clone().into_truncate(target_width)
	}

	/// Creates a new `ApInt` that represents the given `ApInt` truncated
	/// to the given target `BitWidth`.
	/// 
	/// [For more information look into `truncate`](struct.ApInt.html#method.truncate).
	/// 
	/// # Errors
	/// 
	/// - If `target_width` is equal to or greater than or equal to the bitwidth
	///   of the given `ApInt`.
	pub fn strict_truncate<W>(&self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		self.clone().into_strict_truncate(target_width)
	}

	// ========================================================================

	/// Tries to zero-extend this `ApInt` inplace to the given `target_width`
	/// or creates a new `ApInt` with a width of `target_width` otherwise.
	/// 
	/// # Note
	/// 
	/// - This may be a cheap operation if it can reuse the memory of
	///   the old (`self`) instance. Zero-extension is inplace as long as `self`
	///   and the resulting `ApInt` require the same amount of `Digit`s.
	/// - This is equal to a simple `move` operation if `target_width`
	///   is equal to the given `ApInt` bitwidth.
	/// 
	/// # Errors
	/// 
	/// - If the `target_width` is less than the current width.
	pub fn into_zero_extend<W>(self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		let actual_width = self.width();
		let target_width = target_width.into();

		if target_width == actual_width {
			return Ok(self)
		}

		if target_width < actual_width {
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
			ApInt::from_iter(
				self.digits()
				    .chain(iter::repeat(digit::ZERO).take(additional_digits)))
				.and_then(|apint| apint.into_truncate(target_width))
		}
	}

	/// Tries to zero-extend this `ApInt` inplace to the given `target_width`
	/// or creates a new `ApInt` with a width of `target_width` otherwise.
	/// 
	/// [For more information look into `into_zero_extend`](struct.ApInt.html#method.into_zero_extend).
	/// 
	/// # Errors
	/// 
	/// - If `target_width` is equal to or less than the bitwidth of the given `ApInt`.
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

	/// Creates a new `ApInt` that represents the given `ApInt` zero-extended
	/// to the given target `BitWidth`.
	/// 
	/// # Note
	/// 
	/// - This will never reuse memory inplace and may even
	///   heap-allocate if the given `ApInt` is larger than what
	///   can be space-optimized.
	/// - This is equal to a call to `clone()` if `target_width`
	///   is equal to the bitwidth of the given `ApInt`.
	/// - This will always perform worse than `into_zero_extend`.
	/// 
	/// # Errors
	/// 
	/// - If the `target_width` is less than the current width.
	pub fn zero_extend<W>(&self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		self.clone().into_zero_extend(target_width)
	}

	/// Creates a new `ApInt` that represents the given `ApInt` zero-extended
	/// to the given target `BitWidth`.
	/// 
	/// [For more information look into `zero_extend`](struct.ApInt.html#method.zero_extend).
	/// 
	/// # Errors
	/// 
	/// - If `target_width` is equal to or less than or equal to the bitwidth
	///   of the given `ApInt`.
	pub fn strict_zero_extend<W>(&self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		self.clone().into_strict_zero_extend(target_width)
	}

	// ========================================================================

	/// Tries to sign-extend this `ApInt` inplace to the given `target_width`
	/// or creates a new `ApInt` with a width of `target_width` otherwise.
	/// 
	/// # Note
	/// 
	/// - This may be a cheap operation if it can reuse the memory of
	///   the old (`self`) instance. Sign-extension is inplace as long as `self`
	///   and the resulting `ApInt` require the same amount of `Digit`s.
	/// - This is equal to a simple `move` operation if `target_width`
	///   is equal to the given `ApInt` bitwidth.
	/// 
	/// # Errors
	/// 
	/// - If the `target_width` is less than the current width.
	pub fn into_sign_extend<W>(self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		let actual_width = self.width();
		let target_width = target_width.into();

		if target_width == actual_width {
			return Ok(self)
		}

		if target_width < actual_width {
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

		let actual_req_digits = actual_width.required_digits();
		let target_req_digits = target_width.required_digits();

		if actual_req_digits == target_req_digits {
			// We can do a cheap sign-extension here.
			// 
			// In this case we can reuse the heap memory of the consumed `ApInt`.
			// 
			// For example when given an `ApInt` with a `BitWidth` of `100` bits
			// and we want to sign-extend it to `120` bits then both `BitWidth`
			// require exactly `2` digits for their representation and we can simply
			// set the `BitWidth` of the consumed `ApInt` to the target width
			// and we are done.

			let mut this = self;
			this.len = target_width;

			// Fill most-significant-digit of `self` with `1` starting from its
			// most-significant bit up to the `target_width`.
			use digit;
			let start = digit::BITS - (this.most_significant_digit().repr().leading_zeros() as usize);
			let end   = target_width.excess_bits().unwrap_or(digit::BITS);
			this.most_significant_digit_mut().set_all_within(start..end)?;

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


			// Fill most-significant-digit of `self` with `1` starting from its most-significant bit.
			let mut this = self;
			let start = digit::BITS - (this.most_significant_digit().repr().leading_zeros() as usize);
			this.most_significant_digit_mut().set_all_within(start..digit::BITS)?;

			ApInt::from_iter(
				this.digits()
				    .chain(iter::repeat(digit::ONES).take(additional_digits)))
				.and_then(|apint| apint.into_truncate(target_width))
		}
	}

	/// Tries to sign-extend this `ApInt` inplace to the given `target_width`
	/// or creates a new `ApInt` with a width of `target_width` otherwise.
	/// 
	/// [For more information look into `into_sign_extend`](struct.ApInt.html#method.into_sign_extend).
	/// 
	/// # Errors
	/// 
	/// - If `target_width` is equal to or less than the bitwidth of the given `ApInt`.
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

	/// Creates a new `ApInt` that represents the given `ApInt` sign-extended
	/// to the given target `BitWidth`.
	/// 
	/// # Note
	/// 
	/// - This will never reuse memory inplace and may even
	///   heap-allocate if the given `ApInt` is larger than what
	///   can be space-optimized.
	/// - This is equal to a call to `clone()` if `target_width`
	///   is equal to the bitwidth of the given `ApInt`.
	/// - This will always perform worse than `into_sign_extend`.
	/// 
	/// # Errors
	/// 
	/// - If the `target_width` is less than the current width.
	pub fn sign_extend<W>(&self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		self.clone().into_sign_extend(target_width)
	}

	/// Creates a new `ApInt` that represents the given `ApInt` sign-extended
	/// to the given target `BitWidth`.
	/// 
	/// [For more information look into `sign_extend`](struct.ApInt.html#method.sign_extend).
	/// 
	/// # Errors
	/// 
	/// - If `target_width` is equal to or less than or equal to the bitwidth
	///   of the given `ApInt`.
	pub fn strict_sign_extend<W>(&self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		self.clone().into_strict_sign_extend(target_width)
	}

	// ========================================================================

	/// Resizes the given `ApInt` inplace to the given `target_width`.
	/// 
	/// # Note
	/// 
	/// This operation will forward to
	/// 
	/// - [`into_truncate`](struct.ApInt.html#method.into_truncate)
	/// if `target_width` is less than or equal to the width of
	/// the given `ApInt`
	/// - [`into_zero_extend`](struct.ApInt.html#method.into_zero_extend)
	/// otherwise
	pub fn into_zero_resize<W>(self, target_width: W) -> ApInt
		where W: Into<BitWidth>
	{
		let actual_width = self.width();
		let target_width = target_width.into();

		if target_width <= actual_width {
			self.into_truncate(target_width)
			    .expect("It was asserted that the target truncation `BitWidth` \
			             is valid for this operation.")
		}
		else {
			self.into_zero_extend(target_width)
			    .expect("It was asserted that the target zero-extension `BitWidth` \
			             is valid for this operation.")
		}
	}

	/// Tries to strictly resize the given `ApInt` inplace to the given `target_width`.
	/// 
	/// # Note
	/// 
	/// This operation will forward to
	/// 
	/// - [`into_strict_truncate`](struct.ApInt.html#method.into_strict_truncate)
	/// if `target_width` is less than or equal to the width of
	/// the given `ApInt`
	/// - [`into_strict_zero_extend`](struct.ApInt.html#method.into_strict_zero_extend)
	/// otherwise
	/// 
	/// # Errors
	/// 
	/// - If `target_width` is equal to the width of the given `ApInt`.
	pub fn into_strict_zero_resize<W>(self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		let actual_width = self.width();
		let target_width = target_width.into();

		if target_width <= actual_width {
			self.into_strict_truncate(target_width)
		}
		else {
			self.into_strict_zero_extend(target_width)
		}
	}

	/// Resizes the given `ApInt` inplace to the given `target_width`.
	/// 
	/// # Note
	/// 
	/// This operation will forward to
	/// 
	/// - [`into_truncate`](struct.ApInt.html#method.into_truncate)
	/// if `target_width` is less than or equal to the width of
	/// the given `ApInt`
	/// - [`into_sign_extend`](struct.ApInt.html#method.into_sign_extend)
	/// otherwise
	pub fn into_sign_resize<W>(self, target_width: W) -> ApInt
		where W: Into<BitWidth>
	{
		let actual_width = self.width();
		let target_width = target_width.into();

		if target_width <= actual_width {
			self.into_truncate(target_width)
			    .expect("It was asserted that the target truncation `BitWidth` \
			             is valid for this operation.")
		}
		else {
			self.into_sign_extend(target_width)
			    .expect("It was asserted that the target sign-extension `BitWidth` \
			             is valid for this operation.")
		}
	}

	/// Tries to strictly resize the given `ApInt` inplace to the given `target_width`.
	/// 
	/// # Note
	/// 
	/// This operation will forward to
	/// 
	/// - [`into_strict_truncate`](struct.ApInt.html#method.into_strict_truncate)
	/// if `target_width` is less than or equal to the width of
	/// the given `ApInt`
	/// - [`into_strict_sign_extend`](struct.ApInt.html#method.into_strict_sign_extend)
	/// otherwise
	/// 
	/// # Errors
	/// 
	/// - If `target_width` is equal to the width of the given `ApInt`.
	pub fn into_strict_sign_resize<W>(self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		let actual_width = self.width();
		let target_width = target_width.into();

		if target_width <= actual_width {
			self.into_strict_truncate(target_width)
		}
		else {
			self.into_strict_sign_extend(target_width)
		}
	}

	/// Returns a new `ApInt` that is equal to the given `ApInt`
	/// zero-resized to the given `target_width`.
	/// 
	/// # Note
	/// 
	/// - This will never reuse memory inplace and may even
	///   heap-allocate if the given `ApInt` is larger than what
	///   can be space-optimized.
	/// - This is equal to a call to `clone()` if `target_width`
	///   is equal to the bitwidth of the given `ApInt`.
	/// - This will always perform worse than a call to
	///   [`into_zero_resize`](struct.ApInt.html#method.into_zero_resize)
	pub fn zero_resize<W>(&self, target_width: W) -> ApInt
		where W: Into<BitWidth>
	{
		self.clone().into_zero_resize(target_width)
	}

	/// Tries to create an `ApInt` that is equal to the given `ApInt`
	/// strictly zero-resized to the given `target_width`.
	/// 
	/// # Note
	/// 
	/// - This will never reuse memory inplace and may even
	///   heap-allocate if the given `ApInt` is larger than what
	///   can be space-optimized.
	/// - This is equal to a call to `clone()` if `target_width`
	///   is equal to the bitwidth of the given `ApInt`.
	/// - This will always perform worse than a call to
	///   [`into_strict_zero_resize`](struct.ApInt.html#method.into_strict_zero_resize)
	/// 
	/// # Errors
	/// 
	/// - If `target_width` is equal to the width of the given `ApInt`.
	pub fn strict_zero_resize<W>(&self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		self.clone().into_strict_zero_resize(target_width)
	}

	/// Returns a new `ApInt` that is equal to the given `ApInt`
	/// sign-resized to the given `target_width`.
	/// 
	/// # Note
	/// 
	/// - This will never reuse memory inplace and may even
	///   heap-allocate if the given `ApInt` is larger than what
	///   can be space-optimized.
	/// - This is equal to a call to `clone()` if `target_width`
	///   is equal to the bitwidth of the given `ApInt`.
	/// - This will always perform worse than a call to
	///   [`into_sign_resize`](struct.ApInt.html#method.into_sign_resize)
	pub fn sign_resize<W>(&self, target_width: W) -> ApInt
		where W: Into<BitWidth>
	{
		self.clone().into_sign_resize(target_width)
	}

	/// Tries to create an `ApInt` that is equal to the given `ApInt`
	/// strictly sign-resized to the given `target_width`.
	/// 
	/// # Note
	/// 
	/// - This will never reuse memory inplace and may even
	///   heap-allocate if the given `ApInt` is larger than what
	///   can be space-optimized.
	/// - This is equal to a call to `clone()` if `target_width`
	///   is equal to the bitwidth of the given `ApInt`.
	/// - This will always perform worse than a call to
	///   [`into_strict_sign_resize`](struct.ApInt.html#method.into_strict_sign_resize)
	/// 
	/// # Errors
	/// 
	/// - If `target_width` is equal to the width of the given `ApInt`.
	pub fn strict_sign_resize<W>(&self, target_width: W) -> Result<ApInt>
		where W: Into<BitWidth>
	{
		self.clone().into_strict_sign_resize(target_width)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn test_inl_widths() -> impl Iterator<Item=BitWidth> {
		[ 1,  2,  4,  8, 16, 32, 64,
		 10, 20, 30, 40, 50, 60, 63].into_iter()
		                            .map(|&n| BitWidth::new(n).unwrap())
	}

	mod clone {
		use super::*;

		/// Test Clone impl of `ApInt`.
		/// 
		/// Invariants between the origin `ApInt` `o` and for the cloned `c` are:
		/// 
		/// - `o` and `c` have same bit widths
		/// - If `o` is heap-allocated then `c` is, too and vice versa for stack.
		/// - `o` and `c` have an equal amount of digits and the values of their
		///   digits is equal and in the same order.
		/// - Memory addresses of `c` and `o` won't overlap. (No aliasing!)
		///   This is enforced by safe Rust.
		#[test]
		#[ignore]
		fn clone() {

		}
	}

	mod assign {
		use super::*;

		/// Test for assigning to the same bit width.
		#[test]
		#[ignore]
		fn equal_width() {
		}

		/// Test for assigning between bit widths that
		/// can be stored entirely on the stack.
		#[test]
		#[ignore]
		fn inl() {
		}

		/// Test for assigning where a heap-allocated
		/// `ApInt` is truncated to a purely stack-allocated one.
		#[test]
		#[ignore]
		fn ext_to_inl() {
		}

		/// Test for assigning where origin and target `ApInt`
		/// are both entirely heap-allocated.
		#[test]
		#[ignore]
		fn ext() {
		}
	}

	mod strict_assign {
		use super::*;

		/// Test for assigning to a non-strict assigning width
		/// which results in an error.
		#[test]
		#[ignore]
		fn fail_strict() {
		}

		/// Test to assert equality to non-strict assign.
		#[test]
		#[ignore]
		fn equal_to_assign() {
		}
	}

	mod into_truncate {
		use super::*;

		/// Test for truncation to the same bit width.
		#[test]
		#[ignore]
		fn equal_width() {
		}

		/// Test for truncation to a bit width that is
		/// greater than the current bit width and thus an error.
		#[test]
		#[ignore]
		fn fail_width() {
		}

		/// Test for truncation between bit widths that
		/// can be stored entirely on the stack.
		#[test]
		#[ignore]
		fn inl() {
		}

		/// Test for truncation where a heap-allocated
		/// `ApInt` is truncated to a purely stack-allocated one.
		#[test]
		#[ignore]
		fn ext_to_inl() {
		}

		/// Test for truncation where origin and target `ApInt`
		/// are both entirely heap-allocated.
		#[test]
		#[ignore]
		fn ext() {
		}
	}

	mod into_strict_truncate {
		use super::*;

		/// Test for truncation to a non-strict truncation width
		/// which results in an error.
		#[test]
		#[ignore]
		fn fail_strict() {
		}

		/// Test to assert equality for any other case than the
		/// strict truncation width case to `into_truncate`.
		#[test]
		#[ignore]
		fn equal_to_into_truncate() {
		}
	}

	mod truncate {
		use super::*;

		/// Test to assert behavioural equality to `into_truncate`.
		#[test]
		#[ignore]
		fn equal_to_into_truncate() {
		}
	}

	mod strict_truncate {
		use super::*;

		/// Test for truncation to a non-strict truncation width
		/// which results in an error.
		#[test]
		#[ignore]
		fn fail_strict() {
		}

		/// Test to assert behavioural equality to `into_strict_truncate`.
		#[test]
		#[ignore]
		fn equal_to_into_strict_truncate() {
		}
	}

	mod into_zero_extend {
		use super::*;

		/// Test for zero-extension to the same bit width.
		#[test]
		#[ignore]
		fn equal_width() {
		}

		/// Test for zero-extension to a bit width that is
		/// greater than the current bit width and thus an error.
		#[test]
		#[ignore]
		fn fail_width() {
		}

		/// Test for zero-extension between bit widths that
		/// can be stored entirely on the stack.
		#[test]
		#[ignore]
		fn inl() {
		}

		/// Test for zero-extension where a heap-allocated
		/// `ApInt` is zero-extended to a purely stack-allocated one.
		#[test]
		#[ignore]
		fn ext_to_inl() {
		}

		/// Test for zero-extension where origin and target `ApInt`
		/// are both entirely heap-allocated.
		#[test]
		#[ignore]
		fn ext() {
		}
	}

	mod into_strict_zero_extend {
		use super::*;

		/// Test for zero-extension to a non-strict zero-extension width
		/// which results in an error.
		#[test]
		#[ignore]
		fn fail_strict() {
		}

		/// Test to assert equality for any other case than the
		/// strict zero-extension width case to `into_zero_extend`.
		#[test]
		#[ignore]
		fn equal_to_into_zero_extend() {
		}
	}

	mod zero_extend {
		use super::*;

		/// Test to assert behavioural equality to `into_zero_extend`.
		#[test]
		#[ignore]
		fn equal_to_into_zero_extend() {
		}
	}

	mod strict_zero_extend {
		use super::*;

		/// Test for zero-extension to a non-strict zero-extension width
		/// which results in an error.
		#[test]
		#[ignore]
		fn fail_strict() {
		}

		/// Test to assert behavioural equality to `into_strict_zero_extend`.
		#[test]
		#[ignore]
		fn equal_to_into_strict_zero_extend() {
		}
	}

	mod into_sign_extend {
		use super::*;

		/// Test for sign-extension to the same bit width.
		#[test]
		#[ignore]
		fn equal_width() {
		}

		/// Test for sign-extension to a bit width that is
		/// greater than the current bit width and thus an error.
		#[test]
		#[ignore]
		fn fail_width() {
		}

		/// Test for sign-extension between bit widths that
		/// can be stored entirely on the stack.
		#[test]
		#[ignore]
		fn inl() {
		}

		/// Test for sign-extension where a heap-allocated
		/// `ApInt` is sign-extended to a purely stack-allocated one.
		#[test]
		#[ignore]
		fn ext_to_inl() {
		}

		/// Test for sign-extension where origin and target `ApInt`
		/// are both entirely heap-allocated.
		#[test]
		#[ignore]
		fn ext() {
		}
	}

	mod into_strict_sign_extend {
		use super::*;

		/// Test for sign-extension to a non-strict sign-extension width
		/// which results in an error.
		#[test]
		#[ignore]
		fn fail_strict() {
		}

		/// Test to assert equality for any other case than the
		/// strict sign-extension width case to `into_sign_extend`.
		#[test]
		#[ignore]
		fn equal_to_into_zero_extend() {
		}
	}

	mod sign_extend {
		use super::*;

		/// Test to assert behavioural equality to `into_sign_extend`.
		#[test]
		#[ignore]
		fn equal_to_into_zero_extend() {
		}
	}

	mod strict_sign_extend {
		use super::*;

		/// Test for sign-extension to a non-strict sign-extension width
		/// which results in an error.
		#[test]
		#[ignore]
		fn fail_strict() {
		}

		/// Test to assert behavioural equality to `into_strict_sign_extend`.
		#[test]
		#[ignore]
		fn equal_to_into_strict_sign_extend() {
		}
	}

}