
use apint::{APInt, APIntData};
use errors::{Error, Result};

use bitwidth::{BitWidth};
use storage::{Storage};
use digit::{Bit, Digit};

impl Clone for APInt {
	fn clone(&self) -> Self {
		match self.len.storage() {
			Storage::Inl => {
				APInt{len: self.len, data: APIntData{inl: unsafe{self.data.inl}}}
			}
			Storage::Ext => {
				let req_blocks = self.len_blocks();
				let mut buffer = Vec::with_capacity(req_blocks);
				buffer.extend_from_slice(self.as_digit_slice());
				debug_assert_eq!(buffer.capacity(), req_blocks);
				let dst = buffer.as_mut_ptr();
				::std::mem::forget(buffer);
				APInt{len: self.len, data: APIntData{ext: dst}}
			}
		}
	}
}

//  =======================================================================
///  Casting: Truncation & Extension
/// =======================================================================
impl APInt {
	/// Creates a new `APInt` that represents this `APInt` truncated to 
	/// the given target bit-width.
	///
	/// # Panics
	/// 
	/// - If `target_bitwidth` is greater than the `APInt`'s current bit-width.
	/// - If `target_bitwidth` is zero (`0`).
	/// 
	/// # Note
	/// 
	/// Equal to a call to `clone()` if `target_bitwidth` is equal to this `APInt`'s bit-width.
	pub fn truncate<W>(&self, target_bitwidth: W) -> Result<APInt>
		where W: Into<BitWidth>
	{
		let target_bitwidth = target_bitwidth.into();
		let len_bitwidth    = target_bitwidth.to_usize();

		if len_bitwidth > self.len_bits() {
			return Error::truncation_bitwidth_too_large(len_bitwidth, self.len_bits())
				.with_annotation(format!(
					"Cannot truncate bit-width of {:?} to {:?} bits. \
					 Do you mean to extend the instance instead?",
					self.len_bits(), target_bitwidth))
				.into()
		}
		if len_bitwidth == self.len_bits() {
			warn!("APInt::truncate: Truncating to the same bit-width is equal to cloning. \
				   Do you mean to clone the object instead?");
			return Ok(self.clone())
		}

		match (target_bitwidth.storage(), self.len.storage()) {
			(Storage::Inl, Storage::Inl) => Ok(APInt{
				len : target_bitwidth,
				data: APIntData{
					inl: unsafe{self.data.inl.truncated(target_bitwidth).unwrap()}
				}
			}),
			(Storage::Inl, Storage::Ext) => Ok(APInt{
				len : target_bitwidth,
				data: APIntData{
					inl: unsafe{(*self.data.ext).truncated(target_bitwidth).unwrap()}
				}
			}),
			(Storage::Ext, Storage::Ext) => {
				let     req_blocks         = target_bitwidth.required_blocks();
				let mut buffer: Vec<Digit> = Vec::with_capacity(req_blocks);
				buffer.extend_from_slice(&self.as_digit_slice()[0..req_blocks]);
				debug_assert_eq!(buffer.capacity(), req_blocks);
				if let Some(excess_bits) = target_bitwidth.excess_bits() {
					buffer.last_mut().unwrap().truncate(excess_bits).unwrap();
				}
				let dst = buffer.as_mut_ptr();
				::std::mem::forget(buffer);
				Ok(APInt{len: self.len, data: APIntData{ext: dst}})
			}
			_ => unreachable!()
		}
	}

	/// Creates a new `APInt` that represents the zero-extension of this `APInt` to the given target bit-width.
	///
	/// # Semantics (from LLVM)
	/// 
	/// The zext fills the high order bits of the value with zero bits until it reaches the size of the destination bit-width.
	/// When zero extending from `i1`, the result will always be either `0` or `1`.
	/// 
	/// # Panics
	/// 
	/// - If `target_bitwidth` is less than the `APInt`'s current bit-width.
	/// 
	/// # Note
	/// 
	/// Equal to a call to `clone()` if `target_bitwidth` is equal to this `APInt`'s bit-width.
	pub fn zero_extend<W>(&self, target_bitwidth: W) -> Result<APInt>
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
			(Storage::Inl, Storage::Inl) => Ok(APInt{
				len : target_bitwidth,
				data: APIntData{
					inl: unsafe{self.data.inl.truncated(target_bitwidth).unwrap()}
				}
			}),
			(Storage::Inl, Storage::Ext) => Ok(APInt{
				len : target_bitwidth,
				data: APIntData{
					inl: unsafe{(*self.data.ext).truncated(target_bitwidth).unwrap()}
				}
			}),
			(Storage::Ext, Storage::Ext) => {
				let req_blocks     = target_bitwidth.required_blocks();
				let present_blocks = self.len_blocks();
				assert!(present_blocks <= req_blocks);
				let mut buffer: Vec<Digit> = Vec::with_capacity(req_blocks);
				buffer.extend_from_slice(&self.as_digit_slice()[0..present_blocks]);
				let rest = req_blocks - present_blocks;
				buffer.resize(rest, Digit::zeros());
				debug_assert_eq!(buffer.capacity(), req_blocks);
				debug_assert_eq!(buffer.len()     , req_blocks);
				let dst = buffer.as_mut_ptr();
				::std::mem::forget(buffer);
				Ok(APInt{len: self.len, data: APIntData{ext: dst}})
			}
			_ => unreachable!()
		}
	}

	/// Creates a new `APInt` that represents the sign-extension of this `APInt` to the given target bit-width.
	/// 
	/// 
	/// # Semantic (from LLVM)
	/// 
	/// The ‘sext‘ instruction performs a sign extension by copying the sign bit (highest order bit) of the value until it reaches the target bit-width.
	/// When sign extending from `i1`, the extension always results in `-1` or `0`.
	///
	/// # Panics
	/// 
	/// - If `target_bitwidth` is less than the `APInt`'s current bit-width.
	/// 
	/// # Note
	/// 
	/// Equal to a call to `clone()` if `target_bitwidth` is equal to this `APInt`'s bit-width.
	pub fn sign_extend<W>(&self, target_bitwidth: W) -> Result<APInt>
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
	pub fn zero_resize<W>(&self, target_bitwidth: W) -> APInt
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
	pub fn sign_resize<W>(&self, target_bitwidth: W) -> APInt
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
