use digit::Digit;

use std::slice;

/// A sequence of digits.
#[derive(Debug, Clone)]
pub(crate) struct DigitSeq<'a> {
	digits: slice::Iter<'a, Digit>
}

impl<'a> Iterator for DigitSeq<'a> {
	type Item = Digit;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		self.digits.next().map(|d| *d)
	}
}

/// A sequence of mutable digits.
#[derive(Debug)]
pub(crate) struct DigitSeqMut<'a> {
	digits: slice::IterMut<'a, Digit>
}

impl<'a> Iterator for DigitSeqMut<'a> {
	type Item = &'a mut Digit;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		self.digits.next()
	}
}

/// A type that acts as a sequence of digits.
/// 
/// This is used as abstraction over the different low-level representations
/// of an `APInt`.
pub(crate) trait AsDigitSeq {
	/// Returns a sequence of digits.
	fn digits(&self) -> DigitSeq;
}

/// A type that acts as a sequence of mutable digits.
/// 
/// This is used as abstraction over the different low-level representations
/// of an `APInt`.
pub(crate) trait AsDigitSeqMut {
	/// Returns a sequence of mutable digits.
	fn digits_mut(&mut self) -> DigitSeqMut;
}
