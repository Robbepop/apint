use digit;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BitWidth(pub usize);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Storage { Inl, Ext }

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Model { C8, C16, C32, C64, Inl, Ext }

impl BitWidth {
	pub(crate) fn excess_bits(self) -> Option<usize> {
		match self.to_usize() % digit::BITS {
			0 => None,
			n => Some(n)
		}
	}

	pub(crate) fn storage(self) -> Storage {
		if self.to_usize() < digit::BITS { Storage::Inl } else { Storage::Ext }
	}

	pub(crate) fn model(self) -> Model {
		use self::Model::*;
		match self.to_usize() {
			8  => C8,
			16 => C16,
			32 => C32,
			64 => C64,
			n if n < digit::BITS => Inl,
			_                      => Ext
		}
	}

	pub fn to_usize(self) -> usize {
		self.0
	}

	pub fn from_usize(val: usize) -> Self {
		if val == 0 { panic!("BitWidth::from_usize(0) cannot be instantiated with zero (0).")}
		BitWidth(val)
	}

	#[inline]
	pub fn required_blocks(&self) -> usize {
		((self.to_usize() - 1) / digit::BITS) + 1
	}

}

impl From<usize> for BitWidth {
	fn from(val: usize) -> BitWidth {
		if val == 0 {
			panic!("BitWidth::from(..) cannot be instantiated with zero (0).")
		}
		BitWidth::from_usize(val)
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct BitWidthIter {
	total: usize,
	cur  : usize
}

impl BitWidthIter {
	pub fn new(total: usize) -> BitWidthIter {
		BitWidthIter{total, cur: 0}
	}
}

impl Iterator for BitWidthIter {
	type Item = BitWidth;

	fn next(&mut self) -> Option<Self::Item> {
		if self.cur >= self.total { return None; }
		use std::cmp;
		let cur = cmp::max(self.total - self.cur, digit::BITS);
		self.cur += digit::BITS;
		Some(cur.into())
	}
}
