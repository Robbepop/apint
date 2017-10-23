
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BitPos(usize);

impl BitPos {
	#[inline]
	pub fn to_usize(self) -> usize {
		self.0
	}
}

impl From<usize> for BitPos {
	#[inline]
	fn from(val: usize) -> BitPos {
		BitPos(val)
	}
}
