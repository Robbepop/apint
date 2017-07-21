use bitwidth::BitWidth;

pub(crate) const BITS: usize = 64;

const U64_ZEROS: u64 = 0x0000_0000_0000_0000_u64;
const U64_ONES : u64 = 0xFFFF_FFFF_FFFF_FFFF_u64;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Bit { Set, Unset }

impl From<bool> for Bit {
	fn from(flag: bool) -> Bit {
		if flag { Bit::Set } else { Bit::Unset }
	}
}

impl From<Bit> for bool {
	fn from(bit: Bit) -> bool {
		match bit {
			Bit::Set   => true,
			Bit::Unset => false
		}
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Digit(pub u64);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct DoubleDigit(pub u128);

impl From<u64> for Digit {
	fn from(val: u64) -> Digit {
		Digit::from_u64(val)
	}
}

//  =======================================================================
///  Constructors
/// =======================================================================
impl Digit {
	/// Creates a digit from a `u64` representation.
	#[inline]
	pub fn from_u64(val: u64) -> Digit {
		Digit(val)
	}

	/// Creates a digit where all bits are initialized to `0`.
	#[inline]
	pub fn zeros() -> Digit {
		Digit::from_u64(U64_ZEROS)
	}

	/// Creates a digit where all bits are initialized to `1`.
	#[inline]
	pub fn ones() -> Digit {
		Digit::from_u64(U64_ONES)
	}
}

//  =======================================================================
///  Utility & helper methods.
/// =======================================================================
impl Digit {
	/// Returns the internal representation as `u64` value.
	#[inline]
	pub fn to_u64(self) -> u64 { 
		self.0
	}
}

//  =======================================================================
///  Deprecated. To be removed.
/// =======================================================================
impl Digit {
	#[inline]
	pub fn truncated<W>(mut self, bitwidth: W) -> Digit
		where W: Into<BitWidth>
	{
		let bitwidth = bitwidth.into();
		self.truncate(bitwidth);
		self
	}

	#[inline]
	pub fn truncate<W>(&mut self, bitwidth: W)
		where W: Into<BitWidth>
	{
		let bitwidth = bitwidth.into();
		if bitwidth.to_usize() > self::BITS {
			panic!("Digit::truncate(..) cannot truncate to a bitwidth larger than the maximum digit size of {:?}", self::BITS)
		}
		self.0 &= U64_ONES >> ((self::BITS as u64) - (bitwidth.to_usize() as u64))
	}
}

//  =======================================================================
///  Bitwise access
/// =======================================================================
impl Digit {
	/// Returns `true` if the `n`th bit is set to `1`, else returns `false`.
	/// 
	/// # Panics
	/// 
	/// If the given `n` is greater than the digit size.
	#[inline]
	pub fn get(&self, n: usize) -> bool {
		if n >= self::BITS {
			panic!("Digit::get({:?}) is out of bounds of a digit. There are only 64 bits in a single digit.", n)
		}
		((self.to_u64() >> n) & 0x01) == 1
	}

	/// Sets the `n`th bit in the digit to `1`.
	/// 
	/// # Panics
	/// 
	/// If the given `n` is greater than the digit size.
	#[inline]
	pub fn set(&mut self, n: usize) {
		if n >= self::BITS {
			panic!("Digit::set({:?}) is out of bounds of a digit. There are only 64 bits in a single digit.", n)
		}
		self.0 |= 0x01 << n
	}

	/// Sets the `n`th bit in the digit to `0`.
	/// 
	/// # Panics
	/// 
	/// If the given `n` is greater than the digit size.
	#[inline]
	pub fn unset(&mut self, n: usize) {
		if n >= self::BITS {
			panic!("Digit::unset({:?}) is out of bounds of a digit. There are only 64 bits in a single digit.", n)
		}
		self.0 &= !(0x01 << n)
	}

	/// Flips `n`th bit.
	/// 
	/// # Panics
	/// 
	/// If the given `n` is greater than the digit size.
	#[inline]
	pub fn flip(&mut self, n: usize) {
		if n >= self::BITS {
			panic!("Digit::flip({:?}) is out of bounds of a digit. There are only 64 bits in a single digit.", n)
		}
		self.0 ^= 0x01 << n
	}

	/// Sets all bits in this digit to `1`.
	/// 
	/// # Panics
	/// 
	/// If the given `n` is greater than the digit size.
	#[inline]
	pub fn set_all(&mut self) {
		self.0 |= U64_ONES
	}

	/// Sets all bits in this digit to `0`.
	/// 
	/// # Panics
	/// 
	/// If the given `n` is greater than the digit size.
	#[inline]
	pub fn unset_all(&mut self) {
		self.0 &= U64_ZEROS
	}

	/// Flips all bits in this digit.
	/// 
	/// # Panics
	/// 
	/// If the given `n` is greater than the digit size.
	#[inline]
	pub fn flip_all(&mut self) {
		self.0 ^= U64_ONES
	}

	/// Sets the first `n` bits in the digit to `1`.
	/// 
	/// # Panics
	/// 
	/// If the given `n` is greater than the digit size.
	pub fn set_first_n(&mut self, n: usize) {
		if n >= self::BITS {
			panic!("Digit::unset_first_n({:?}) is out of bounds of a digit. There are only 64 bits in a single digit.", n)
		}
		self.0 |= !(U64_ONES >> n)
	}

	/// Sets the first `n` bits in the digit to `0`.
	/// 
	/// # Panics
	/// 
	/// If the given `n` is greater than the digit size.
	pub fn unset_first_n(&mut self, n: usize) {
		if n >= self::BITS {
			panic!("Digit::unset_first_n({:?}) is out of bounds of a digit. There are only 64 bits in a single digit.", n)
		}
		self.0 &= U64_ONES >> (self::BITS - n)
	}

}

//  =======================================================================
///  Bitwise operations
/// =======================================================================
impl Digit {
	pub fn bitnot(self) -> Digit {
		Digit(!self.to_u64())
	}

	pub fn bitand(self, other: Digit) -> Digit {
		Digit(self.to_u64() & other.to_u64())
	}

	pub fn bitor(self, other: Digit) -> Digit {
		Digit(self.to_u64() | other.to_u64())
	}

	pub fn bitxor(self, other: Digit) -> Digit {
		Digit(self.to_u64() ^ other.to_u64())
	}
}

//  =======================================================================
///  Bitwise assign operations
/// =======================================================================
impl Digit {
	pub fn bitnot_assign(&mut self) {
		self.0 = !self.to_u64()
	}

	pub fn bitand_assign(&mut self, other: Digit) {
		self.0 &= other.to_u64()
	}

	pub fn bitor_assign(&mut self, other: Digit) {
		self.0 |= other.to_u64()
	}

	pub fn bitxor_assign(&mut self, other: Digit) {
		self.0 ^= other.to_u64()
	}
}

//  =======================================================================
///  Relational operations.
/// =======================================================================
impl Digit {
	#[inline]
	pub fn ult(self, other: Digit) -> bool {
		self.to_u64() < other.to_u64()
	}

	/// Maybe we should re-introduce a LenDigit that know's its internal bit-width so
	/// that it can apply its signed-operations accordingly.
	pub fn slt(self, other: Digit, width: usize) -> bool {
		if width >= self::BITS {
			panic!("nary_int::Digit::slt(..) encountered invalid bit-width of {:?}", width)
		}
		((self.to_u64() << (self::BITS - width)) as i64) < ((other.to_u64() << (self::BITS - width)) as i64)
	}
}
