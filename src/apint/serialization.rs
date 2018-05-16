use radix::{Radix};
use apint::{ApInt};
use errors::{Error, Result};
use digit;

use std::fmt;

impl fmt::Binary for ApInt {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		if self.is_zero() {
			return write!(f, "0")
		}
		let mut ds = self.as_digit_slice().into_iter().rev();
		while let Some(digit) = ds.next() {
			if digit.is_zero() {
				continue;
			}
			write!(f, "{:b}", digit)?;
			break
		}
		for digit in ds {
			write!(f, "{:064b}", digit)?
		}
		Ok(())
	}
}

impl fmt::Octal for ApInt {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		if self.is_zero() {
			return write!(f, "0")
		}
		unimplemented!()
		// Ok(())
	}
}

impl fmt::LowerHex for ApInt {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		if self.is_zero() {
			return write!(f, "0")
		}
		let mut ds = self.as_digit_slice().into_iter().rev();
		while let Some(digit) = ds.next() {
			if digit.is_zero() {
				continue;
			}
			write!(f, "{:x}", digit)?;
			break
		}
		for digit in ds {
			write!(f, "{:016x}", digit)?
		}
		Ok(())
	}
}

impl fmt::UpperHex for ApInt {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		if self.is_zero() {
			return write!(f, "0")
		}
		let mut ds = self.as_digit_slice().into_iter().rev();
		while let Some(digit) = ds.next() {
			if digit.is_zero() {
				continue;
			}
			write!(f, "{:X}", digit)?;
			break
		}
		for digit in ds {
			write!(f, "{:016X}", digit)?
		}
		Ok(())
	}
}

/// # Deserialization
impl ApInt {
	/// Parses the given `input` `String` with the given `Radix` and returns an `ApInt`
	/// with the given `target_width` `BitWidth`.
	/// 
	/// **Note:** The given `input` is parsed as big-endian value. This means, the most significant bit (MSB)
	/// is the leftst bit in the string representation provided by the user.
	/// 
	/// The string is assumed to contain no whitespace and contain only values within a subset of the 
	/// range of `0`..`9` and `a`..`z` depending on the given `radix`.
	/// 
	/// The string is assumed to have no sign as `ApInt` does not handle signdness.
	/// 
	/// # Errors
	/// 
	/// - If `input` is empty.
	/// - If `input` is not a valid representation for an `ApInt` for the given `radix`.
	/// - If `input` has trailing zero characters (`0`), e.g. `"0042"` instead of `"42"`.
	/// - If `input` represents an `ApInt` value that does not fit into the given `target_bitwidth`.
	/// 
	/// # Examples
	/// 
	/// ```no_run
	/// # use apint::ApInt;
	/// let a = ApInt::from_str_radix(10, "42");      // ok
	/// let b = ApInt::from_str_radix( 2, "1011011"); // ok (dec. = 91)
	/// let c = ApInt::from_str_radix(16, "ffcc00");  // ok (dec. = 16763904)
	/// let c = ApInt::from_str_radix(10, "256");     // Error: 256 does not fit within 8 bits!
	/// let d = ApInt::from_str_radix( 2, "01020");   // Error: Invalid digit '2' at position 3 for given radix.
	/// let e = ApInt::from_str_radix(16, "hello");   // Error: "hello" is not a valid ApInt representation!
	/// ```
	pub fn from_str_radix<R, S>(radix: R, input: S) -> Result<ApInt>
		where R: Into<Radix>,
		      S: AsRef<str>
	{
		let radix = radix.into();
		let input = input.as_ref();

		if input.is_empty() {
			return Err(Error::invalid_string_repr(input, radix)
				.with_annotation("Cannot parse an empty string into an ApInt."))
		}
		if input.starts_with('_') {
			return Err(Error::invalid_string_repr(input, radix)
				.with_annotation("The input string starts with an underscore ('_') instead of a number. \
					              The use of underscores is explicitely for separation of digits."))
		}
		if input.ends_with('_') {
			return Err(Error::invalid_string_repr(input, radix)
				.with_annotation("The input string ends with an underscore ('_') instead of a number. \
					              The use of underscores is explicitely for separation of digits."))
		}

		// First normalize all characters to plain digit values.
		let mut v = Vec::with_capacity(input.len());
		for (i, b) in input.bytes().enumerate() {
			let d = match b {
				b'0'...b'9' => b - b'0',
				b'a'...b'z' => b - b'a' + 10,
				b'A'...b'Z' => b - b'A' + 10,
				b'_' => continue,
				_ => ::std::u8::MAX
			};
			if !radix.is_valid_byte(d) {
				return Err(Error::invalid_char_in_string_repr(input, radix, i, char::from(b)))
			}
			v.push(d);
		}

		let result = match radix.exact_bits_per_digit() {
			Some(bits) => {
				v.reverse();
				if digit::BITS % bits == 0 {
					ApInt::from_bitwise_digits(&v, bits)
				}
				else {
					ApInt::from_inexact_bitwise_digits(&v, bits)
				}
			}
			None => {
				ApInt::from_radix_digits(&v, radix)
			}
		};


		Ok(result)
	}

	// Convert from a power of two radix (bits == ilog2(radix)) where bits evenly divides
	// Digit::BITS.
	// 
	// Forked from: https://github.com/rust-num/num/blob/master/bigint/src/biguint.rs#L126
	// 
	// TODO: Better document what happens here and why.
	fn from_bitwise_digits(v: &[u8], bits: usize) -> ApInt {
		use digit;
		use digit::{DigitRepr, Digit};

	    debug_assert!(!v.is_empty() && bits <= 8 && digit::BITS % bits == 0);
	    debug_assert!(v.iter().all(|&c| DigitRepr::from(c) < (1 << bits)));

	    let radix_digits_per_digit = digit::BITS / bits;

	    let data = v.chunks(radix_digits_per_digit)
	                .map(|chunk| chunk.iter()
	                	              .rev()
	                	              .fold(0, |acc, &c| (acc << bits) | DigitRepr::from(c)))
	                .map(Digit);

	    ApInt::from_iter(data).unwrap()
	}

	// Convert from a power of two radix (bits == ilog2(radix)) where bits doesn't evenly divide
	// Digit::BITS.
	// 
	// Forked from: https://github.com/rust-num/num/blob/master/bigint/src/biguint.rs#L143
	// 
	// TODO: Better document what happens here and why.
	fn from_inexact_bitwise_digits(v: &[u8], bits: usize) -> ApInt {
		use digit;
		use digit::{DigitRepr, Digit};

	    debug_assert!(!v.is_empty() && bits <= 8 && digit::BITS % bits != 0);
	    debug_assert!(v.iter().all(|&c| (DigitRepr::from(c)) < (1 << bits)));

	    let len_digits = (v.len() * bits + digit::BITS - 1) / digit::BITS;
	    let mut data = Vec::with_capacity(len_digits);

	    let mut d = 0;
	    let mut dbits = 0; // Number of bits we currently have in d.

	    // Walk v accumulating bits in d; whenever we accumulate digit::BITS in d, spit out a digit:
	    for &c in v {
	        d |= (DigitRepr::from(c)) << dbits;
	        dbits += bits;

	        if dbits >= digit::BITS {
	            data.push(Digit(d));
	            dbits -= digit::BITS;
	            // If `dbits` was greater than `digit::BITS`, we dropped some of the bits in c
	            // (they couldn't fit in d) - grab the bits we lost here:
	            d = (DigitRepr::from(c)) >> (bits - dbits);
	        }
	    }

	    if dbits > 0 {
	        debug_assert!(dbits < digit::BITS);
	        data.push(Digit(d));
	    }

	    ApInt::from_iter(data).unwrap()
	}

	// Read little-endian radix digits.
	// 
	// Forked from: https://github.com/rust-num/num/blob/master/bigint/src/biguint.rs#L177
	// 
	// TODO: This does not work, yet. Some parts of the algorithm are
	//       commented-out since the required functionality does not exist, yet.
	fn from_radix_digits(v: &[u8], radix: Radix) -> ApInt {
		use digit;
		use digit::{DigitRepr, Digit};

	    debug_assert!(!v.is_empty() && !radix.is_power_of_two());
	    debug_assert!(v.iter().all(|&c| radix.is_valid_byte(c)));

	    // Estimate how big the result will be, so we can pre-allocate it.
	    let bits = (f64::from(radix.to_u8())).log2() * v.len() as f64;
	    let big_digits = (bits / digit::BITS as f64).ceil();
	    let mut data = Vec::with_capacity(big_digits as usize);

	    let (_base, power) = radix.get_radix_base();
	    let radix = DigitRepr::from(radix.to_u8());

	    let r = v.len() % power;
	    let i = if r == 0 {
	        power
	    } else {
	        r
	    };
	    let (head, tail) = v.split_at(i);

	    let first = head.iter().fold(0, |acc, &d| acc * radix + DigitRepr::from(d));
	    data.push(first);

	    debug_assert!(tail.len() % power == 0);
	    for chunk in tail.chunks(power) {
	        if data.last() != Some(&0) {
	            data.push(0);
	        }

	        let mut carry = 0;
	        for _d in &mut data {
	            // *d = mac_with_carry(0, *d, base, &mut carry); // TODO! This was commented out.

				// // fn carry_mul_add(a: Digit, b: Digit, c: Digit, carry: Digit) -> DigitAndCarry
				// // Returns the result of `(a + (b * c)) + carry` and its implied carry value.

	            // let DigitAndCarry(d, carry) = carry_mul_add(digit::ZERO, *d, base, carry); // TODO! This was commented out.
	        }
	        debug_assert!(carry == 0);

	        let _n = chunk.iter().fold(0, |acc, &d| acc * radix + DigitRepr::from(d));
	        // add2(&mut data, &[n]); // TODO: This was commented out.
	    }

	    ApInt::from_iter(data.into_iter().map(Digit)).unwrap()
	}
}

//  =======================================================================
///  Serialization
/// =======================================================================
impl ApInt {
	/// Returns a `String` representation of the binary encoded `ApInt` for the given `Radix`.
	pub fn as_string_with_radix<R>(&self, radix: R) -> String
		where R: Into<Radix>
	{
		let _radix = radix.into();

		unimplemented!();
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use bitwidth::{BitWidth};

	mod binary {
		use super::*;

		fn assert_binary(val: ApInt, expected: &str) {
			assert_eq!(
				format!("{:b}", val),
				expected
			)
		}

		#[test]
		fn small() {
			assert_binary(
				ApInt::zero(BitWidth::w32()),
				"0"
			);
			assert_binary(
				ApInt::one(BitWidth::w32()),
				"1"
			);
			assert_binary(
				ApInt::from(0b_1010_0110_0110_1001_u32),
				"1010011001101001"
			);
			assert_binary(
				ApInt::all_set(BitWidth::w32()),
				"11111111111111111111111111111111" // 32 ones
			);
			assert_binary(
				ApInt::signed_min_value(BitWidth::w32()),
				"10000000000000000000000000000000" // 31 zeros
			);
			assert_binary(
				ApInt::signed_max_value(BitWidth::w32()),
				"1111111111111111111111111111111"  // 31 ones
			);
		}

		#[test]
		fn large() {
			assert_binary(
				ApInt::zero(BitWidth::w128()),
				"0"
			);
			assert_binary(
				ApInt::one(BitWidth::w128()),
				"1"
			);
			assert_binary(
				ApInt::from(0b_1010_0110_0110_1001_u128),
				"1010011001101001"
			);
			assert_binary(
				ApInt::all_set(BitWidth::w128()),
				"11111111111111111111111111111111\
				 11111111111111111111111111111111\
				 11111111111111111111111111111111\
				 11111111111111111111111111111111"
			);
			assert_binary(
				ApInt::signed_min_value(BitWidth::w128()),
				"10000000000000000000000000000000\
				 00000000000000000000000000000000\
				 00000000000000000000000000000000\
				 00000000000000000000000000000000"
			);
			assert_binary(
				ApInt::signed_max_value(BitWidth::w128()),
				"1111111111111111111111111111111\
				 11111111111111111111111111111111\
				 11111111111111111111111111111111\
				 11111111111111111111111111111111"
			);
		}
	}

	mod hex {
		use super::*;

		fn assert_hex(val: ApInt, expected: &str) {
			assert_eq!(
				format!("{:x}", val),
				expected.to_lowercase()
			);
			assert_eq!(
				format!("{:X}", val),
				expected.to_uppercase()
			)
		}

		#[test]
		fn small() {
			assert_hex(
				ApInt::zero(BitWidth::w32()),
				"0"
			);
			assert_hex(
				ApInt::one(BitWidth::w32()),
				"1"
			);
			assert_hex(
				ApInt::from(0xFEDC_BA98_u32),
				"FEDC\
				 BA98"
			);
			assert_hex(
				ApInt::all_set(BitWidth::w32()),
				"FFFF\
				 FFFF"
			);
			assert_hex(
				ApInt::signed_min_value(BitWidth::w32()),
				"8000\
				 0000"
			);
			assert_hex(
				ApInt::signed_max_value(BitWidth::w32()),
				"7FFF\
				 FFFF"
			);
		}

		#[test]
		fn large() {
			assert_hex(
				ApInt::zero(BitWidth::w128()),
				"0"
			);
			assert_hex(
				ApInt::one(BitWidth::w128()),
				"1"
			);
			assert_hex(
				ApInt::from(0xFEDC_BA98_0A1B_7654_ABCD_0123_u128),
				"FEDC\
				 BA98\
				 0A1B\
				 7654\
				 ABCD\
				 0123"
			);
			assert_hex(
				ApInt::all_set(BitWidth::w128()),
				"FFFFFFFF\
				 FFFFFFFF\
				 FFFFFFFF\
				 FFFFFFFF"
			);
			assert_hex(
				ApInt::signed_min_value(BitWidth::w128()),
				"80000000\
				 00000000\
				 00000000\
				 00000000"
			);
			assert_hex(
				ApInt::signed_max_value(BitWidth::w128()),
				"7FFFFFFF\
				 FFFFFFFF\
				 FFFFFFFF\
				 FFFFFFFF"
			);
		}
	}

	mod from_str_radix {

		use super::*;

		fn test_radices() -> impl Iterator<Item=Radix> {
			[2, 4, 8, 16, 32, 7, 10, 36].into_iter().map(|&r| Radix::new(r).unwrap())
		}

		#[test]
		fn empty() {
			for radix in test_radices() {
				assert_eq!(
					ApInt::from_str_radix(radix, ""),
					Err(Error::invalid_string_repr("", radix)
						.with_annotation("Cannot parse an empty string into an ApInt."))
				)
			}
		}

		#[test]
		fn starts_with_underscore() {
			for radix in test_radices() {
				for &input in &["_0", "_123", "__", "_1_0"] {
					assert_eq!(
						ApInt::from_str_radix(radix, input),
						Err(Error::invalid_string_repr(input, radix)
						    .with_annotation("The input string starts with an underscore ('_') instead of a number. \
						                      The use of underscores is explicitely for separation of digits."))
					)
				}
			}
		}

		#[test]
		fn ends_with_underscore() {
			for radix in test_radices() {
				for &input in &["0_", "123_", "1_0_"] {
					assert_eq!(
						ApInt::from_str_radix(radix, input),
						Err(Error::invalid_string_repr(input, radix)
						    .with_annotation("The input string ends with an underscore ('_') instead of a number. \
						                      The use of underscores is explicitely for separation of digits."))
					)
				}
			}
		}

		#[test]
		fn zero() {
			for radix in test_radices() {
				assert_eq!(
					ApInt::from_str_radix(radix, "0"),
					Ok(ApInt::zero(BitWidth::new(64).unwrap()))
				)
			}
		}

		#[test]
		fn small_values() {
			use std::u64;
			let samples = vec![
				// (Radix, Input String, Expected ApInt)

				( 2,  "0",  0),
				( 8,  "0",  0),
				(10,  "0",  0),
				(16,  "0",  0),

				( 2,  "1",  1),
				( 8,  "1",  1),
				(10,  "1",  1),
				(16,  "1",  1),

				( 2, "10",  2),
				( 8, "10",  8),
				(10, "10", 10),
				(16, "10", 16),

				( 2, "11",  3),
				( 8, "11",  9),
				(10, "11", 11),
				(16, "11", 17),

				( 2, "1001_0011", 0b1001_0011),
				( 2, "0001_0001_0001_0001", 0x1111),
				( 2, "0101_0101_0101_0101", 0x5555),
				( 2, "1010_1010_1010_1010", 0xAAAA),
				( 2, "1111_1111_1111_1111", 0xFFFF),
				( 2, "1111_1111_1111_1111\
					  1111_1111_1111_1111\
					  1111_1111_1111_1111\
					  1111_1111_1111_1111", u64::max_value()),

				( 8, "7654_3210", 0o7654_3210),
				( 8, "0123_4567", 0o0123_4567),
				( 8, "777_747_666", 0o777_747_666),
				( 8, "111", 0b001_001_001),
				( 8,  "7_7777_7777_7777_7777_7777", u64::max_value() / 2),
				// ( 8, "17_7777_7777_7777_7777_7777", u64::max_value()), // Does not work, yet! Should it work?

				(10, "100", 100),
				(10, "42", 42),
				(10, "1337", 1337),
				(10, "5_000_000", 5_000_000),
				// (10, "18_446_744_073_709_551_615", u64::max_value()), // Does not work, yet!

				(16, "100", 0x100),
				(16, "42", 0x42),
				(16, "1337", 0x1337),
				(16, "1111", 0x1111),
				(16, "5555", 0x5555),
				(16, "FFFF", 0xFFFF),
				(16, "0123_4567_89AB_CDEF", 0x0123_4567_89AB_CDEF),
				(16, "FEDC_BA98_7654_3210", 0xFEDC_BA98_7654_3210)
			];
			for sample in &samples {
				let radix = Radix::new(sample.0).unwrap();
				let input = sample.1;
				let result = ApInt::from_str_radix(radix, input).unwrap();
				let expected = ApInt::from_u64(sample.2);
				assert_eq!(result, expected)
			}
		}
	}
}
