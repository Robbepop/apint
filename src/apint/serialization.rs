use radix::{Radix};
use bitwidth::{BitWidth};
use apint::{ApInt};
use errors::{Error, Result};

//  =======================================================================
///  Deserialization
/// =======================================================================
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
	/// let a = ApInt::from_str_radix( 64, 10, "42");      // ok
	/// let b = ApInt::from_str_radix( 32,  2, "1011011"); // ok (dec. = 91)
	/// let c = ApInt::from_str_radix(128, 16, "ffcc00");  // ok (dec. = 16763904)
	/// let c = ApInt::from_str_radix(  8, 10, "257");     // Error: 257 does not fit within 8 bits!
	/// let d = ApInt::from_str_radix(100, 16, "hello");   // Error: "hello" is not a valid ApInt representation!
	/// ```
	pub fn from_str_radix<W, R, S>(target_width: W, radix: R, input: S) -> Result<ApInt>
		where W: Into<BitWidth>,
		      R: Into<Radix>,
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
		if input.len() >= 2 && input.starts_with('0') {
			return Err(Error::invalid_string_repr(input, radix)
				.with_annotation("The input string starts with zero digits and is not zero."))
		}

		/// A `target_width` that is greater than or equal to the `BitWidth` returned by this function
		/// can store any number representation of the given input length and radix.
		fn safe_bit_width(radix: Radix, n: usize) -> BitWidth {
			(n * ((f64::from(radix.to_u8())).log2().ceil() as usize)).into()
		}

		/// A `target_width` that is less than the `BitWidth` returned by this function
		/// can **never** store any number representation of the given input length and radix.
		fn unsafe_bit_width(radix: Radix, n: usize) -> BitWidth {
			safe_bit_width(radix, n - 1)
		}

		let target_width = target_width.into();
		let safe_width = safe_bit_width(radix, input.len());
		let unsafe_width = unsafe_bit_width(radix, input.len());
		if target_width < unsafe_width {
			return Err(Error::invalid_string_repr(input, radix)
				.with_annotation("The target bit-width does not suffice to represent the given input string as `ApInt`."))
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

		let result =
			if radix.is_power_of_two() {
				use digit;
				v.reverse();
				let bits = radix.bits_per_digit();
				if digit::BITS % bits == 0 {
					ApInt::from_bitwise_digits(&v, bits)
				}
				else {
					ApInt::from_inexact_bitwise_digits(&v, bits)
				}
			}
			else {
				ApInt::from_radix_digits(&v, radix)
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
	    debug_assert!(v.iter().all(|&c| (DigitRepr::from(c)) < (1 << bits)));

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

	    let (base, power) = radix.get_radix_base();
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
	        for d in &mut data {
	            // *d = mac_with_carry(0, *d, base, &mut carry); // TODO! This was commented out.

				// // fn carry_mul_add(a: Digit, b: Digit, c: Digit, carry: Digit) -> DigitAndCarry
				// // Returns the result of `(a + (b * c)) + carry` and its implied carry value.

	            // let DigitAndCarry(d, carry) = carry_mul_add(digit::ZERO, *d, base, carry); // TODO! This was commented out.
	        }
	        debug_assert!(carry == 0);

	        let n = chunk.iter().fold(0, |acc, &d| acc * radix + DigitRepr::from(d));
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
		let radix = radix.into();

		unimplemented!();
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	mod from_str_radix {

		use super::*;

		fn test_radices() -> impl Iterator<Item=Radix> {
			[2, 4, 8, 16, 32, 7, 10, 36].into_iter().map(|&r| Radix::new(r).unwrap())
		}

		#[test]
		fn empty() {
			for radix in test_radices() {
				assert_eq!(
					ApInt::from_str_radix(64, radix, ""),
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
						ApInt::from_str_radix(64, radix, input),
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
						ApInt::from_str_radix(64, radix, input),
						Err(Error::invalid_string_repr(input, radix)
						    .with_annotation("The input string ends with an underscore ('_') instead of a number. \
						                      The use of underscores is explicitely for separation of digits."))
					)
				}
			}
		}

		#[test]
		fn leading_zeros() {
			for radix in test_radices() {
				for &input in &["00", "0001", "0_1"] {
					assert_eq!(
						ApInt::from_str_radix(64, radix, input),
						Err(Error::invalid_string_repr(input, radix)
							.with_annotation("The input string starts with zero digits and is not zero."))
					)
				}
			}
		}

		#[test]
		fn zero() {
			for radix in test_radices() {
				assert_eq!(
					ApInt::from_str_radix(64, radix, "0"),
					Ok(ApInt::zero(BitWidth::new(64).unwrap()))
				)
			}
		}
	}
}
