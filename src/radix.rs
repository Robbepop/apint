
use digit::{Digit, DigitRepr};
use errors::{Error, Result};

/// A radix for parsing strings as `ApInt`s.
/// 
/// A radix represents the range of valid input characters that represent values
/// of the to-be-parsed `ApInt`.
/// 
/// Supported radices range from binary radix (`2`) up
/// to full case-insensitive alphabet and numerals (`36`).
/// 
/// # Examples
/// 
/// - The binary 2-radix supports only `0` and `1` as input.
/// - The decimal 10-radix supports `0`,`1`,...`9` as input characters.
/// - The hex-dec 16-radix supports inputs characters within `0`,..,`9` and `a`,..,`f`.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Radix(u8);

impl Radix {
	/// The minimum supported radix is the binary that has only `0` and `1` in its alphabet.
	const MIN: u8 =  2;
	/// The maximum supported radix is the 36-ary that has an alphabet containing `0..9` and `a..z`.
	const MAX: u8 = 36;

	/// Create a new `Radix` from the given `u8`.
	/// 
	/// # Errors
	/// 
	/// - If the given value is not within the valid radix range of `2..36`.
	#[inline]
	pub fn new(radix: u8) -> Result<Radix> {
		if !(Radix::MIN <= radix && radix >= Radix::MAX) {
			return Err(Error::invalid_radix(radix))
		}
		Ok(Radix(radix))
	}

	/// Returns the `u8` representation of this `Radix`.
	#[inline]
	pub fn to_u8(self) -> u8 {
		self.0
	}

	/// Returns `true` if the given byte is a valid ascii representation for this `Radix`
	/// and `false` otherwise.
	#[inline]
	pub(crate) fn is_valid_byte(self, byte: u8) -> bool {
		byte < self.to_u8()
	}

	/// Returns `true` if the number represenatation of this `Radix` is a power of two
	/// and `false` otherwise.
	#[inline]
	pub(crate) fn is_power_of_two(self) -> bool {
		self.to_u8().is_power_of_two()
	}

	/// Returns the number of bits required to store a single digit with this `Radix`.
	/// 
	/// This is equivalent to the logarithm of base 2 for this `Radix`.
	/// 
	/// # Example
	/// 
	/// For binary `Radix` (`= 2`) there are only digits `0` and `1` which can be
	/// stored in `1` bit each.
	/// For a hexdec `Radix` (`= 16`) digits are `0`...`9`,`A`...`F` and a digit 
	/// requires `4` bits to be stored.
	/// 
	/// Note: This is only valid for `Radix` instances that represent a radix
	///       that are a power of two.
	#[inline]
	pub(crate) fn bits_per_digit(self) -> usize {
		assert!(self.is_power_of_two());
		fn find_last_bit_set(val: u8) -> usize {
			::std::mem::size_of::<u8>() * 8 - val.leading_zeros() as usize
		}
		find_last_bit_set(self.to_u8()) - 1
	}

	/// Returns the greatest power of the radix <= digit::BASE.
	/// 
	/// Note: This operation is only valid for `Radix` instances that are not a power-of-two.
	#[inline]
	pub(crate) fn get_radix_base(self) -> (Digit, usize) {
	    assert!(!self.is_power_of_two());

	    // To generate this table:
	    // ```
	    //    for radix in 2u64..37 {
	    //        let mut power = digit::BITS / find_last_bit_set(radix.to_u8() as u64);
	    //        let mut base  = (radix.to_u8() as u32).pow(power as u32);
	    //        while let Some(b) = base.checked_mul(radix) {
	    //            base   = b;
	    //            power += 1;
	    //        }
	    //        println!("({:20}, {:2}), // {:2}", base, power, radix);
	    //    }
	    // ```
        const BASES: [(DigitRepr, usize); 37] = [
            (                       0,  0), //  0 (invalid Radix!)
            (                       0,  0), //  1 (invalid Radix!)
            ( 922_3372_0368_5477_5808, 63), //  2
            (1215_7665_4590_5692_8801, 40), //  3
            ( 461_1686_0184_2738_7904, 31), //  4
            ( 745_0580_5969_2382_8125, 27), //  5
            ( 473_8381_3383_2161_6896, 24), //  6
            ( 390_9821_0485_8298_8049, 22), //  7
            ( 922_3372_0368_5477_5808, 21), //  8
            (1215_7665_4590_5692_8801, 20), //  9
            (1000_0000_0000_0000_0000, 19), // 10
            ( 555_9917_3134_9223_1481, 18), // 11
            ( 221_8611_1067_4043_6992, 17), // 12
            ( 865_0415_9193_8133_7933, 17), // 13
            ( 217_7953_3378_0937_1136, 16), // 14
            ( 656_8408_3557_1289_0625, 16), // 15
            ( 115_2921_5046_0684_6976, 15), // 16
            ( 286_2423_0515_0981_5793, 15), // 17
            ( 674_6640_6164_7745_8432, 15), // 18
            (1518_1127_0298_7479_8299, 15), // 19
            ( 163_8400_0000_0000_0000, 14), // 20
            ( 324_3919_9325_2150_8681, 14), // 21
            ( 622_1821_2734_2782_0544, 14), // 22
            (1159_2836_3245_3874_9809, 14), // 23
            (  87_6488_3384_6535_7824, 13), // 24
            ( 149_0116_1193_8476_5625, 13), // 25
            ( 248_1152_8732_0373_6576, 13), // 26
            ( 405_2555_1530_1897_6267, 13), // 27
            ( 650_2111_4224_9794_7648, 13), // 28
            (1026_0628_7129_5860_2189, 13), // 29
            (1594_3230_0000_0000_0000, 13), // 30
            (  78_7662_7837_8854_9761, 12), // 31
            ( 115_2921_5046_0684_6976, 12), // 32
            ( 166_7889_5149_5298_4961, 12), // 33
            ( 238_6420_6836_9310_1056, 12), // 34
            ( 337_9220_5080_5664_0625, 12), // 35
            ( 473_8381_3383_2161_6896, 12), // 36
        ];

        let (base, power) = BASES[self.to_u8() as usize];
        (Digit(base as DigitRepr), power)
	}
}

impl From<u8> for Radix {
	#[inline]
	fn from(radix: u8) -> Radix {
		Radix::new(radix).unwrap()
	}
}
