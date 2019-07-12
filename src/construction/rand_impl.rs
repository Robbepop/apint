use crate::data::{ApInt, Digit};
use crate::info::{BitWidth};

use rand;
use rand::{Rng, SeedableRng};
use rand::distributions::{Distribution, Standard};
use rand::rngs::SmallRng;

impl Distribution<Digit> for Standard {
    /// Creates a random `Digit` using the given random number generator.
	fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Digit {
		Digit(rng.next_u64())
	}
}

/// # Random Utilities using `rand` crate.
impl ApInt {
	/// Creates a new `ApInt` with the given `BitWidth` and random `Digit`s.
	pub fn random_with_width(width: BitWidth) -> ApInt {
		ApInt::random_with_width_using(width, &mut SmallRng::from_entropy())
	}

    /// Creates a new `ApInt` with the given `BitWidth` and random `Digit`s using the given random
    /// number generator. This is useful for cryptographic or testing purposes.
    pub fn random_with_width_using<R: Rng>(width: BitWidth, rng: &mut R) -> ApInt {
        let required_digits = width.required_digits();
        assert!(required_digits >= 1);
        let random_digits = rng.sample_iter::<Digit, Standard>(Standard).take(required_digits);
        ApInt::from_iter(random_digits)
            .expect("We asserted that `required_digits` is at least `1` or greater
                     so it is safe to assume that `ApInt::from_iter` won't fail.")
            .into_truncate(width) // This truncation will be cheap always!
            .expect("`BitWidth::required_digits` returns an upper bound for the
                     number of required digits, so it is safe to truncate.")
    }

    /// Randomizes the digits of this `ApInt` inplace.
    pub fn randomize(&mut self) {
        self.randomize_using(&mut SmallRng::from_entropy())
    }

    /// Randomizes the digits of this `ApInt` inplace using the given random number generator.
    pub fn randomize_using<R: Rng>(&mut self, rng: &mut R) {
        self.digits_mut()
            .zip(rng.sample_iter::<Digit, Standard>(Standard))
            .for_each(|(d, r)| *d = r);
        self.clear_unused_bits();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand_xoshiro::Xoshiro256StarStar;

    #[test]
    fn random_with_width_using() {
        let r = &mut Xoshiro256StarStar::seed_from_u64(0);
        assert_eq!(ApInt::random_with_width_using(BitWidth::w1(), r), ApInt::from_bool(false));
        assert_eq!(ApInt::random_with_width_using(BitWidth::w8(), r), ApInt::from_u8(42));
        assert_eq!(ApInt::random_with_width_using(BitWidth::w16(), r), ApInt::from_u16(59104));
        assert_eq!(ApInt::random_with_width_using(BitWidth::w32(), r), ApInt::from_u32(640494892));
        assert_eq!(ApInt::random_with_width_using(BitWidth::w64(), r), ApInt::from_u64(13521403990117723737));
        assert_eq!(ApInt::random_with_width_using(BitWidth::w128(), r), ApInt::from([7788427924976520344u64, 18442103541295991498]));
    }

    #[test]
    fn randomize_using() {
        let r0 = &mut Xoshiro256StarStar::seed_from_u64(0);
        let r1 = &mut Xoshiro256StarStar::seed_from_u64(0);
        {
            let mut randomized = ApInt::from_bool(false);
            randomized.randomize_using(r0);
            let new_random = ApInt::random_with_width_using(BitWidth::w1(), r1);
            assert_eq!(randomized, new_random);
        }{
            let mut randomized = ApInt::from_u8(0);
            randomized.randomize_using(r0);
            let new_random = ApInt::random_with_width_using(BitWidth::w8(), r1);
            assert_eq!(randomized, new_random);
        }{
            let mut randomized = ApInt::from_u16(0);
            randomized.randomize_using(r0);
            let new_random = ApInt::random_with_width_using(BitWidth::w16(), r1);
            assert_eq!(randomized, new_random);
        }{
            let mut randomized = ApInt::from_u32(0);
            randomized.randomize_using(r0);
            let new_random = ApInt::random_with_width_using(BitWidth::w32(), r1);
            assert_eq!(randomized, new_random);
        }{
            let mut randomized = ApInt::from_u64(0);
            randomized.randomize_using(r0);
            let new_random = ApInt::random_with_width_using(BitWidth::w64(), r1);
            assert_eq!(randomized, new_random);
        }{
            let mut randomized = ApInt::from_u128(0);
            randomized.randomize_using(r0);
            let new_random = ApInt::random_with_width_using(BitWidth::w128(), r1);
            assert_eq!(randomized, new_random);
        }
    }
}
