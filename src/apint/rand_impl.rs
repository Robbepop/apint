use crate::{
    ApInt,
    BitWidth,
    Digit,
};
use rand::SeedableRng as _;

impl rand::distributions::Distribution<Digit> for rand::distributions::Standard {
    /// Creates a random `Digit` using the given random number generator.
    fn sample<R>(&self, rng: &mut R) -> Digit
    where
        R: rand::Rng + ?Sized,
    {
        Digit(rng.next_u64())
    }
}

/// # Random Utilities using `rand` crate.
impl ApInt {
    /// Creates a new `ApInt` with the given `BitWidth` and random `Digit`s.
    pub fn random_with_width(width: BitWidth) -> ApInt {
        ApInt::random_with_width_using(width, &mut rand::rngs::SmallRng::from_entropy())
    }

    /// Creates a new `ApInt` with the given `BitWidth` and random `Digit`s
    /// using the given random number generator.
    ///
    /// **Note:** This is useful for cryptographic or testing purposes.
    pub fn random_with_width_using<R>(width: BitWidth, rng: &mut R) -> ApInt
    where
        R: rand::Rng,
    {
        let required_digits = width.required_digits();
        assert!(required_digits >= 1);
        use rand::distributions::{
            Distribution,
            Standard,
        };
        let random_digits = Standard.sample_iter(rng).take(required_digits);
        // The truncation will be cheap always!
        ApInt::from_iter(random_digits)
            .expect(
                "We asserted that `required_digits` is at least `1` or greater
                     so it is safe to assume that `ApInt::from_iter` won't fail.",
            )
            .into_truncate(width)
            .expect(
                "`BitWidth::required_digits` returns an upper bound for the
                     number of required digits, so it is safe to truncate.",
            )
    }

    /// Randomizes the digits of this `ApInt` inplace.
    ///
    /// This won't change its `BitWidth`.
    pub fn randomize(&mut self) {
        self.randomize_using(&mut rand::rngs::SmallRng::from_entropy())
    }

    /// Randomizes the digits of this `ApInt` inplace using the given
    /// random number generator.
    ///
    /// This won't change its `BitWidth`.
    pub fn randomize_using<R>(&mut self, rng: &mut R)
    where
        R: rand::Rng,
    {
        use rand::distributions::{
            Distribution,
            Standard,
        };
        let std_dist = Standard.sample_iter(rng);
        self.digits_mut().zip(std_dist).for_each(|(d, r)| *d = r);
        self.clear_unused_bits();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    #[test]
    fn random_with_width_using() {
        let default_seed = <XorShiftRng as rand::SeedableRng>::Seed::default();
        let mut rng = XorShiftRng::from_seed(default_seed);
        assert_eq!(
            ApInt::random_with_width_using(BitWidth::w1(), &mut rng),
            ApInt::from_bit(true)
        );
        assert_eq!(
            ApInt::random_with_width_using(BitWidth::w8(), &mut rng),
            ApInt::from_u8(100)
        );
        assert_eq!(
            ApInt::random_with_width_using(BitWidth::w16(), &mut rng),
            ApInt::from_u16(30960)
        );
        assert_eq!(
            ApInt::random_with_width_using(BitWidth::w32(), &mut rng),
            ApInt::from_u32(1788231528)
        );
        assert_eq!(
            ApInt::random_with_width_using(BitWidth::w64(), &mut rng),
            ApInt::from_u64(13499822775494449820)
        );
        assert_eq!(
            ApInt::random_with_width_using(BitWidth::w128(), &mut rng),
            ApInt::from([16330942765510900160_u64, 131735358788273206])
        );
    }

    #[test]
    fn randomize_using() {
        let default_seed = <XorShiftRng as rand::SeedableRng>::Seed::default();
        let mut rng1 = XorShiftRng::from_seed(default_seed);
        let mut rng2 = XorShiftRng::from_seed(default_seed);

        {
            let mut randomized = ApInt::from_bit(false);
            randomized.randomize_using(&mut rng1);
            let new_random = ApInt::random_with_width_using(BitWidth::w1(), &mut rng2);
            assert_eq!(randomized, new_random);
        }
        {
            let mut randomized = ApInt::from_u8(0);
            randomized.randomize_using(&mut rng1);
            let new_random = ApInt::random_with_width_using(BitWidth::w8(), &mut rng2);
            assert_eq!(randomized, new_random);
        }
        {
            let mut randomized = ApInt::from_u16(0);
            randomized.randomize_using(&mut rng1);
            let new_random = ApInt::random_with_width_using(BitWidth::w16(), &mut rng2);
            assert_eq!(randomized, new_random);
        }
        {
            let mut randomized = ApInt::from_u32(0);
            randomized.randomize_using(&mut rng1);
            let new_random = ApInt::random_with_width_using(BitWidth::w32(), &mut rng2);
            assert_eq!(randomized, new_random);
        }
        {
            let mut randomized = ApInt::from_u64(0);
            randomized.randomize_using(&mut rng1);
            let new_random = ApInt::random_with_width_using(BitWidth::w64(), &mut rng2);
            assert_eq!(randomized, new_random);
        }
        {
            let mut randomized = ApInt::from_u128(0);
            randomized.randomize_using(&mut rng1);
            let new_random = ApInt::random_with_width_using(BitWidth::w128(), &mut rng2);
            assert_eq!(randomized, new_random);
        }
    }
}
