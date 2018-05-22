use apint::{ApInt};
use bitwidth::{BitWidth};
use digit::{Digit};

use rand;

impl rand::Rand for Digit {
    /// Creates a random `Digit` using the given random number generator.
    fn rand<R: rand::Rng>(rng: &mut R) -> Digit {
        Digit(rng.next_u64())
    }
}

/// # Random Utilities using `rand` crate.
impl ApInt {
    /// Creates a new `ApInt` with the given `BitWidth` and random `Digit`s.
    pub fn random_with_width(width: BitWidth) -> ApInt {
        ApInt::random_with_width_using(width, &mut rand::weak_rng())
    }

    /// Creates a new `ApInt` with the given `BitWidth` and random `Digit`s
    /// using the given random number generator.
    /// 
    /// **Note:** This is useful for cryptographic or testing purposes.
    pub fn random_with_width_using<R>(width: BitWidth, rng: &mut R) -> ApInt
        where R: rand::Rng
    {
        let required_digits = width.required_digits();
        assert!(required_digits >= 1);
        let random_digits = rng.gen_iter::<Digit>().take(required_digits);
        ApInt::from_iter(random_digits)
            .expect("We asserted that `required_digits` is at least `1` or greater
                     so it is safe to assume that `ApInt::from_iter` won't fail.")
            .into_truncate(width) // This truncation will be cheap always!
            .expect("`BitWidth::required_digits` returns an upper bound for the
                     number of required digits, so it is safe to truncate.")
    }

    /// Randomizes the digits of this `ApInt` inplace.
    /// 
    /// This won't change its `BitWidth`.
    pub fn randomize(&mut self) {
        self.randomize_using(&mut rand::weak_rng())
    }

    /// Randomizes the digits of this `ApInt` inplace using the given
    /// random number generator.
    /// 
    /// This won't change its `BitWidth`.
    pub fn randomize_using<R>(&mut self, rng: &mut R)
        where R: rand::Rng
    {
        self.digits_mut()
            .zip(rng.gen_iter::<Digit>())
            .for_each(|(d, r)| *d = r);
        self.clear_unused_bits();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn random_with_width_using() {
        let mut rng = rand::XorShiftRng::new_unseeded();
        let r = &mut rng;
        assert_eq!(ApInt::random_with_width_using(BitWidth::w1(), r), ApInt::from_bit(false));
        assert_eq!(ApInt::random_with_width_using(BitWidth::w8(), r), ApInt::from_u8(140));
        assert_eq!(ApInt::random_with_width_using(BitWidth::w16(), r), ApInt::from_u16(970));
        assert_eq!(ApInt::random_with_width_using(BitWidth::w32(), r), ApInt::from_u32(2466290541));
        assert_eq!(ApInt::random_with_width_using(BitWidth::w64(), r), ApInt::from_u64(16730135874920933484));
        assert_eq!(ApInt::random_with_width_using(BitWidth::w128(), r), ApInt::from_u128(217725508292902744084870179638383324996));
    }

    #[test]
    fn randomize_using() {
        let mut rng1 = rand::XorShiftRng::new_unseeded();
        let mut rng2 = rand::XorShiftRng::new_unseeded();
        let r1 = &mut rng1;
        let r2 = &mut rng2;

        {
            let mut randomized = ApInt::from_bit(false);
            randomized.randomize_using(r1);
            let new_random = ApInt::random_with_width_using(BitWidth::w1(), r2);
            assert_eq!(randomized, new_random);
        }{
            let mut randomized = ApInt::from_u8(0);
            randomized.randomize_using(r1);
            let new_random = ApInt::random_with_width_using(BitWidth::w8(), r2);
            assert_eq!(randomized, new_random);
        }{
            let mut randomized = ApInt::from_u16(0);
            randomized.randomize_using(r1);
            let new_random = ApInt::random_with_width_using(BitWidth::w16(), r2);
            assert_eq!(randomized, new_random);
        }{
            let mut randomized = ApInt::from_u32(0);
            randomized.randomize_using(r1);
            let new_random = ApInt::random_with_width_using(BitWidth::w32(), r2);
            assert_eq!(randomized, new_random);
        }{
            let mut randomized = ApInt::from_u64(0);
            randomized.randomize_using(r1);
            let new_random = ApInt::random_with_width_using(BitWidth::w64(), r2);
            assert_eq!(randomized, new_random);
        }{
            let mut randomized = ApInt::from_u128(0);
            randomized.randomize_using(r1);
            let new_random = ApInt::random_with_width_using(BitWidth::w128(), r2);
            assert_eq!(randomized, new_random);
        }
    }
}
