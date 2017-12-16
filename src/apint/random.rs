use apint::{ApInt};
use bitwidth::{BitWidth};
use digit::{Digit};

use rand;

impl ApInt {
	/// Creates a new `ApInt` with the given `BitWidth` and random `Digit`s.
	pub fn random_with_width(width: BitWidth) -> ApInt {
		ApInt::random_with_width_using(width, rand::weak_rng())
	}

	/// Creates a new `ApInt` with the given `BitWidth` and random `Digit`s
    /// using the given random number generator.
    /// 
    /// **Note:** This is useful for cryptographic or testing purposes.
    pub fn random_with_width_using<R>(width: BitWidth, rng: R) -> ApInt
        where R: rand::Rng
    {
        let required_digits = width.required_digits();
        assert!(required_digits >= 1);
        let mut rng = rng;
        let random_digits = rng.gen_iter::<u64>().take(required_digits).map(Digit);
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
        self.randomize_using(rand::weak_rng())
    }

    /// Randomizes the digits of this `ApInt` inplace using the given 
    /// random number generator.
    /// 
    /// This won't change its `BitWidth`.
    pub fn randomize_using<R>(&mut self, rng: R)
        where R: rand::Rng
    {
        use digit_seq::AsDigitSeqMut;
        use traits::Width;
        let mut rng = rng;
        self.digits_mut()
            .zip(rng.gen_iter::<u64>().map(Digit))
            .for_each(|(d, r)| *d = r);
        use std::mem;
        let width = self.width();
        let this = mem::replace(self, ApInt::from_bit(false));
        let this = this.into_truncate(width)
            .expect("Truncating to its own width will simply restore the
                     invariant that excess bits are set to zero (`0`).");
        mem::replace(self, this);
    }
}
