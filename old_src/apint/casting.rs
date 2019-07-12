
use apint::{ApInt};
use errors::{Error, Result};

use bitwidth::{BitWidth};
use storage::{Storage};
use digit::{Bit};
use traits::Width;
use utils::{try_forward_bin_mut_impl, forward_bin_mut_impl};

impl Clone for ApInt {
    fn clone(&self) -> Self {
        match self.storage() {
            Storage::Inl => {
                ApInt::new_inl(self.len, unsafe{ self.data.inl })
            }
            Storage::Ext => {
                use std::mem;
                let req_digits = self.len_digits();
                let mut buffer = self.as_digit_slice()
                    .to_vec()
                    .into_boxed_slice();
                assert_eq!(buffer.len(), req_digits);
                let ptr_buffer = buffer.as_mut_ptr();
                mem::forget(buffer);
                unsafe{ ApInt::new_ext(self.len, ptr_buffer) }
            }
        }
    }
}

/// # Assignment Operations
impl ApInt {
    /// Assigns `rhs` to this `ApInt`.
    ///
    /// This mutates digits and may affect the bitwidth of `self`
    /// which **might result in an expensive operations**.
    ///
    /// After this operation `rhs` and `self` are equal to each other.
    pub fn assign(&mut self, rhs: &ApInt) {
        if self.len_digits() == rhs.len_digits() {
            // If `self` and `rhs` require the same amount of digits
            // for their representation we can simply utilize `ApInt`
            // invariants and basically `memcpy` from `rhs` to `self`.
            // Afterwards a simple adjustment of the length is sufficient.
            // (At the end of this method.)
            self.as_digit_slice_mut()
                .copy_from_slice(rhs.as_digit_slice());
        }
        else {
            // In this case `rhs` and `self` require an unequal amount
            // of digits for their representation which means that the
            // digits that may be allocated by `self` must be dropped.
            //
            // Note that `ApInt::drop_digits` only deallocates if possible.
            unsafe{ self.drop_digits(); }

            match rhs.storage() {
                Storage::Inl => {
                    // If `rhs` is a small `ApInt` we can simply update
                    // the `digit` field of `self` and we are done.
                    self.data.inl = unsafe{ rhs.data.inl };
                }
                Storage::Ext => {
                    // If `rhs` is a large heap-allocated `ApInt` we first
                    // need to expensively clone its buffer and feed it to `self`.
                    let cloned = rhs.clone();
                    self.data.ext = unsafe{ cloned.data.ext };
                    use std::mem;
                    mem::forget(cloned);
                }
            }
        }
        // Since all cases may need bit width adjustment we outsourced it
        // to the end of this method.
        self.len = rhs.len;
    }

    /// Strictly assigns `rhs` to this `ApInt`.
    /// 
    /// After this operation `rhs` and `self` are equal to each other.
    /// 
    /// **Note:** Strict assigns protect against mutating the bit width
    /// of `self` and thus return an error instead of executing a probably
    /// expensive `assign` operation.
    /// 
    /// # Errors
    /// 
    /// - If `rhs` and `self` have unmatching bit widths.
    pub fn strict_assign(&mut self, rhs: &ApInt) -> Result<()> {
        if self.width() != rhs.width() {
            return Error::unmatching_bitwidths(self.width(), rhs.width())
                .with_annotation(format!(
                    "Occured while trying to `strict_assign` {:?} to {:?}.", self, rhs))
                .into()
        }
        self.as_digit_slice_mut()
            .copy_from_slice(rhs.as_digit_slice());
        Ok(())
    }
}

