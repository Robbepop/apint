use crate::data::{ApInt, Digit, Storage, ContiguousDigitSeq, ContiguousDigitSeqMut};
use crate::info::{Error, Width, Result};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) enum DataAccess<'a> {
    Inl(Digit),
    Ext(&'a [Digit])
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum DataAccessMut<'a> {
    Inl(&'a mut Digit),
    Ext(&'a mut [Digit])
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) enum ZipDataAccess<'a, 'b> {
    Inl(Digit, Digit),
    Ext(&'a [Digit], &'b [Digit])
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum ZipDataAccessMutSelf<'a, 'b> {
    Inl(&'a mut Digit, Digit),
    Ext(&'a mut [Digit], &'b [Digit])
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum ZipDataAccessMutBoth<'a, 'b> {
    Inl(&'a mut Digit, &'b mut Digit),
    Ext(&'a mut [Digit], &'b mut [Digit])
}

impl ApInt {
    pub(crate) fn digits(&self) -> ContiguousDigitSeq {
        ContiguousDigitSeq::from(self.as_digit_slice())
    }

    pub(crate) fn digits_mut(&mut self) -> ContiguousDigitSeqMut {
        ContiguousDigitSeqMut::from(self.as_digit_slice_mut())
    }

    /// Accesses the internal `Digit` data of this `ApInt` in a safe way.
    #[inline]
    pub(crate) fn access_data(&self) -> DataAccess {
        match self.storage() {
            Storage::Inl => DataAccess::Inl(unsafe{self.data.inl}),
            Storage::Ext => DataAccess::Ext(self.as_digit_slice())
        }
    }

    /// Mutably accesses the internal `Digit` data of this `ApInt` in a safe way.
    #[inline]
    pub(crate) fn access_data_mut(&mut self) -> DataAccessMut {
        match self.storage() {
            Storage::Inl => DataAccessMut::Inl(unsafe{&mut self.data.inl}),
            Storage::Ext => DataAccessMut::Ext(self.as_digit_slice_mut())
        }
    }

    /// Zips both given `ApInt` instances and tries to access their data in a safe way.
    /// 
    /// # Errors
    /// 
    /// - If both given `ApInt` instances have non-matching bit widths.
    #[inline]
    pub(crate) fn zip_access_data<'a, 'b>(&'a self, other: &'b ApInt) -> Result<ZipDataAccess<'a, 'b>> {
        if self.width() != other.width() {
            return Error::unmatching_bitwidths(self.width(), other.width()).into()
        }
        Ok(match self.storage() {
            Storage::Inl => {
                ZipDataAccess::Inl(
                    unsafe{ self.data.inl},
                    unsafe{other.data.inl})
            },
            Storage::Ext => {
                ZipDataAccess::Ext(
                    self.as_digit_slice(),
                    other.as_digit_slice())
            }
        })
    }

    /// Zips both given `ApInt` instances and tries to mutably access `self` data and immutably
    /// access `other` data in a safe way.
    /// 
    /// # Errors
    /// 
    /// - If both given `ApInt` instances have non-matching bit widths.
    #[inline]    
    pub(crate) fn zip_access_data_mut_self<'a, 'b>(&'a mut self, other: &'b ApInt) -> Result<ZipDataAccessMutSelf<'a, 'b>> {
        if self.width() != other.width() {
            return Error::unmatching_bitwidths(self.width(), other.width()).into()
        }
        Ok(match self.storage() {
            Storage::Inl => {
                ZipDataAccessMutSelf::Inl(
                    unsafe{&mut self.data.inl},
                    unsafe{other.data.inl})
            },
            Storage::Ext => {
                ZipDataAccessMutSelf::Ext(
                    self.as_digit_slice_mut(),
                    other.as_digit_slice())
            }
        })
    }

    /// Zips both given `ApInt` instances and tries to mutably access `lhs` and `rhs` data
    /// in a safe way.
    /// 
    /// # Errors
    /// 
    /// - If both given `ApInt` instances have non-matching bit widths.
    #[inline]    
    pub(crate) fn zip_access_data_mut_both<'a, 'b>(lhs: &'a mut ApInt, rhs: &'b mut ApInt) -> Result<ZipDataAccessMutBoth<'a, 'b>> {
        if lhs.width() != rhs.width() {
            return Error::unmatching_bitwidths(lhs.width(), rhs.width()).into()
        }
        Ok(match lhs.storage() {
            Storage::Inl => {
                ZipDataAccessMutBoth::Inl(
                    unsafe{&mut lhs.data.inl},
                    unsafe{&mut rhs.data.inl})
            },
            Storage::Ext => {
                ZipDataAccessMutBoth::Ext(
                    lhs.as_digit_slice_mut(),
                    rhs.as_digit_slice_mut())
            }
        })
    }
}