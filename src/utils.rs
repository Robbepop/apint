use crate::errors::Result;

/// Consumes `entity` and forwards it to an inplace-mutating function.
///
/// Returns the entity afterwards.
pub fn forward_mut_impl<T, F>(entity: T, op: F) -> T
where
    F: Fn(&mut T) -> (),
{
    let mut this = entity;
    op(&mut this);
    this
}

/// Consumes `entity` and forwards it to an inplace-mutating function.
///
/// Returns the entity afterwards.
pub fn forward_bin_mut_impl<L, R, F>(entity: L, rhs: R, op: F) -> L
where
    F: Fn(&mut L, R) -> (),
{
    let mut this = entity;
    op(&mut this, rhs);
    this
}

/// Consumes `entity` and forwards it to an inplace-mutating function.
///
/// Returns the entity afterwards.
pub fn try_forward_bin_mut_impl<L, R, F>(entity: L, rhs: R, op: F) -> Result<L>
where
    F: Fn(&mut L, R) -> Result<()>,
{
    let mut this = entity;
    op(&mut this, rhs)?;
    Ok(this)
}
