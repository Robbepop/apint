use bitwidth::{BitWidth};

/// Types that have an associated bit width may implement `Width`.
pub trait Width {
    /// Returns the bit width of `self`.
    fn width(&self) -> BitWidth;
}
