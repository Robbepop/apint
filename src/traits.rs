use bitwidth::{BitWidth};

pub(crate) trait Width {
	fn width(&self) -> BitWidth;
}
