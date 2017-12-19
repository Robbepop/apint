use errors::{Result};
use bitwidth::{BitWidth};

pub(crate) trait Width {
	fn width(&self) -> BitWidth;
}

pub(crate) trait ApIntMutImpl<I>
	where I: Width
{
	fn neg_inplace(&mut self);
	fn add_inplace(&mut self, other: &I) -> Result<()>;
	fn sub_inplace(&mut self, other: &I) -> Result<()>;
	fn mul_inplace(&mut self, other: &I) -> Result<()>;
	fn sdiv_inplace(&mut self, other: &I) -> Result<()>;
	fn udiv_inplace(&mut self, other: &I) -> Result<()>;
	fn srem_inplace(&mut self, other: &I) -> Result<()>;
	fn urem_inplace(&mut self, other: &I) -> Result<()>;
}
