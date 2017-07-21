mod constructors;
mod casting;
mod utils;
mod bitwise;
mod relational;
mod arithmetic;
mod shift;
// mod serialization;

use digit::{Digit};
use bitwidth::{BitWidth};

pub struct APInt {
	len : BitWidth,
	data: APIntData
}

union APIntData {
	inl: Digit,
	ext: *mut Digit
}

// #[derive(Debug, Clone)]
// enum Repr<'a> {
// 	Inl(ComputeBlock),
// 	Ext(ComputeBlockChain<'a>)
// }

// #[derive(Debug)]
// enum ReprMut<'a> {
// 	Inl(ComputeBlockMut<'a>),
// 	Ext(ComputeBlockChainMut<'a>)
// }

impl APInt {
	// fn repr(&self) -> Repr {
	// 	match self.len.storage() {
	// 		Storage::Inl => Repr::Inl(
	// 			ComputeBlock::new(self.len, unsafe{self.data.inl})),
	// 		Storage::Ext => Repr::Ext(
	// 			ComputeBlockChain::new(self.len, self.as_block_slice()))
	// 	}
	// }

	// fn repr_mut(&mut self) -> ReprMut {
	// 	match self.len.storage() {
	// 		Storage::Inl => ReprMut::Inl(
	// 			ComputeBlockMut::new(self.len, unsafe{&mut self.data.inl})),
	// 		Storage::Ext => ReprMut::Ext(
	// 			ComputeBlockChainMut::new(self.len, self.as_block_slice_mut()))
	// 	}
	// }
}
