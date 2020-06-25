//! Shim over `alloc` and `std` alloc utilities.

#[cfg(not(feature = "std"))]
mod no_std_defs {
    // We could use `core::` to import these directly instead of through `mem`, but
    // this removes the need to type out `::convert`, `::num`, and some extra
    // braces for every use in the crate.
    pub use core::{
        convert::{
            TryFrom,
            TryInto,
        },
        num::NonZeroUsize,
    };

    pub use alloc::{
        borrow,
        boxed,
        format,
        string,
        vec,
    };

    /// Collection types.
    pub mod collections {
        pub use self::{
            BTreeMap,
            BTreeSet,
            BinaryHeap,
            LinkedList,
            VecDeque,
        };
        pub use alloc::collections::*;
        pub use core::ops::Bound;
    }
}

#[cfg(feature = "std")]
mod std_defs {
    pub use std::{
        borrow,
        boxed,
        convert::{
            TryFrom,
            TryInto,
        },
        format,
        num::NonZeroUsize,
        string,
        vec,
    };

    /// Collection types.
    pub mod collections {
        pub use self::{
            binary_heap::BinaryHeap,
            btree_map::BTreeMap,
            btree_set::BTreeSet,
            linked_list::LinkedList,
            vec_deque::VecDeque,
            Bound,
        };
        pub use std::collections::*;
    }
}

#[cfg(not(feature = "std"))]
#[doc(inline)]
pub use self::no_std_defs::*;

#[cfg(feature = "std")]
#[doc(inline)]
pub use self::std_defs::*;
