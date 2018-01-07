ApInt - Arbitrary Precision Integer
===================================

|        Linux        |       Windows       |       Codecov        |       Coveralls      |       Docs       |       Crates.io      |
|:-------------------:|:-------------------:|:--------------------:|:--------------------:|:----------------:|:--------------------:|
| [![travisCI][1]][2] | [![appveyor][3]][4] | [![codecov][15]][16] | [![coveralls][5]][6] | [![docs][11]][12] | [![crates][13]][14] |

**Development in progress:** *The implementation has not been finished, is unstable and may not work.*

An **A**rbitrary **p**recision **Int**eger (**ApInt**) represents an integer that has an arbitrary but 
fixed runtime bit-width and offers two's complement modulo arithmetic equal to machine integers.

The API is based on the popular LLVM [`APInt`](http://llvm.org/doxygen/classllvm_1_1APInt.html) support library
that is heavily used within the compiler and compiler based tools.

## Example Use Cases

- Simulate machine arithmetic on compilation, e.g. for constant evaluation and some optimizations.
- SMT solvers may use this as an underlying model for the theory of bitvectors.

## Internals

The design focus is at efficiency and robustness.
`ApInt` instances are small-value-optimized. This means that only `ApInt` instances with a bit-width larger than 64 bits allocate dynamic memory.

An `ApInt` constists of a sequence of 64-bit `Digit`s.
Computations are done within their 128-bit `DoubleDigit` form to prevent bit-loss on over- or underflows.
This implies a dependency on 128-bit integers which are currently unstable in Rust.

## Differences & Parallels

The below table lists public and internal differences between `ApInt` and `num::BigInt`.

|        Topic             |               `num::BigInt`               |               `ApInt`                   |
|:------------------------:|:------------------------------------------|:----------------------------------------|
| Abstraction              | High-level unbounded integers.            | Twos-complement machine integers.       |
| Behaviour                | Behaves like an immutable type most often. This results in lots of copies and better usability. | API design with a focus on efficient operations and machine emulation. |
| Small Value Optimization   | No                                        | Yes: Up to 64-bits.                     |
| Building Blocks          | 32-bit `BigDigit` aka `u32`               | 64-bit `Digit`                          |
| Compute Unit             | 64-bit `DoubleBigDigit` aka `u64`         | 128-bit `DoubleDigit`                   |
| Signed                   | Yes: `num::BigUint` is for unsigned.      | No: Operations know signedness instead. |
| `mem::size_of<..>`       | About 24 bytes + some signedness info.    | Exactly 128 bits (16 bytes).            |
| Width interoperability   | No restriction to operate between `BigInt` instances with different bit-widths. | Only `ApInt` instances with the same bit-width can interoperate. |
| Memory footprint         | Determined by current value stored.       | Determined by bit-width.                |
| Can grow and shrink?     | Yes                                       | No, see above.                          |
| Unstable features?       | None                                      | Yes, e.g. [128-bit integers][17].                  |

## Current State

Currently only a few parts of the implementation are done - especially the implementation of `ApInt`'s with bit-widths greater than 64 bits is incomplete.

State of the API modules implemented so far:

|        Module       | Design | Implementation | Testing | TODO |
|:-------------------:|:------:|:--------------:|:-------:|:----:|
| `arithmetic`        | **done** | unfinished | unfinished | |
| `constructors`      | **done** | **done** | **done** | |
| `casting`           | **done** | **done** | *not started* | issue [#4](https://github.com/Robbepop/apint/issues/4) |
| `bitwise`           | **done** | **done** | *not started* | |
| `shift`             | **done** | **done** |  **done** | |
| `relational`        | **done** | **done** | *not started* | |
| `utils`             | **done** | **done** | *not started* | |
| `serialization`     | **done** | unfinished | unfinished | depends on `arithmetic` |
| `to_primitive`      | **done** | **done** | **done** | |
| `serde_impl` (opt.) | **done** | **done** | **done** | |
| `rand_impl` (opt.)  | **done** | **done** | **done** | |

## Planned Features

- Full and efficient `ApInt` implementation and decent test coverage.
- High-level `SignedApInt` and `UnsignedApInt` types that wrap `ApInt` with static sign information
  allowing for improved user friendliness but restricted access to the underlying operations.
- Mid-level `ApsInt` wrapper around `ApInt` that stores a run-time sign information.
  This is different from `SignedApInt` and `UnsignedApInt` since those types store
  their sign immutable in their type. This is the same as LLVM's `APSInt` data type.

## Unstable Features Used

These features need to be stabilized before this crate can be used on the stable channel.

- [`#![feature(i128_type)]`][17]
- [`#![feature(conservative_impl_trait)]`][18]
- [`#![feature(unique)]`][19]
- [`#![feature(slice_rotate)`][20]

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Dual licence: [![badge][7]](LICENSE-MIT) [![badge][8]](LICENSE-APACHE)

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.

[1]: https://travis-ci.org/Robbepop/apint.svg?branch=master
[2]: https://travis-ci.org/Robbepop/apint
[3]: https://ci.appveyor.com/api/projects/status/16fc9l6rtroo4xqd?svg=true
[4]: https://ci.appveyor.com/project/Robbepop/apint/branch/master
[5]: https://coveralls.io/repos/github/Robbepop/apint/badge.svg?branch=master
[6]: https://coveralls.io/github/Robbepop/apint?branch=master
[7]: https://img.shields.io/badge/license-MIT-blue.svg
[8]: https://img.shields.io/badge/license-APACHE-orange.svg
[9]: ./LICENSE-MIT
[10]: ./LICENSE-APACHE
[11]: https://docs.rs/apint/badge.svg
[12]: https://docs.rs/apint/0.0.0-alpha.8
[13]: https://img.shields.io/crates/v/apint.svg
[14]: https://crates.io/crates/apint/0.0.0-alpha.8
[15]: https://codecov.io/gh/robbepop/apint/branch/master/graph/badge.svg
[16]: https://codecov.io/gh/Robbepop/apint/branch/master

[17]: https://github.com/rust-lang/rust/issues/35118
[18]: https://github.com/rust-lang/rust/issues/34511
[19]: https://github.com/rust-lang/rust/issues/27730
[20]: https://github.com/rust-lang/rust/issues/41891
