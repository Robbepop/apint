ApInt - Arbitrary Precision Integer
===================================

|        Linux        |       Windows       |       Codecov        |       Coveralls      |       Docs       |       Crates.io      |
|:-------------------:|:-------------------:|:--------------------:|:--------------------:|:----------------:|:--------------------:|
| [![travisCI][1]][2] | [![appveyor][3]][4] | [![codecov][15]][16] | [![coveralls][5]][6] | [![docs][11]][12] | [![crates][13]][14] |

**Development in progress:** *The implementation has not been finished and may not work.*

**A**rbitrary **p**recision **Int**egers (**ApInt**) represent integers that have an arbitrary but 
fixed runtime bit-width and offers two's complement modulo arithmetic equal to machine integers.

The integer types offered by this library are:

- [`ApInt`][30]: A low-level arbitrary-precision integer without static signedness information. (General)
- [`Int`][31]: A signed arbitrary-precision integer. (Convenience for `iN`.)
- [`UInt`][32]: An unsigned arbitrary-precision integer. (Convenience for `uN`.)

The API is based on the LLVM [`APInt`](http://llvm.org/doxygen/classllvm_1_1APInt.html) support library.

## Example Use Cases

- Emulate machine arithmetic on compilation, e.g. for constant evaluation and some optimizations.
- SMT solvers may use this as an underlying model for the theory of bitvectors.
- Operations and backend for cryptographic keys.
- Also usable as a simple bitset with runtime length information.

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
| Small Value Optimization | No                                        | Yes: Up to 64-bits.                     |
| Building Blocks          | 32-bit `BigDigit` aka `u32`               | 64-bit `Digit`                          |
| Compute Unit             | 64-bit `DoubleBigDigit` aka `u64`         | 128-bit `DoubleDigit`                   |
| Signed                   | Yes: `num::BigUint` is for unsigned.      | No: Operations know signedness instead. |
| `mem::size_of<..>`       | About 24 bytes + some signedness info.    | Exactly 128 bits (16 bytes).            |
| Width interoperability   | No restriction to operate between `BigInt` instances with different bit-widths. | Only `ApInt` instances with the same bit-width can interoperate. |
| Memory footprint         | Determined by current value stored.       | Determined by bit-width.                |
| Can grow and shrink?     | Yes                                       | No, see above.                          |
| Unstable features?       | None                                      | Stable as of Rust 1.26.                 |

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
- Mid-level `ApsInt` wrapper around `ApInt` that stores a run-time sign information.
  This is different from `Int` and `UInt` since those types store
  their sign immutable in their type. This is the same as LLVM's `APSInt` data type.

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
[12]: https://docs.rs/apint/
[13]: https://img.shields.io/crates/v/apint.svg
[14]: https://crates.io/crates/apint/
[15]: https://codecov.io/gh/robbepop/apint/branch/master/graph/badge.svg
[16]: https://codecov.io/gh/Robbepop/apint/branch/master

[17]: https://github.com/rust-lang/rust/issues/35118
[18]: https://github.com/rust-lang/rust/issues/34511
[19]: https://github.com/rust-lang/rust/issues/41891

[30]: https://docs.rs/apint/0.1.0/apint/struct.APInt.html
[31]: https://docs.rs/apint/0.1.0/apint/struct.Int.html
[32]: https://docs.rs/apint/0.1.0/apint/struct.UInt.html

## Release Notes

### Version 0.2.0 - 2018-05-16

- Add `Binary`, `LowerHex` and `UpperHex` impls to `Int`, `UInt` and `ApInt`.  
  Note that implementations for `Octal` are still missing.

### Version 0.1.0 - 2018-04-15

- Removed strict casting methods in `ApInt`, `Int` and `UInt`.
- Add `into_bitnot` to `ApInt`, `Int` and `UInt`.
- Add division-by-zero error and managing around it for respective operations.
- Add a crate prelude module for simple usage of commonly used types.
- Fixed bug in `ApInt::sign_extend` and `Int::extend` (issue [#15](https://github.com/Robbepop/apint/issues/15)). Thanks [AaronKutch](https://github.com/AaronKutch) for reporting!
- Fixed markdown headers of many public impl blocks.
- Fixed several documentation comments of public APIs, like `ApInt::from_{i128, u128}`.
- Fixed several minor bugs due to forwarding to wrong implementation methods.
