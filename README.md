# ApInt - Arbitrary Precision Integer

|        Linux        |       Windows       |       Codecov        |       Coveralls      |       Docs       |       Crates.io      |
|:-------------------:|:-------------------:|:--------------------:|:--------------------:|:----------------:|:--------------------:|
| [![travisCI][1]][2] | [![appveyor][3]][4] | [![codecov][15]][16] | [![coveralls][5]][6] | [![docs][11]][12] | [![crates][13]][14] |

**Development in progress:** *The implementation has not been finished and may not work.*

**A**rbitrary **p**recision **Int**egers (**ApInt**) represent integers that have an arbitrary but fixed runtime bit-width and offers two's complement modulo arithmetic equal to machine integers.

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
- Use it like any big integer library, except that the user manages resizes and allocations.

## Internals

The design focus is at efficiency and robustness.
An `ApInt` constists of a sequence of `Digit`s.
A `Digit` is `u64` by default, but this can be changed TODO
`ApInt` instances are small-value-optimized. This means that only `ApInt` instances with a bit-width larger than the number of bits in a `Digit` allocate dynamic memory.

Very little `unsafe` is used outside of managing internal `union`s, by default. The robustness of `ApInt` operations is backed by extensive fuzz testing (including unit, regression, random input, and edge case testing in multiple flag modes).
Internal bounds checking is on by default but can be turned off and `unsafe` indexing turned on by the TODO flag. To be clear, input checks to functions will still be on (e.g. functions will still return `Err`s if input bit widths are not matching). This has the advantage of increasing performance by approximately TODO, but be warned that if a bug is encountered it will cause undefined behavior instead of panicking like it does when the flag is off.
Even with the TODO flag enabled, `apint` is still arguably one of the safest big integer libraries because of intensive testing with the flag enabled and disabled.

## Performance

For best performance, compile with `O3`, `panic=abort`, `cpu=native` (which can have a decent impact on some CPUs due to better CPU-specific shifting and `.leading_zeros()` functions), TODO (see "Internals" above).

## Differences & Parallels

The below table lists public and internal differences between `ApInt` and `num::BigInt`.

|        Topic             |               `num::BigInt`               |               `ApInt`                   |
|:------------------------:|:------------------------------------------|:----------------------------------------|
| Abstraction              | High-level unbounded integers.            | Twos-complement machine integers.       |
| Behaviour                | Behaves like an immutable type most often. This results in lots of copies and better usability. | API design with a focus on efficient operations and machine emulation. |
| Small Value Optimization | No                                        | Yes: Up to 64-bits.                     |
| Building Blocks          | 32-bit `BigDigit` aka `u32`               | 64-bit `Digit` (by default)             |
| Compute Unit             | 64-bit `DoubleBigDigit` aka `u64`         | 128-bit `DoubleDigit`                   |
| Signed                   | Yes: `num::BigUint` is for unsigned.      | No: Operations know signedness instead. |
| `mem::size_of<..>`       | About 24 bytes + some signedness info.    | Exactly 128 bits (16 bytes). (this is assuming pointer widths are 64 bits)           |
| Width interoperability   | No restriction to operate between `BigInt` instances with different bit-widths. | Only `ApInt` instances with the same bit-width can interoperate. |
| Memory footprint         | Determined by current value stored.       | Determined by bit-width.                |
| Grows and shrinks automatically? | Yes                               | No                                      |
| Unstable features?       | None                                      | Stable as of Rust 1.31.                 |

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
- Mid-level `ApsInt` wrapper around `ApInt` that stores a run-time sign information. This is different from `Int` and `UInt` since those types store their sign immutable in their type. This is the same as LLVM's `APSInt` data type. These also allow for more efficient multiplication and division operations on negative numbers (see the documentation for those).
- Low level unsafe functions that have no bounds checking, allow for `ApInt`s of different bit widths to be operated on, and have access to reusing internal allocations for calculations that require allocated temporaries.
- More efficient operations.

## License

Licensed under either of

- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

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

### Version 0.3.0 TODO

- Removed `Bit`, changed `ApInt::from_bit` to `ApInt::from_bool`
- Add circular shift functions like `rotate_left_assign`.
- reorganized internals with updated dependencies followed by `rustfmt`ing and clippy
- Add the TODO flag.
- `Digit` can now easily be changed to be a `u32`.
- Corrected README.md for markdown lints.

### Version 0.2.0 - 2018-05-16

- Rename many functions from `_checked_` to `_wrapping_` and clarified documentation
- Added division functions
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
