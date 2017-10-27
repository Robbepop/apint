APInt - Arbitrary Precision Integers for Rust
=============================================

|        Linux        |       Windows       |       Codecov        |       Coveralls      |       Docs       |       Crates.io      |
|:-------------------:|:-------------------:|:--------------------:|:--------------------:|:----------------:|:--------------------:|
| [![travisCI][1]][2] | [![appveyor][3]][4] | [![codecov][15]][16] | [![coveralls][5]][6] | [![docs][11]][12] | [![crates][13]][14] |

**Development in progress:** *The implementation has not been finished, is unstable and may not work.*

**A**rbitrary **P**recision **Int**egers (**APInt**) represent integers that have an arbitrary but 
fixed runtime bit-width and offer twos-complement modulo arithmetic similar to machine integers.

The API is based on the popular LLVM [`APInt`](http://llvm.org/doxygen/classllvm_1_1APInt.html) support library
that is heavily used within the compiler and compiler-based tools.

## Example Use Cases

- Simulate machine numbers during the compilation process of compilers.
- SMT solver to model theory of bitvectors.

## Internals

The design focus is efficiency and robustness.
`APInt` instances are space-optimized for bit-width smaller than or equal to 64 bits.
Only `APInt` instances with a larger bit-width require dynamic memory allocation.

An `APInt` constists of a sequence of 64-bit `Digit`s.
Computations are done within their 128-bit `DoubleDigit` form to prevent bit-loss on over- or underflows.
This creates a dependency on 128-bit integers which are currently unstable in Rust.

## Differences & Parallels

The below table lists public and internal differences between `APInt` and `num::BigInt`.

|        Topic             |               `num::BigInt`               |               `APInt`                  |
|:------------------------:|:------------------------------------------|:---------------------------------------|
| Abstraction              | High-level unbounded integers.            | Twos-complement machine integers.      |
| Small Int Optimization   | No                                        | Yes: Up to 64-bits.                    |
| Building Blocks          | 32-bit `BigDigit` aka `u32`               | 64-bit `Digit`                         |
| Compute Unit             | 64-bit `DoubleBigDigit` aka `u64`         | 128-bit `DoubleDigit`                  |
| Signed                   | Yes, `num::BigUint` is for unsigned.      | No, operations know signdness instead. |
| `mem::size_of<..>`       | Equal to `Vec<..>` (about 24 bytes)       | Exactly 128 bits (16 bytes).           |
| Width interoperability   | No restriction to operate between `BigInt` instances with different bit-widths. | Only `APInt` instances with the same bit-width can interoperate. |
| Memory footprint         | Determined by current value stored.       | Determined by bit-width.               |
| Can grow and shrink?     | Yes                                       | No, see above.                         |
| Unstable features?       | None                                      | [128-bit integers][17]                 |

## Current State

Currently only parts of the implementation is done - especially the implementation of `APInt`'s with bit-widths greater than 64 bits are incompleted.

## Planned Features

- Full `APInt` implementation.
- `APSInt` API built on top of `APInt` to add signedness information as it is done in LLVM.
- Extensive test suite to provide a decent quality implementation guarantee.
- Hopefully soon on stable - as soon as [128-bit integers][17] are stabilized.

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Dual licence: [![badge][7]](LICENSE-MIT) [![badge][8]](LICENSE-APACHE)

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
[12]: https://docs.rs/apint
[13]: https://img.shields.io/crates/v/apint.svg
[14]: https://crates.io/crates/apint
[15]: https://codecov.io/gh/robbepop/apint/branch/master/graph/badge.svg
[16]: https://codecov.io/gh/Robbepop/apint/branch/master

[17]: https://github.com/rust-lang/rust/issues/35118
