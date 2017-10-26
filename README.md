APInt - Arbitrary Precision Integers for Rust
=============================================

|        Linux        |       Windows       |       Codecov        |       Coveralls      |       Docs       |       Crates.io      |
|:-------------------:|:-------------------:|:--------------------:|:--------------------:|:----------------:|:--------------------:|
| [![travisCI][1]][2] | [![appveyor][3]][4] | [![codecov][15]][16] | [![coveralls][5]][6] | [![docs][11]][12] | [![crates][13]][14] |

**Development in progress:** *The implementation has not been finished, is unstable and may not work.*

**A**rbitrary **P**recision **Int**egers (**APInt**) are a way to handle integers that have an arbitrary but 
fixed (on runtime) bit-width and offer modulo arithmetic similar to the primitive machine integers.

This library and its API are based on the popular LLVM [`APInt`](http://llvm.org/doxygen/classllvm_1_1APInt.html) support library
which is used quite heavily within the compiler and compiler-based tools. To model machine numbers during the compilation process.

Uses cases may vary greatly - the initial motivation for building this library was for use in an SMT solver
that operates mainly on the theory of bitvectors.

## Internals

The design focus was for efficiency and stability. `APInt` instances are space-optimized for
bit-widths equal to or smaller than `64` bits - only larger bit-widths require dynamic memory allocation!
For small bit-widths a compute buffer of `128` bits is used which is realized by the currently unstable
Rust language feature `i128` that will hopefully be stabilized soon as this is the only stable channel blocker so far.

The public interface functions avoid panicing and promote returning `Result`s and decent quality error codes instead.
Some convenience arithmetic operators are overloaded in the cases where it is useful - those do panic as it is 
convenient for them to be homogenous in input and output types.

## Current State

Currently only a part of the internal implementation is done. Especially the implementation of the large `APInt`'s
with bit-widths greater than `64` bits are lacking a lot of implementation code. However, this should not be a major problem
since this crate is so similar to the well known `APInt` of LLVM as already stated above.

It is planned to add `SAPInt` (*S*igned *A*rbitrary *P*recision *Int*eger) an optional interface on top of `APInt` to
further add some signedness information. This will behave similar to LLVM's `APSInt` type.

## Planned Features

- Full `APInt` implementation with focus on efficiency and stability
- `SAPInt` interface layer on top of `APInt` to add signess information
- Extensive test suite to provide a decent quality implementation guarantee
- Hopefully soon on stable - as soon as `i128` is stabilized

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
