# MPC
**M**a**P**le **C**ompiler. The initial implementation of the Maple programming language.

## Testing
MPC includes an automated integration testing suite, that can be executed with:
```
cargo run --bin mpc_test
```

## Portability
While MPC should be able to run on all platforms targeted by recent rustc, that can host LLVM-13.

For ease of development, currently only 64-bit macOS, and 64-bit Linux are considered supported.

There is also no support for cross-compilation, and the target is implicitly assumed to be the
host platform's default LLVM target.

## Copyright
All non-trivial files in this repository are distributed under version 2.0 (only) of the GNU GPL, and
> Copyright (C) Mate Kukri, 2022-2023.
