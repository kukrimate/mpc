# MPC
**M**a**P**le **C**ompiler. The initial implementation of the Maple programming language.

## Dependencies
MPC has two dependencies, that need to be manually installed.

MPC is written in Rust, requiring `rustc` nightly for compilation,
and Cargo as a build system. Both of which can be acquired from:
> https://www.rust-lang.org/tools/install

LLVM 15 is used as a code generation backend. It may need to be manually
installed if not bundled with the host operating system. It can be obtained from:
> https://releases.llvm.org/

## Portability
While MPC should be able to run on all platforms targeted by recent rustc, that can host LLVM 15.

For ease of development, currently only 64-bit macOS, and 64-bit Linux are considered supported.

There is also no support for cross-compilation, and the target is implicitly assumed to be the
host platform's default LLVM target.

## Compilation

If not bundled with the operating system, set the environment variable
`LLVM_SYS_150_PREFIX` to point to the directory where LLVM 15 was installed,
e.g:
```
export LLVM_SYS_150_PREFIX=/opt/llvm-15
```

Then MPC can be built with Cargo, either in Debug mode (which is also default):
```
cargo build --debug
```

Or in release mode, which enables various optimizations in Rustc, and disables
some runtime checks. This mode should be used for MPC binaries distributed to
users:
```
cargo build --release
```

The resulting binary, in both cases, will sit inside a subdirectory of the
`target` directory.

## Installation
The MPC binary will contain the (compile time) value of the environment variable
`MPC_STD_DIR`, and this will be used as the directory to search for the MPC
standard library. This by default is pointed to the `mpc_std` subdirectory in
the source tree. When installed, this should point to the directory where the
contents of `mpc_std` were installed.

To automate the installation process of both MPC and the standard library,
a script, namely `install.sh` is provided. This can be used to install MPC with
its standard library to a specified installation prefix, e.g:
```
PREFIX=/usr/local ./install.sh
```

## Integration tests
MPC includes an automated integration testing suite, that can be executed with:
```
cargo run --bin mpc_test
```

## Copyright
All non-trivial files in this repository are distributed under version 2.0 (only) of the GNU GPL, and
> Copyright (C) Mate Kukri, 2022-2023.
