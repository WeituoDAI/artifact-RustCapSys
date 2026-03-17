## Overview

`my_type_system.v` : formalization of the Rust capability type system including the proof of capability validity and capability unforgeability.

## Installation

### Requirement

- The Rocq Prover, version 9.1.1 compiled with OCaml 4.14.1
- rocq-iris dev.2026-01-30.0.9c05
- lambda-rust 2fb071653b08f9808fb94aa53e27b58b9c83486a

Guide for preparing the environment:

1. Install opam, Rocq Prover
2. Install the lambda-rust library (https://gitlab.mpi-sws.org/iris/lambda-rust)
3. In the root of lambda-rust project installed, run the following command :
```
# opam pin add coq-lambda-rust
```

## Verification

Run the following command in the current folder:
```
# eval $(opam env)
# make
```