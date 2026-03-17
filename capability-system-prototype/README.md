# capability-system-prototype

## Overview

- `cap.rs` : main data structures, executable functions
- `abs.rs` : abstract state machine
- `proof` : proof of the isolation, the capability unforgeability

## Verification

Install Verus as described [in the official documentation](https://github.com/verus-lang/verus/blob/main/INSTALL.md).

If Verus is installed, you can verify the project by
```
#Replace $verus with the path to the verus binary
$verus ./main.rs
```

(or you can set the path of "Verifier" in `Makefile` and use it)

You should see output like this: 
```
[...]
verification results:: 54 verified, 0 errors
```