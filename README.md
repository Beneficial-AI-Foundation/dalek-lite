
This repo is based on the `signal-curve25519-4.1.3` tag of https://github.com/signalapp/curve25519-dalek, with these changes:
- removed all crates besides `curve25519-dalek`
- removed all backends except for `serial/u64`
- commented out unit tests
- removed most CI workflows

It contains Verus proofs for a selection of functions. See these links for more information: 
- General overview: https://beneficial-ai-foundation.github.io/dalek-lite/index.html
- Proved function specifications: https://beneficial-ai-foundation.github.io/dalek-lite/specs.html

