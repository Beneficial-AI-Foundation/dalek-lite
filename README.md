<p align="center">
<img
 alt="dalek-cryptography logo: a dalek with edwards curves as sparkles coming out of its radar-schnozzley blaster thingies"
 width="200px"
 src="https://cdn.jsdelivr.net/gh/dalek-cryptography/curve25519-dalek/docs/assets/dalek-logo-clear.png"/>
</p>

# Dalek elliptic curve cryptography

This repo contains pure-Rust crates for elliptic curve cryptography:

|                 Crate                    |   Description  | Crates.io | Docs | CI                                                                                                                                                                                                                          |
-------------------------------------------|----------------|-----------|------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
| [`curve25519‑dalek`](./curve25519-dalek) | A library for arithmetic over the Curve25519 and Ristretto elliptic curves and their associated scalars. | [![](https://img.shields.io/crates/v/curve25519-dalek.svg)](https://crates.io/crates/curve25519-dalek) | [![](https://img.shields.io/docsrs/curve25519-dalek)](https://docs.rs/curve25519-dalek) | [![CI](https://github.com/dalek-cryptography/curve25519-dalek/actions/workflows/curve25519-dalek.yml/badge.svg?branch=main)](https://github.com/dalek-cryptography/curve25519-dalek/actions/workflows/curve25519-dalek.yml) |
| [`ed25519‑dalek`](./ed25519-dalek)       | An implementation of the EdDSA digital signature scheme over Curve25519. | [![](https://img.shields.io/crates/v/ed25519-dalek.svg)](https://crates.io/crates/ed25519-dalek) | [![](https://docs.rs/ed25519-dalek/badge.svg)](https://docs.rs/ed25519-dalek) | [![CI](https://github.com/dalek-cryptography/curve25519-dalek/actions/workflows/ed25519-dalek.yml/badge.svg?branch=main)](https://github.com/dalek-cryptography/curve25519-dalek/actions/workflows/ed25519-dalek.yml)       |
| [`x25519‑dalek`](./x25519-dalek)         | An implementation of elliptic curve Diffie-Hellman key exchange over Curve25519. | [![](https://img.shields.io/crates/v/x25519-dalek.svg)](https://crates.io/crates/x25519-dalek) | [![](https://docs.rs/x25519-dalek/badge.svg)](https://docs.rs/x25519-dalek) | [![CI](https://github.com/dalek-cryptography/curve25519-dalek/actions/workflows/x25519-dalek.yml/badge.svg?branch=main)](https://github.com/dalek-cryptography/curve25519-dalek/actions/workflows/x25519-dalek.yml)         |

There is also the [`curve25519-dalek-derive`](./curve25519-dalek-derive) crate, which is just a helper crate with some macros that make curve25519-dalek easier to write.

# Beneficial AI Foundation note

This repo is based on the `signal-curve25519-4.1.3` tag of https://github.com/signalapp/curve25519-dalek, with these changes:
- removed all crates besides `curve25519-dalek`
- removed all backends except for `serial/u64`
- commented out unit tests
- removed most CI workflows

It contains Verus proofs for a selection of functions. See these links for more information: 
- General overview: https://beneficial-ai-foundation.github.io/dalek-lite/index.html
- Proved function specifications: https://beneficial-ai-foundation.github.io/dalek-lite/specs.html

