//! The Lizard method for encoding/decoding 16 bytes into Ristretto points.
//!
//! Lizard is a *reversible encoding* (not a hash-to-curve) that embeds 16 bytes
//! into a Ristretto point. Decoding succeeds only for points that were produced
//! by the encoding procedure (and returns `None` otherwise / if ambiguous).
//!
//! The executable API is exposed as methods on `RistrettoPoint`:
//! - `RistrettoPoint::lizard_encode::<D>(data: &[u8; 16]) -> RistrettoPoint`
//! - `RistrettoPoint::lizard_decode::<D>(&self) -> Option<[u8; 16]>`
//!
//! For Verus specifications (reference mathematical intent), see
//! `crate::specs::lizard_specs`.
#![allow(non_snake_case)]

#[cfg(curve25519_dalek_bits = "32")]
mod u32_constants;

#[cfg(curve25519_dalek_bits = "64")]
mod u64_constants;

pub mod jacobi_quartic;
pub mod lizard_constants;
pub mod lizard_ristretto;
