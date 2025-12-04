//! Lemmas for Edwards curve operations
//!
//! This module contains proofs for operations on Ed25519 twisted Edwards curve points.
//!
//! ## Submodules
//!
//! - `constants_lemmas`: Lemmas about Edwards curve constants (EDWARDS_D, EDWARDS_D2)
//! - `decompress_lemmas`: Lemmas for point decompression
//!
//! ## Moved
//!
//! - `sqrt_ratio_lemmas` → `common_lemmas/sqrt_ratio_lemmas.rs`
//!   (sqrt_ratio_i is field-level, not Edwards-specific)

pub mod constants_lemmas;
pub mod decompress_lemmas;

