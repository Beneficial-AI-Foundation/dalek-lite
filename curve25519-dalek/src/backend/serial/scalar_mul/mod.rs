// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2021 isis lovecruft
// Copyright (c) 2016-2019 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Implementations of various scalar multiplication algorithms.
//!
//! Note that all of these implementations use serial code for field
//! arithmetic with the multi-model strategy described in the
//! `curve_models` module.  The vectorized AVX2 backend has its own
//! scalar multiplication implementations, since it only uses one
//! curve model.

#[allow(missing_docs)]
pub mod variable_base;

#[allow(missing_docs)]
pub mod vartime_double_base;

#[cfg(feature = "alloc")]
pub mod straus;

#[cfg(feature = "alloc")]
pub mod precomputed_straus;

#[cfg(feature = "alloc")]
pub mod pippenger;

// PHASE 2: Complete algorithmic correctness framework
#[cfg(feature = "verus")]
pub mod phase2_unified_correctness;

// PHASE 3: EdDSA signature verification protocol correctness
#[cfg(feature = "verus")]
pub mod phase3_signature_verification_correctness;

#[cfg(feature = "verus")]
pub mod phase3_eddsa_verification_implementation;

// PHASE 3: EdDSA key generation mathematical correctness
#[cfg(feature = "verus")]
pub mod phase3_key_generation_correctness;

// PHASE 3: EdDSA protocol composition correctness
#[cfg(feature = "verus")]
pub mod phase3_protocol_composition_correctness;
