//! Lemmas about the scalar group order constant L
//!
//! This module contains fully proved lemmas about the Scalar52::L constant,
//! which represents the group order of the Ristretto/Ed25519 group.
//!
//! ## Mathematical Background
//!
//! Scalar elements in the 52-bit limb representation have the form:
//! ```text
//! value = limbs[0] + 2^52·limbs[1] + 2^104·limbs[2] + 2^156·limbs[3] + 2^208·limbs[4]
//! ```
//!
//! L = 2^252 + 27742317777372353535851937790883648493
//!   = [0x0002631a5cf5d3ed, 0x000dea2f79cd6581, 0x000000000014def9, 0, 0x0000100000000000]
//!
//! ## Note
//!
//! - Montgomery reduction lemmas are in `montgomery_reduce_lemmas.rs`.
#![allow(unused_imports)]
use crate::backend::serial::u64::constants;
use vstd::prelude::*;

verus! {

// =============================================================================
// L Limbs Bounds Lemmas
// =============================================================================
/// Proves concrete bounds on each limb of the group order constant L.
/// These bounds are essential for tracking overflow in Montgomery reduction.
///
/// L = 2^252 + 27742317777372353535851937790883648493
/// L.limbs = [0x0002631a5cf5d3ed, 0x000dea2f79cd6581, 0x000000000014def9, 0, 0x0000100000000000]
pub(crate) proof fn lemma_l_limbs_bounds()
    ensures
        constants::L.limbs[0] < 0x4000000000000,  // < 2^50
        constants::L.limbs[1] < 0x10000000000000,  // < 2^52
        constants::L.limbs[2] < 0x200000,  // < 2^21
        constants::L.limbs[3] == 0,
        constants::L.limbs[4] == 0x100000000000,  // == 2^44
        // All limbs < 2^52
        constants::L.limbs[0] < 0x10000000000000,
        constants::L.limbs[2] < 0x10000000000000,
        constants::L.limbs[4] < 0x10000000000000,
{
    // Step 1: Establish the concrete limb values
    assert(constants::L.limbs[0] == 0x0002631a5cf5d3ed_u64);
    assert(constants::L.limbs[1] == 0x000dea2f79cd6581_u64);
    assert(constants::L.limbs[2] == 0x000000000014def9_u64);
    assert(constants::L.limbs[3] == 0x0000000000000000_u64);
    assert(constants::L.limbs[4] == 0x0000100000000000_u64);

    // Step 2: Prove tight bounds on each limb via bit_vector
    assert(0x0002631a5cf5d3ed_u64 < 0x4000000000000u64) by (bit_vector);  // L[0] < 2^50
    assert(0x000dea2f79cd6581_u64 < 0x10000000000000u64) by (bit_vector);  // L[1] < 2^52
    assert(0x000000000014def9_u64 < 0x200000u64) by (bit_vector);  // L[2] < 2^21
    assert(0x0000100000000000_u64 == 0x100000000000u64) by (bit_vector);  // L[4] == 2^44

    // Step 3: Prove all non-zero limbs < 2^52 (for overflow checking)
    assert(0x0002631a5cf5d3ed_u64 < 0x10000000000000u64) by (bit_vector);
    assert(0x000000000014def9_u64 < 0x10000000000000u64) by (bit_vector);
    assert(0x0000100000000000_u64 < 0x10000000000000u64) by (bit_vector);
}

} // verus!
