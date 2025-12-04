//! Lemmas about Edwards curve constants (EDWARDS_D, EDWARDS_D2)
//!
//! This module contains proofs about the properties of Edwards curve constants.
//! These are the curve parameters `d` and `2d` used in the twisted Edwards curve equation.

#![allow(unused_imports)]
use crate::backend::serial::u64::constants::{EDWARDS_D, EDWARDS_D2};
use crate::backend::serial::u64::field::FieldElement51;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// EDWARDS_D Lemmas
// =============================================================================

/// EDWARDS_D has 51-bit bounded limbs
pub(crate) proof fn lemma_edwards_d_limbs_bounded()
    ensures fe51_limbs_bounded(&EDWARDS_D, 51),
{
    // All EDWARDS_D limbs < 2^51
    assert(929955233495203u64 < (1u64 << 51)) by (bit_vector);
    assert(466365720129213u64 < (1u64 << 51)) by (bit_vector);
    assert(1662059464998953u64 < (1u64 << 51)) by (bit_vector);
    assert(2033849074728123u64 < (1u64 << 51)) by (bit_vector);
    assert(1442794654840575u64 < (1u64 << 51)) by (bit_vector);
}

/// EDWARDS_D has 54-bit bounded limbs
pub(crate) proof fn lemma_edwards_d_limbs_bounded_54()
    ensures fe51_limbs_bounded(&EDWARDS_D, 54),
{
    lemma_edwards_d_limbs_bounded();
    assert((1u64 << 51) < (1u64 << 54)) by (bit_vector);
}

// =============================================================================
// EDWARDS_D2 Lemmas (2*d)
// =============================================================================

/// EDWARDS_D2 (= 2·d) has 51-bit bounded limbs
pub(crate) proof fn lemma_edwards_d2_limbs_bounded()
    ensures fe51_limbs_bounded(&EDWARDS_D2, 51),
{
    // All EDWARDS_D2 limbs < 2^51
    assert(1859910466990425u64 < (1u64 << 51)) by (bit_vector);
    assert(932731440258426u64 < (1u64 << 51)) by (bit_vector);
    assert(1072319116312658u64 < (1u64 << 51)) by (bit_vector);
    assert(1815898335770999u64 < (1u64 << 51)) by (bit_vector);
    assert(633789495995903u64 < (1u64 << 51)) by (bit_vector);
}

/// EDWARDS_D2 has 54-bit bounded limbs
pub(crate) proof fn lemma_edwards_d2_limbs_bounded_54()
    ensures fe51_limbs_bounded(&EDWARDS_D2, 54),
{
    lemma_edwards_d2_limbs_bounded();
    assert((1u64 << 51) < (1u64 << 54)) by (bit_vector);
}

} // verus!

