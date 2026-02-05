//! Lemmas about Montgomery curve constants used in the Elligator map.
//!
//! This module provides small, fully proved facts about the field-element
//! constant `MONTGOMERY_A` from `backend::serial::u64::constants`.
#![allow(unused_imports)]
use crate::backend::serial::u64::constants::MONTGOMERY_A;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::prelude::*;

verus! {

/// `MONTGOMERY_A` has 51-bit bounded limbs.
pub proof fn lemma_montgomery_a_limbs_bounded_51()
    ensures
        fe51_limbs_bounded(&MONTGOMERY_A, 51),
{
    assert(fe51_limbs_bounded(&MONTGOMERY_A, 51)) by {
        assert(0u64 < (1u64 << 51) && 486662u64 < (1u64 << 51)) by (bit_vector);
    };
}

} // verus!
