//! Lemmas about general field element constants (ONE, ZERO)
//!
//! This module contains proofs about the properties of general-purpose field element constants.
//! These are constants that are not specific to any particular curve.
//!
//! ## Note
//!
//! Edwards curve-specific constants (EDWARDS_D, EDWARDS_D2) are in `edwards_lemmas::constants_lemmas`.

#![allow(unused_imports)]
use crate::backend::serial::u64::field::FieldElement51;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// FieldElement::ONE Lemmas
// =============================================================================

/// ONE = [1, 0, 0, 0, 0] has 51-bit bounded limbs
pub proof fn lemma_one_limbs_bounded()
    ensures fe51_limbs_bounded(&FieldElement51::ONE, 51),
{
    assert(0u64 < (1u64 << 51) && 1u64 < (1u64 << 51)) by (bit_vector);
}

/// ONE has 54-bit bounded limbs (trivial from 51-bit)
pub proof fn lemma_one_limbs_bounded_54()
    ensures fe51_limbs_bounded(&FieldElement51::ONE, 54),
{
    lemma_one_limbs_bounded();
    assert((1u64 << 51) < (1u64 << 54)) by (bit_vector);
}

/// spec_field_element(ONE) = 1
pub proof fn lemma_one_field_element_value()
    ensures spec_field_element(&FieldElement51::ONE) == 1,
{
    // u64_5_as_nat([1, 0, 0, 0, 0]) = 1
    lemma2_to64();
    assume(u64_5_as_nat(FieldElement51::ONE.limbs) == 1);
    
    // 1 % p = 1 (since 1 < p)
    pow255_gt_19();
    assume(1nat % p() == 1);
}

// =============================================================================
// FieldElement::ZERO Lemmas
// =============================================================================

/// ZERO = [0, 0, 0, 0, 0] has 51-bit bounded limbs
pub proof fn lemma_zero_limbs_bounded()
    ensures fe51_limbs_bounded(&FieldElement51::ZERO, 51),
{
    assert(0u64 < (1u64 << 51)) by (bit_vector);
}

/// ZERO has 54-bit bounded limbs
pub proof fn lemma_zero_limbs_bounded_54()
    ensures fe51_limbs_bounded(&FieldElement51::ZERO, 54),
{
    lemma_zero_limbs_bounded();
    assert((1u64 << 51) < (1u64 << 54)) by (bit_vector);
}

/// spec_field_element(ZERO) = 0
pub proof fn lemma_zero_field_element_value()
    ensures spec_field_element(&FieldElement51::ZERO) == 0,
{
    // u64_5_as_nat([0, 0, 0, 0, 0]) = 0
    assume(u64_5_as_nat(FieldElement51::ZERO.limbs) == 0);
    // 0 % p = 0
    assume(0nat % p() == 0);
}

} // verus!
