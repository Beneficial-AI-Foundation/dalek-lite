//! General lemmas about the Edwards curve
//!
//! This module contains general facts about the Ed25519 curve that are not specific
//! to any particular operation (like decompression or point addition).

#![allow(unused_imports)]
use crate::backend::serial::u64::constants::EDWARDS_D;
use crate::backend::serial::u64::field::FieldElement51;
use crate::specs::edwards_specs::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::prelude::*;

verus! {

/// Lemma: The identity point (0, 1) is on the Edwards curve
///
/// This is a fundamental property of the Ed25519 curve.
/// The identity element of the group is the point (0, 1).
pub proof fn lemma_identity_on_curve()
    ensures
        math_on_edwards_curve(0, 1),
{
    let d = spec_field_element(&EDWARDS_D);

    // LHS: -0² + 1² = 1 (mod p)
    // RHS: 1 + d·0²·1² = 1 (mod p)
    // LHS == RHS ✓

    assert(math_field_square(0) == 0);
    assert(math_field_square(1) == 1);
    assert(math_field_sub(1, 0) == 1);
    assert(math_field_mul(d, 0) == 0);
    assert(math_field_add(1, 0) == 1);
}

/// Lemma: y = 1 is always a valid y-coordinate (gives the identity point x = 0)
///
/// When y = 1, we have u = y² - 1 = 0, so x² = 0/v = 0, giving x = 0.
pub proof fn lemma_y_one_is_valid()
    ensures
        math_is_valid_y_coordinate(1),
{
    let d = spec_field_element(&EDWARDS_D);
    let y2 = math_field_square(1);  // 1
    let u = math_field_sub(y2, 1);  // 0
    let v = math_field_add(math_field_mul(d, y2), 1);  // d + 1

    // u = 0, which is the first case in math_is_valid_y_coordinate
    assert(u % p() == 0);
    // Therefore math_is_valid_y_coordinate(1) is true
}

} // verus!

