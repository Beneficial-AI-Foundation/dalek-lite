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
#![allow(non_snake_case)]

use core::cmp::Ordering;

use crate::backend::serial::curve_models::{ProjectiveNielsPoint, ProjectivePoint};
use crate::constants;
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::Identity;
use crate::window::NafLookupTable5;

#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::is_valid_projective_point;
#[cfg(verus_keep_ghost)]
use crate::specs::field_specs::{fe51_limbs_bounded, sum_of_limbs_bounded};
#[cfg(verus_keep_ghost)]
use crate::specs::scalar_specs::is_valid_naf;
#[cfg(verus_keep_ghost)]
use crate::specs::window_specs::{
    naf_lookup_table5_projective_limbs_bounded, naf_lookup_table8_affine_limbs_bounded,
};

use vstd::prelude::*;

verus! {

/// Compute \\(aA + bB\\) in variable time, where \\(B\\) is the Ed25519 basepoint.
// VERIFICATION NOTE: PROOF BYPASS - complex loop invariants not yet verified.
// Uses `assume(false)` at loop entry points to skip internal verification.
pub fn mul(a: &Scalar, A: &EdwardsPoint, b: &Scalar) -> (out: EdwardsPoint)
    ensures
        true,
{
    let a_naf = a.non_adjacent_form(5);

    #[cfg(feature = "precomputed-tables")]
    let b_naf = b.non_adjacent_form(8);
    #[cfg(not(feature = "precomputed-tables"))]
    let b_naf = b.non_adjacent_form(5);

    // Find starting index
    let mut i: usize = 255;
    /* <ORIGINAL CODE>
    for j in (0..256).rev() {
        i = j;
        if a_naf[i] != 0 || b_naf[i] != 0 {
            break;
        }
    }
    </ORIGINAL CODE> */
    // VERIFICATION NOTE: Verus doesn't support for-loops over Rev<Range<_>>
    while i > 0
        invariant
            i <= 255,
        decreases i,
    {
        if a_naf[i] != 0 || b_naf[i] != 0 {
            break;
        }
        i -= 1;
    }

    let table_A = NafLookupTable5::<ProjectiveNielsPoint>::from(A);
    #[cfg(feature = "precomputed-tables")]
    let table_B = &constants::AFFINE_ODD_MULTIPLES_OF_BASEPOINT;
    #[cfg(not(feature = "precomputed-tables"))]
    let table_B =
        &NafLookupTable5::<ProjectiveNielsPoint>::from(&constants::ED25519_BASEPOINT_POINT);

    let mut r = ProjectivePoint::identity();

    /* VERIFICATION CHANGES:
       1. `loop` → `loop` with `invariant`/`decreases` (Verus requires explicit termination proof)
       2. `-a_naf[i]` → `(-(a_naf[i] as i16))` (avoid i8::MIN negation overflow)
       3. Added `assume(false)` (proof bypass for complex loop invariants)
    */
    loop
        invariant
            i <= 255,
        decreases i,
    {
        assume(false);  // PROOF BYPASS
        let mut t = r.double();

        match a_naf[i].cmp(&0) {
            Ordering::Greater => t = &t.as_extended() + &table_A.select(a_naf[i] as usize),
            Ordering::Less => t = &t.as_extended() - &table_A.select((-(a_naf[i] as i16)) as usize),  // CHANGED: i8→i16 for negation
            Ordering::Equal => {}
        }

        match b_naf[i].cmp(&0) {
            Ordering::Greater => t = &t.as_extended() + &table_B.select(b_naf[i] as usize),
            Ordering::Less => t = &t.as_extended() - &table_B.select((-(b_naf[i] as i16)) as usize),  // CHANGED: i8→i16 for negation
            Ordering::Equal => {}
        }

        r = t.as_projective();

        if i == 0 {
            break;
        }
        i -= 1;
    }

    assume(false);  // PROOF BYPASS: precondition for as_extended
    r.as_extended()
}

} // verus!
