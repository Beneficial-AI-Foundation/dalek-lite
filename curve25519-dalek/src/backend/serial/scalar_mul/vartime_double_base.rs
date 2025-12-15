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
// VERIFICATION NOTE: PROOF BYPASS - assumes used for intermediate preconditions
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

    /* <ORIGINAL CODE>
    loop {
        let mut t = r.double();

        match a_naf[i].cmp(&0) {
            Ordering::Greater => t = &t.as_extended() + &table_A.select(a_naf[i] as usize),
            Ordering::Less => t = &t.as_extended() - &table_A.select(-a_naf[i] as usize),
            Ordering::Equal => {}
        }

        match b_naf[i].cmp(&0) {
            Ordering::Greater => t = &t.as_extended() + &table_B.select(b_naf[i] as usize),
            Ordering::Less => t = &t.as_extended() - &table_B.select(-b_naf[i] as usize),
            Ordering::Equal => {}
        }

        r = t.as_projective();

        if i == 0 {
            break;
        }
        i -= 1;
    }
    </ORIGINAL CODE> */
    // VERIFICATION NOTE: Refactored loop to while with explicit decreases clause.
    // Also refactored -a_naf[i] to avoid i8 negation overflow.
    while i > 0
        invariant
            i <= 255,
        decreases i,
    {
        let mut t = r.double();

        match a_naf[i].cmp(&0) {
            Ordering::Greater => t = &t.as_extended() + &table_A.select(a_naf[i] as usize),
            Ordering::Less => {
                let idx = (-(a_naf[i] as i16)) as usize;
                t = &t.as_extended() - &table_A.select(idx)
            }
            Ordering::Equal => {}
        }

        match b_naf[i].cmp(&0) {
            Ordering::Greater => t = &t.as_extended() + &table_B.select(b_naf[i] as usize),
            Ordering::Less => {
                let idx = (-(b_naf[i] as i16)) as usize;
                t = &t.as_extended() - &table_B.select(idx)
            }
            Ordering::Equal => {}
        }

        r = t.as_projective();
        i -= 1;
    }

    // Handle final iteration at i = 0 (original loop always executes at least once)
    let mut t = r.double();

    match a_naf[0].cmp(&0) {
        Ordering::Greater => t = &t.as_extended() + &table_A.select(a_naf[0] as usize),
        Ordering::Less => {
            let idx = (-(a_naf[0] as i16)) as usize;
            t = &t.as_extended() - &table_A.select(idx)
        }
        Ordering::Equal => {}
    }

    match b_naf[0].cmp(&0) {
        Ordering::Greater => t = &t.as_extended() + &table_B.select(b_naf[0] as usize),
        Ordering::Less => {
            let idx = (-(b_naf[0] as i16)) as usize;
            t = &t.as_extended() - &table_B.select(idx)
        }
        Ordering::Equal => {}
    }

    r = t.as_projective();

    r.as_extended()
}

} // verus!
