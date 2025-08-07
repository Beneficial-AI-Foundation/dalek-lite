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

#[cfg(feature = "verus")]
use vstd::prelude::*;

#[cfg(feature = "verus")]
verus! {
    /// NAF property specifications for mixed-width NAF in double-base scalar multiplication
    /// Supports both width-5 and width-8 NAF representations depending on precomputed tables
    
    spec fn naf_mixed_width_digit_valid(digit: i8, width: usize) -> bool {
        match width {
            5 => -15 <= digit && digit <= 15 && (digit % 2 != 0 || digit == 0),
            8 => -127 <= digit && digit <= 127 && (digit % 2 != 0 || digit == 0),
            _ => false, // Only width-5 and width-8 are supported
        }
    }
    
    spec fn naf_double_base_properties(a_naf: &[i8], b_naf: &[i8], b_width: usize) -> bool {
        // Both NAF representations have exactly 256 coefficients
        a_naf.len() == 256 && b_naf.len() == 256 &&
        // a_naf uses width-5 NAF for variable point A
        forall|i: int| 0 <= i < 256 ==> naf_mixed_width_digit_valid(a_naf[i], 5) &&
        // b_naf uses either width-5 or width-8 depending on precomputed tables
        forall|i: int| 0 <= i < 256 ==> naf_mixed_width_digit_valid(b_naf[i], b_width) &&
        // Non-adjacent property for both representations
        naf_non_adjacent_property_mixed(a_naf) &&
        naf_non_adjacent_property_mixed(b_naf)
    }
    
    spec fn naf_non_adjacent_property_mixed(naf: &[i8]) -> bool {
        // Non-adjacent form property: no two adjacent non-zero digits
        forall|i: int| 0 <= i < naf.len() - 1 ==> 
            (naf[i] != 0 ==> naf[i + 1] == 0)
    }
    
    spec fn naf_table_compatibility_mixed(digit: i8, width: usize) -> bool {
        // Table select compatibility for both NafLookupTable5 and basepoint tables
        if digit > 0 {
            match width {
                5 => digit <= 15 && digit % 2 == 1 && (digit as usize) < 16,
                8 => digit <= 127 && digit % 2 == 1 && (digit as usize) < 128,
                _ => false,
            }
        } else if digit < 0 {
            match width {
                5 => digit >= -15 && (-digit) % 2 == 1 && ((-digit) as usize) < 16,
                8 => digit >= -127 && (-digit) % 2 == 1 && ((-digit) as usize) < 128,
                _ => false,
            }
        } else {
            true // digit == 0, no table access
        }
    }
}

/// Compute \\(aA + bB\\) in variable time, where \\(B\\) is the Ed25519 basepoint.
/// 
/// # Preconditions (for verification)
/// - For double-base scalar multiplication with NAF representation:
///   - Each scalar.non_adjacent_form(w) returns exactly 256 i8 values
///   - For width-5 NAF: digits are signed, odd, and in range [-15, 15]
///   - For width-8 NAF: digits are signed, odd, and in range [-127, 127] 
///   - NAF arrays accessed at indices [0..255] during iteration from 255 down to 0
///   - Both a_naf[i] and b_naf[i] array accesses are safe for synchronized processing
///   - Table select operations require odd positive arguments within NAF width bounds
pub fn mul(a: &Scalar, A: &EdwardsPoint, b: &Scalar) -> EdwardsPoint {
    let a_naf = a.non_adjacent_form(5);

    #[cfg(feature = "precomputed-tables")]
    let b_naf = b.non_adjacent_form(8);
    #[cfg(not(feature = "precomputed-tables"))]
    let b_naf = b.non_adjacent_form(5);
    
    #[cfg(feature = "verus")]
    {
        #[cfg(feature = "precomputed-tables")]
        assume(naf_double_base_properties(&a_naf, &b_naf, 8));
        
        #[cfg(not(feature = "precomputed-tables"))]
        assume(naf_double_base_properties(&a_naf, &b_naf, 5));
    }

    // Find starting index
    let mut i: usize = 255;
    for j in (0..256).rev() {
        #[cfg(feature = "verus")]
        assert([
            j < 256,  // Loop index bounds for safe NAF array access
            a_naf.len() == 256,  // a_naf array size consistency
            b_naf.len() == 256,  // b_naf array size consistency
            j < a_naf.len(),  // Safe a_naf[j] access when assigning to i
            j < b_naf.len(),  // Safe b_naf[j] access when assigning to i
        ]);
        
        i = j;
        if a_naf[i] != 0 || b_naf[i] != 0 {
            break;
        }
    }

    let table_A = NafLookupTable5::<ProjectiveNielsPoint>::from(A);
    #[cfg(feature = "precomputed-tables")]
    let table_B = &constants::AFFINE_ODD_MULTIPLES_OF_BASEPOINT;
    #[cfg(not(feature = "precomputed-tables"))]
    let table_B =
        &NafLookupTable5::<ProjectiveNielsPoint>::from(&constants::ED25519_BASEPOINT_POINT);

    let mut r = ProjectivePoint::identity();
    loop {
        #[cfg(feature = "verus")]
        assert([
            i < 256,  // Loop index bounds for safe NAF array access
            a_naf.len() == 256,  // a_naf array size consistency
            b_naf.len() == 256,  // b_naf array size consistency
            i < a_naf.len(),  // Safe a_naf[i] access
            i < b_naf.len(),  // Safe b_naf[i] access
            // NAF property verification for current digits
            naf_mixed_width_digit_valid(a_naf[i], 5),
            naf_table_compatibility_mixed(a_naf[i], 5),
            #[cfg(feature = "precomputed-tables")]
            naf_mixed_width_digit_valid(b_naf[i], 8),
            #[cfg(not(feature = "precomputed-tables"))]
            naf_mixed_width_digit_valid(b_naf[i], 5),
            #[cfg(feature = "precomputed-tables")]
            naf_table_compatibility_mixed(b_naf[i], 8),
            #[cfg(not(feature = "precomputed-tables"))]
            naf_table_compatibility_mixed(b_naf[i], 5),
        ]);
        
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

    r.as_extended()
}
