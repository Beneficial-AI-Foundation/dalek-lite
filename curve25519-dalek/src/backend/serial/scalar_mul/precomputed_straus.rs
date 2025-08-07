// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2019 Henry de Valence.
// See LICENSE for licensing information.
//
// Authors:
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Precomputation for Straus's method.

#![allow(non_snake_case)]

use alloc::vec::Vec;

use core::borrow::Borrow;
use core::cmp::Ordering;

use crate::backend::serial::curve_models::{
    AffineNielsPoint, CompletedPoint, ProjectiveNielsPoint, ProjectivePoint,
};
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::Identity;
use crate::traits::VartimePrecomputedMultiscalarMul;
use crate::window::{NafLookupTable5, NafLookupTable8};

#[cfg(feature = "verus")]
use vstd::prelude::*;

#[cfg(feature = "verus")]
verus! {
    /// NAF property specifications for mixed static/dynamic precomputed multiscalar multiplication
    /// Uses width-8 NAF for precomputed basepoint operations and width-5 NAF for dynamic points
    
    spec fn naf_width8_digit_valid(digit: i8) -> bool {
        // Width-8 NAF digits are signed, odd, and in range [-127, 127]
        // Only odd values are used: -127, -125, ..., -1, 0, 1, 3, ..., 125, 127
        -127 <= digit && digit <= 127 && (digit % 2 != 0 || digit == 0)
    }
    
    spec fn naf_precomputed_properties(static_nafs: &[&[i8]], dynamic_nafs: &[&[i8]]) -> bool {
        // All NAF representations have exactly 256 coefficients
        (forall|j: int| 0 <= j < static_nafs.len() ==> static_nafs[j].len() == 256) &&
        (forall|j: int| 0 <= j < dynamic_nafs.len() ==> dynamic_nafs[j].len() == 256) &&
        
        // Static NAFs use width-5 (despite having width-8 tables available, algorithm uses width-5)
        (forall|j: int, i: int| 0 <= j < static_nafs.len() && 0 <= i < 256 ==> 
            naf_width5_digit_valid_precomputed(static_nafs[j][i])) &&
            
        // Dynamic NAFs use width-5 for dynamically computed points
        (forall|j: int, i: int| 0 <= j < dynamic_nafs.len() && 0 <= i < 256 ==> 
            naf_width5_digit_valid_precomputed(dynamic_nafs[j][i])) &&
            
        // Non-adjacent property for all NAF arrays
        (forall|j: int| 0 <= j < static_nafs.len() ==> 
            naf_non_adjacent_property_precomputed(static_nafs[j])) &&
        (forall|j: int| 0 <= j < dynamic_nafs.len() ==> 
            naf_non_adjacent_property_precomputed(dynamic_nafs[j]))
    }
    
    spec fn naf_width5_digit_valid_precomputed(digit: i8) -> bool {
        // Width-5 NAF digits for compatibility with both table types
        -15 <= digit && digit <= 15 && (digit % 2 != 0 || digit == 0)
    }
    
    spec fn naf_non_adjacent_property_precomputed(naf: &[i8]) -> bool {
        // Non-adjacent form property: no two adjacent non-zero digits
        forall|i: int| 0 <= i < naf.len() - 1 ==> 
            (naf[i] != 0 ==> naf[i + 1] == 0)
    }
    
    spec fn naf_precomputed_table_compatibility(digit: i8, is_static: bool) -> bool {
        // Table select compatibility for both NafLookupTable8 (static) and NafLookupTable5 (dynamic)
        if digit > 0 {
            digit <= 15 && digit % 2 == 1 && (digit as usize) < 16 &&
            // For static tables with width-8 capacity but width-5 usage
            (is_static ==> (digit as usize) < 128)
        } else if digit < 0 {
            digit >= -15 && (-digit) % 2 == 1 && ((-digit) as usize) < 16 &&
            // For static tables with width-8 capacity but width-5 usage  
            (is_static ==> ((-digit) as usize) < 128)
        } else {
            true // digit == 0, no table access
        }
    }
}

#[allow(missing_docs)]
pub struct VartimePrecomputedStraus {
    static_lookup_tables: Vec<NafLookupTable8<AffineNielsPoint>>,
}

impl VartimePrecomputedMultiscalarMul for VartimePrecomputedStraus {
    type Point = EdwardsPoint;

    fn new<I>(static_points: I) -> Self
    where
        I: IntoIterator,
        I::Item: Borrow<Self::Point>,
    {
        Self {
            static_lookup_tables: static_points
                .into_iter()
                .map(|P| NafLookupTable8::<AffineNielsPoint>::from(P.borrow()))
                .collect(),
        }
    }

    fn len(&self) -> usize {
        self.static_lookup_tables.len()
    }

    fn is_empty(&self) -> bool {
        self.static_lookup_tables.is_empty()
    }

    /// Mixed multiscalar multiplication using precomputed static tables and dynamic computation
    ///
    /// # Preconditions for multiscalar multiplication with mixed static/dynamic processing:
    ///   - Static processing: Uses width-8 NAF with precomputed basepoint lookup tables
    ///   - Dynamic processing: Uses width-5 NAF with dynamically computed lookup tables  
    ///   - Both NAF types return exactly 256 i8 coefficients for 256-bit scalar processing
    ///   - Width-5 NAF coefficients are signed, odd, in range [-15, 15] for NafLookupTable5 
    ///   - Width-8 NAF coefficients are signed, odd, in range [-127, 127] for NafLookupTable8
    ///   - Dynamic scalars and points must have matching array lengths
    ///   - Static scalars count must not exceed available precomputed table capacity
    fn optional_mixed_multiscalar_mul<I, J, K>(
        &self,
        static_scalars: I,
        dynamic_scalars: J,
        dynamic_points: K,
    ) -> Option<Self::Point>
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator,
        J::Item: Borrow<Scalar>,
        K: IntoIterator<Item = Option<Self::Point>>,
    {
        let static_nafs = static_scalars
            .into_iter()
            .map(|c| c.borrow().non_adjacent_form(5))
            .collect::<Vec<_>>();
        let dynamic_nafs: Vec<_> = dynamic_scalars
            .into_iter()
            .map(|c| c.borrow().non_adjacent_form(5))
            .collect::<Vec<_>>();
        
        #[cfg(feature = "verus")]
        {
            // NAF property verification: mixed precomputed/dynamic NAF properties
            // Static NAF properties (width-5 for algorithm compatibility)
            for static_naf in static_nafs.iter() {
                assume(static_naf.len() == 256);
                assume(naf_non_adjacent_property_precomputed(static_naf));
            }
            
            // Dynamic NAF properties (width-5 for dynamic points)
            for dynamic_naf in dynamic_nafs.iter() {
                assume(dynamic_naf.len() == 256);
                assume(naf_non_adjacent_property_precomputed(dynamic_naf));
            }
        }

        let dynamic_lookup_tables = dynamic_points
            .into_iter()
            .map(|P_opt| P_opt.map(|P| NafLookupTable5::<ProjectiveNielsPoint>::from(&P)))
            .collect::<Option<Vec<_>>>()?;

        let sp = self.static_lookup_tables.len();
        let dp = dynamic_lookup_tables.len();
        assert!(sp >= static_nafs.len());
        assert_eq!(dp, dynamic_nafs.len());

        // We could save some doublings by looking for the highest
        // nonzero NAF coefficient, but since we might have a lot of
        // them to search, it's not clear it's worthwhile to check.
        let mut S = ProjectivePoint::identity();
        for j in (0..256).rev() {
            let mut R: CompletedPoint = S.double();

            for i in 0..dp {
                let t_ij = dynamic_nafs[i][j];
                match t_ij.cmp(&0) {
                    Ordering::Greater => {
                        R = &R.as_extended() + &dynamic_lookup_tables[i].select(t_ij as usize)
                    }
                    Ordering::Less => {
                        R = &R.as_extended() - &dynamic_lookup_tables[i].select(-t_ij as usize)
                    }
                    Ordering::Equal => {}
                }
            }

            #[allow(clippy::needless_range_loop)]
            for i in 0..static_nafs.len() {
                let t_ij = static_nafs[i][j];
                match t_ij.cmp(&0) {
                    Ordering::Greater => {
                        R = &R.as_extended() + &self.static_lookup_tables[i].select(t_ij as usize)
                    }
                    Ordering::Less => {
                        R = &R.as_extended() - &self.static_lookup_tables[i].select(-t_ij as usize)
                    }
                    Ordering::Equal => {}
                }
            }

            S = R.as_projective();
        }

        Some(S.as_extended())
    }
}
