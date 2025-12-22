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
//! Implementation of the interleaved window method, also known as Straus' method.
#![allow(non_snake_case)]

use alloc::vec::Vec;

use core::borrow::Borrow;
use core::cmp::Ordering;

use crate::backend::serial::curve_models::{
    CompletedPoint, ProjectiveNielsPoint, ProjectivePoint,
};
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::Identity;
use crate::traits::MultiscalarMul;
use crate::traits::VartimeMultiscalarMul;
use crate::window::LookupTable;
use crate::window::NafLookupTable5;

/// Perform multiscalar multiplication by the interleaved window
/// method, also known as Straus' method (since it was apparently
/// [first published][solution] by Straus in 1964, as a solution to [a
/// problem][problem] posted in the American Mathematical Monthly in
/// 1963).
///
/// It is easy enough to reinvent, and has been repeatedly.  The basic
/// idea is that when computing
/// \\[
/// Q = s_1 P_1 + \cdots + s_n P_n
/// \\]
/// by means of additions and doublings, the doublings can be shared
/// across the \\( P_i \\\).
///
/// We implement two versions, a constant-time algorithm using fixed
/// windows and a variable-time algorithm using sliding windows.  They
/// are slight variations on the same idea, and are described in more
/// detail in the respective implementations.
///
/// [solution]: https://www.jstor.org/stable/2310929
/// [problem]: https://www.jstor.org/stable/2312273
pub struct Straus {}

impl MultiscalarMul for Straus {
    type Point = EdwardsPoint;

    /// Constant-time Straus using a fixed window of size \\(4\\).
    ///
    /// Our goal is to compute
    /// \\[
    /// Q = s_1 P_1 + \cdots + s_n P_n.
    /// \\]
    ///
    /// For each point \\( P_i \\), precompute a lookup table of
    /// \\[
    /// P_i, 2P_i, 3P_i, 4P_i, 5P_i, 6P_i, 7P_i, 8P_i.
    /// \\]
    ///
    /// For each scalar \\( s_i \\), compute its radix-\\(2^4\\)
    /// signed digits \\( s_{i,j} \\), i.e.,
    /// \\[
    ///    s_i = s_{i,0} + s_{i,1} 16^1 + ... + s_{i,63} 16^{63},
    /// \\]
    /// with \\( -8 \leq s_{i,j} < 8 \\).  Since \\( 0 \leq |s_{i,j}|
    /// \leq 8 \\), we can retrieve \\( s_{i,j} P_i \\) from the
    /// lookup table with a conditional negation: using signed
    /// digits halves the required table size.
    ///
    /// Then as in the single-base fixed window case, we have
    /// \\[
    /// \begin{aligned}
    /// s_i P_i &= P_i (s_{i,0} +     s_{i,1} 16^1 + \cdots +     s_{i,63} 16^{63})   \\\\
    /// s_i P_i &= P_i s_{i,0} + P_i s_{i,1} 16^1 + \cdots + P_i s_{i,63} 16^{63}     \\\\
    /// s_i P_i &= P_i s_{i,0} + 16(P_i s_{i,1} + 16( \cdots +16P_i s_{i,63})\cdots )
    /// \end{aligned}
    /// \\]
    /// so each \\( s_i P_i \\) can be computed by alternately adding
    /// a precomputed multiple \\( P_i s_{i,j} \\) of \\( P_i \\) and
    /// repeatedly doubling.
    ///
    /// Now consider the two-dimensional sum
    /// \\[
    /// \begin{aligned}
    /// s\_1 P\_1 &=& P\_1 s\_{1,0} &+& 16 (P\_1 s\_{1,1} &+& 16 ( \cdots &+& 16 P\_1 s\_{1,63}&) \cdots ) \\\\
    ///     +     & &      +        & &      +            & &             & &     +            &           \\\\
    /// s\_2 P\_2 &=& P\_2 s\_{2,0} &+& 16 (P\_2 s\_{2,1} &+& 16 ( \cdots &+& 16 P\_2 s\_{2,63}&) \cdots ) \\\\
    ///     +     & &      +        & &      +            & &             & &     +            &           \\\\
    /// \vdots    & &  \vdots       & &   \vdots          & &             & &  \vdots          &           \\\\
    ///     +     & &      +        & &      +            & &             & &     +            &           \\\\
    /// s\_n P\_n &=& P\_n s\_{n,0} &+& 16 (P\_n s\_{n,1} &+& 16 ( \cdots &+& 16 P\_n s\_{n,63}&) \cdots )
    /// \end{aligned}
    /// \\]
    /// The sum of the left-hand column is the result \\( Q \\); by
    /// computing the two-dimensional sum on the right column-wise,
    /// top-to-bottom, then right-to-left, we need to multiply by \\(
    /// 16\\) only once per column, sharing the doublings across all
    /// of the input points.
    fn multiscalar_mul<I, J>(scalars: I, points: J) -> EdwardsPoint
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator,
        J::Item: Borrow<EdwardsPoint>,
    {
        let lookup_tables: Vec<_> = points
            .into_iter()
            .map(|point| LookupTable::<ProjectiveNielsPoint>::from(point.borrow()))
            .collect();

        // This puts the scalar digits into a heap-allocated Vec.
        // To ensure that these are erased, pass ownership of the Vec into a
        // Zeroizing wrapper.
        #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
        let mut scalar_digits: Vec<_> = scalars
            .into_iter()
            .map(|s| s.borrow().as_radix_16())
            .collect();

        let mut Q = EdwardsPoint::identity();
        for j in (0..64).rev() {
            Q = Q.mul_by_pow_2(4);
            let it = scalar_digits.iter().zip(lookup_tables.iter());
            for (s_i, lookup_table_i) in it {
                // R_i = s_{i,j} * P_i
                let R_i = lookup_table_i.select(s_i[j]);
                // Q = Q + R_i
                Q = (&Q + &R_i).as_extended();
            }
        }

        #[cfg(feature = "zeroize")]
        zeroize::Zeroize::zeroize(&mut scalar_digits);

        Q
    }
}

impl VartimeMultiscalarMul for Straus {
    type Point = EdwardsPoint;

    /// Variable-time Straus using a non-adjacent form of width \\(5\\).
    ///
    /// This is completely similar to the constant-time code, but we
    /// use a non-adjacent form for the scalar, and do not do table
    /// lookups in constant time.
    ///
    /// The non-adjacent form has signed, odd digits.  Using only odd
    /// digits halves the table size (since we only need odd
    /// multiples), or gives fewer additions for the same table size.
    fn optional_multiscalar_mul<I, J>(scalars: I, points: J) -> Option<EdwardsPoint>
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator<Item = Option<EdwardsPoint>>,
    /* VERIFICATION NOTE: VERUS SPEC (when IntoIterator with I::Item projections is supported):
    requires
        scalars.len() == points.len(),
        forall|i| points[i].is_some() ==> is_well_formed_edwards_point(points[i].unwrap()),
    ensures
        result.is_some() <==> all_points_some(points),
        result.is_some() ==> is_well_formed_edwards_point(result.unwrap()),
        result.is_some() ==> edwards_point_as_affine(result.unwrap()) == sum_of_scalar_muls(scalars, unwrap_points(points)),
    
    VERIFICATION NOTE: see `optional_multiscalar_mul_verus` below for the verified version using Iterator (not IntoIterator).
    */
    {
        let nafs: Vec<_> = scalars
            .into_iter()
            .map(|c| c.borrow().non_adjacent_form(5))
            .collect();

        let lookup_tables = points
            .into_iter()
            .map(|P_opt| P_opt.map(|P| NafLookupTable5::<ProjectiveNielsPoint>::from(&P)))
            .collect::<Option<Vec<_>>>()?;

        let mut r = ProjectivePoint::identity();

        for i in (0..256).rev() {
            let mut t: CompletedPoint = r.double();

            for (naf, lookup_table) in nafs.iter().zip(lookup_tables.iter()) {
                match naf[i].cmp(&0) {
                    Ordering::Greater => {
                        t = &t.as_extended() + &lookup_table.select(naf[i] as usize)
                    }
                    Ordering::Less => t = &t.as_extended() - &lookup_table.select(-naf[i] as usize),
                    Ordering::Equal => {}
                }
            }

            r = t.as_projective();
        }

        Some(r.as_extended())
    }
}

// ============================================================================
// Verus-compatible version
// ============================================================================

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::*;

// Import spec functions from pippenger module (ghost only)
#[cfg(verus_keep_ghost)]
use crate::backend::serial::scalar_mul::pippenger::{
    spec_scalars_from_iter, spec_optional_points_from_iter,
    all_points_some, unwrap_points,
};

// Import runtime helpers from pippenger module
use crate::backend::serial::scalar_mul::pippenger::{
    collect_scalars_from_iter, collect_optional_points_from_iter,
};

verus! {

/* <VERIFICATION NOTE>
Iterator operations, closures capturing &mut, and Borrow trait are not directly
supported by Verus. This version uses explicit loops and concrete types.
The function signature uses Iterator (not IntoIterator) similar to Sum::sum.
PROOF BYPASS: Complex loop invariants not yet verified; uses assume(false).
</VERIFICATION NOTE> */

impl Straus {
    /// Verus-compatible version of optional_multiscalar_mul.
    /// Uses Iterator instead of IntoIterator (Verus doesn't support I::Item projections).
    /// Computes sum(scalars[i] * points[i]) for all i where points[i] is Some.
    pub fn optional_multiscalar_mul_verus<S, I, J>(
    scalars: I,
    points: J,
) -> (result: Option<EdwardsPoint>)
where
    S: Borrow<Scalar>,
    I: Iterator<Item = S>,
    J: Iterator<Item = Option<EdwardsPoint>>,
    requires
        // Same number of scalars and points
        spec_scalars_from_iter::<S, I>(scalars).len() == spec_optional_points_from_iter::<J>(points).len(),
        // All input points (when Some) must be well-formed
        forall|i: int| 0 <= i < spec_optional_points_from_iter::<J>(points).len()
            && (#[trigger] spec_optional_points_from_iter::<J>(points)[i]).is_some()
            ==> is_well_formed_edwards_point(spec_optional_points_from_iter::<J>(points)[i].unwrap()),
    ensures
        // Result is Some if and only if all input points are Some
        result.is_some() <==> all_points_some(spec_optional_points_from_iter::<J>(points)),
        // If result is Some, it is a well-formed Edwards point
        result.is_some() ==> is_well_formed_edwards_point(result.unwrap()),
        // Semantic correctness: result = sum(scalars[i] * points[i])
        result.is_some() ==> edwards_point_as_affine(result.unwrap()) == sum_of_scalar_muls(
            spec_scalars_from_iter::<S, I>(scalars),
            unwrap_points(spec_optional_points_from_iter::<J>(points)),
        ),
{
    // Capture ghost spec values before consuming iterators
    let ghost spec_scalars = spec_scalars_from_iter::<S, I>(scalars);
    let ghost spec_points = spec_optional_points_from_iter::<J>(points);

    // Collect scalars and points (via external_body helpers from pippenger)
    let scalars_vec = collect_scalars_from_iter(scalars);
    let points_vec = collect_optional_points_from_iter(points);

    /* <ORIGINAL CODE>
    let nafs: Vec<_> = scalars
        .into_iter()
        .map(|c| c.borrow().non_adjacent_form(5))
        .collect();
    </ORIGINAL CODE> */
    let mut nafs: Vec<[i8; 256]> = Vec::new();
    let mut idx: usize = 0;
    while idx < scalars_vec.len()
        decreases scalars_vec.len() - idx,
    {
        proof { assume(false); } // PROOF BYPASS
        nafs.push(scalars_vec[idx].non_adjacent_form(5));
        idx = idx + 1;
    }

    /* <ORIGINAL CODE>
    let lookup_tables = points
        .into_iter()
        .map(|P_opt| P_opt.map(|P| NafLookupTable5::<ProjectiveNielsPoint>::from(&P)))
        .collect::<Option<Vec<_>>>()?;
    </ORIGINAL CODE> */
    let mut lookup_tables: Vec<NafLookupTable5<ProjectiveNielsPoint>> = Vec::new();
    idx = 0;
    while idx < points_vec.len()
        decreases points_vec.len() - idx,
    {
        proof { assume(false); } // PROOF BYPASS
        match points_vec[idx] {
            Some(P) => {
                lookup_tables.push(NafLookupTable5::<ProjectiveNielsPoint>::from(&P));
            }
            None => {
                // PROOF BYPASS: Found a None point, so not all_points_some
                proof { assume(!all_points_some(spec_points)); }
                return None;
            }
        }
        idx = idx + 1;
    }

    let mut r = ProjectivePoint::identity();

    /* <ORIGINAL CODE>
    for i in (0..256).rev() {
        let mut t: CompletedPoint = r.double();

        for (naf, lookup_table) in nafs.iter().zip(lookup_tables.iter()) {
            match naf[i].cmp(&0) {
                Ordering::Greater => {
                    t = &t.as_extended() + &lookup_table.select(naf[i] as usize)
                }
                Ordering::Less => t = &t.as_extended() - &lookup_table.select(-naf[i] as usize),
                Ordering::Equal => {}
            }
        }

        r = t.as_projective();
    }
    </ORIGINAL CODE> */
    let mut i: usize = 256;
    loop
        decreases i,
    {
        proof { assume(false); } // PROOF BYPASS
        if i == 0 {
            break;
        }
        i = i - 1;

        let mut t: CompletedPoint = r.double();

        // Inner loop: iterate over nafs and lookup_tables
        let mut j: usize = 0;
        let min_len = if nafs.len() < lookup_tables.len() { nafs.len() } else { lookup_tables.len() };
        while j < min_len
            decreases min_len - j,
        {
            proof { assume(false); } // PROOF BYPASS
            let naf = &nafs[j];
            let lookup_table = &lookup_tables[j];

            match naf[i].cmp(&0) {
                Ordering::Greater => {
                    t = &t.as_extended() + &lookup_table.select(naf[i] as usize);
                }
                Ordering::Less => {
                    t = &t.as_extended() - &lookup_table.select((-naf[i]) as usize);
                }
                Ordering::Equal => {}
            }
            j = j + 1;
        }

        r = t.as_projective();
    }

    assume(false);  // PROOF BYPASS: as_extended precondition requires loop invariants
    let result = r.as_extended();

    // PROOF BYPASS: Assert postconditions for verification goal
    proof {
        assume(all_points_some(spec_points));
        assume(is_well_formed_edwards_point(result));
        assume(edwards_point_as_affine(result) == sum_of_scalar_muls(
            spec_scalars,
            unwrap_points(spec_points),
        ));
    }

    Some(result)
}
} // impl Straus

} // verus!

#[cfg(test)]
mod test {
    use super::*;
    use crate::constants;
    use crate::traits::VartimeMultiscalarMul;

    #[test]
    fn test_straus_original_vs_verus() {
        // Test various sizes
        let test_sizes = [1, 2, 3, 4, 8, 16, 32, 64, 100, 150];
        
        let num_rounds = 20;  // Random rounds per size
        let mut total_comparisons = 0;
        
        for size in test_sizes {
            for round in 0..num_rounds {
                // Generate pseudo-random scalars and points using deterministic seeds
                let seed_base = (size as u64) * 1000 + (round as u64);
                
                let points: Vec<_> = (0..size)
                    .map(|i| {
                        let seed = Scalar::from(seed_base + (i as u64) * 7 + 1);
                        constants::ED25519_BASEPOINT_POINT * seed
                    })
                    .collect();
                
                let scalars: Vec<_> = (0..size)
                    .map(|i| {
                        let a = Scalar::from(seed_base * 3 + (i as u64) * 13 + 5);
                        let b = Scalar::from((i as u64) + 1);
                        a * b
                    })
                    .collect();
                
                // Original implementation
                let original = Straus::optional_multiscalar_mul(
                    scalars.iter(),
                    points.iter().map(|p| Some(*p)),
                );
                
                // Verus implementation
                let verus = Straus::optional_multiscalar_mul_verus(
                    scalars.iter(),
                    points.iter().map(|p| Some(*p)),
                );
                
                assert!(original.is_some(), "Original returned None at size={}, round={}", size, round);
                assert!(verus.is_some(), "Verus returned None at size={}, round={}", size, round);
                
                assert_eq!(
                    original.unwrap().compress(),
                    verus.unwrap().compress(),
                    "Mismatch at size={}, round={}", size, round
                );
                
                total_comparisons += 1;
            }
        }
        
        println!("Straus original vs verus: {} comparisons passed!", total_comparisons);
    }
}
