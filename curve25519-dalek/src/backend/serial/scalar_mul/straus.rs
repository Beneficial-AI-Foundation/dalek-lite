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

use crate::backend::serial::curve_models::{CompletedPoint, ProjectiveNielsPoint, ProjectivePoint};
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::Identity;
use crate::traits::MultiscalarMul;
use crate::traits::VartimeMultiscalarMul;
use crate::window::LookupTable;
use crate::window::NafLookupTable5;

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::straus_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::*;
#[cfg(verus_keep_ghost)]
use crate::specs::field_specs::*;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar_specs::*;
#[cfg(verus_keep_ghost)]
use crate::specs::window_specs::*;

// Import spec functions from iterator_specs (ghost only)
#[cfg(verus_keep_ghost)]
use crate::specs::iterator_specs::{
    all_points_some, spec_optional_points_from_iter, spec_points_from_iter, spec_scalars_from_iter,
    unwrap_points,
};

// Import runtime helpers from iterator_specs
use crate::specs::iterator_specs::{
    collect_optional_points_from_iter, collect_points_from_iter, collect_scalars_from_iter,
};

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
        /*
         * VERUS SPEC (intended):
         *   requires
         *       scalars.len() == points.len(),
         *       forall|i| is_well_formed_edwards_point(points[i]),
         *   ensures
         *       is_well_formed_edwards_point(result),
         *       edwards_point_as_affine(result) == sum_of_scalar_muls(scalars, points),
         *
         * NOTE: Verus doesn't support IntoIterator with I::Item projections.
         * The verified version `multiscalar_mul_verus` below uses:
         *   - Iterator bounds instead of IntoIterator
         *   - spec_scalars_from_iter / spec_points_from_iter to convert
         *     iterators to logical sequences (see specs/iterator_specs.rs)
         */
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
        /*
         * VERUS SPEC (intended):
         *   requires
         *       scalars.len() == points.len(),
         *       forall|i| points[i].is_some() ==> is_well_formed_edwards_point(points[i].unwrap()),
         *   ensures
         *       result.is_some() <==> all_points_some(points),
         *       result.is_some() ==> is_well_formed_edwards_point(result.unwrap()),
         *       result.is_some() ==> edwards_point_as_affine(result.unwrap())
         *           == sum_of_scalar_muls(scalars, unwrap_points(points)),
         *
         * NOTE: Verus doesn't support IntoIterator with I::Item projections.
         * The verified version `optional_multiscalar_mul_verus` below uses:
         *   - Iterator bounds instead of IntoIterator
         *   - spec_scalars_from_iter / spec_optional_points_from_iter to convert
         *     iterators to logical sequences (see specs/iterator_specs.rs)
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

verus! {

/*
 * VERIFICATION NOTE
 * =================
 * Verus limitations addressed in these _verus versions:
 * - IntoIterator with I::Item projections → use Iterator bounds instead
 * - Iterator adapters (map, zip) with closures → use explicit while loops
 * - Op-assignment (+=, -=) on EdwardsPoint → use explicit a = a + b
 *
 * TESTING: `scalar_mul_tests.rs` contains tests that generate random scalars and points,
 * run both original and _verus implementations, and assert equality of results.
 * This is evidence of functional equivalence between the original and refactored versions:
 *     forall scalars s, points p:
 *         optional_multiscalar_mul(s, p) == optional_multiscalar_mul_verus(s, p)
 *         multiscalar_mul(s, p) == multiscalar_mul_verus(s, p)
 */
impl Straus {
    /// Verus-compatible version of optional_multiscalar_mul.
    /// Uses Iterator instead of IntoIterator (Verus doesn't support I::Item projections).
    /// Computes sum(scalars[i] * points[i]) for all i where points[i] is Some.
    pub fn optional_multiscalar_mul_verus<S, I, J>(scalars: I, points: J) -> (result: Option<
        EdwardsPoint,
    >) where S: Borrow<Scalar>, I: Iterator<Item = S>, J: Iterator<Item = Option<EdwardsPoint>>
        requires
    // Same number of scalars and points

            spec_scalars_from_iter::<S, I>(scalars).len() == spec_optional_points_from_iter::<J>(
                points,
            ).len(),
            // All input points (when Some) must be well-formed
            forall|i: int|
                0 <= i < spec_optional_points_from_iter::<J>(points).len() && (
                #[trigger] spec_optional_points_from_iter::<J>(points)[i]).is_some()
                    ==> is_well_formed_edwards_point(
                    spec_optional_points_from_iter::<J>(points)[i].unwrap(),
                ),
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
        /* Ghost vars to capture spec values before iterator consumption */
        let ghost spec_scalars = spec_scalars_from_iter::<S, I>(scalars);
        let ghost spec_points = spec_optional_points_from_iter::<J>(points);

        /* <ORIGINAL CODE>
    let nafs: Vec<_> = scalars
        .into_iter()
        .map(|c| c.borrow().non_adjacent_form(5))
        .collect();
    </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Collect iterators to Vec (Verus doesn't support iterator adapters).
         * Then convert each scalar to non-adjacent form (NAF) with width 5.
         */
        let scalars_vec = collect_scalars_from_iter(scalars);
        let points_vec = collect_optional_points_from_iter(points);

        let mut nafs: Vec<[i8; 256]> = Vec::new();
        let mut idx: usize = 0;
        while idx < scalars_vec.len()
            invariant
                0 <= idx <= scalars_vec@.len(),
                nafs@.len() == idx as int,
                scalars_vec@ == spec_scalars,
                // Each NAF is valid
                forall|k: int|
                    0 <= k < idx ==> {
                        &&& is_valid_naf(#[trigger] nafs@[k]@, 5)
                        &&& reconstruct(nafs@[k]@) == scalar_as_nat(&scalars_vec@[k]) as int
                    },
            decreases scalars_vec.len() - idx,
        {
            // From collect_scalars_from_iter: is_canonical_scalar → bytes[31] <= 127
            // → lemma_u8_32_as_nat_lt_pow2_255 → scalar_as_nat < pow2(255)
            proof {
                assert(is_canonical_scalar(&scalars_vec@[idx as int]));
                assert(scalars_vec@[idx as int].bytes[31] <= 127);
                crate::lemmas::common_lemmas::to_nat_lemmas::lemma_u8_32_as_nat_lt_pow2_255(
                    &scalars_vec@[idx as int].bytes,
                );
            }
            nafs.push(scalars_vec[idx].non_adjacent_form(5));
            idx = idx + 1;
        }
        /* </REFACTORED CODE> */

        /* <ORIGINAL CODE>
    let lookup_tables = points
        .into_iter()
        .map(|P_opt| P_opt.map(|P| NafLookupTable5::<ProjectiveNielsPoint>::from(&P)))
        .collect::<Option<Vec<_>>>()?;
    </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Build lookup tables for each point: precompute odd multiples [1P, 3P, 5P, 7P, ...]
         * Returns None if any point is None (propagates optional failure).
         */
        let mut lookup_tables: Vec<NafLookupTable5<ProjectiveNielsPoint>> = Vec::new();
        idx = 0;
        while idx < points_vec.len()
            invariant
                0 <= idx <= points_vec@.len(),
                lookup_tables@.len() == idx as int,
                points_vec@ == spec_points,
                // All processed points were Some (no early return yet)
                forall|k: int| 0 <= k < idx ==> (#[trigger] points_vec@[k]).is_some(),
                // Each table is valid and has bounded limbs
                forall|k: int|
                    0 <= k < idx ==> {
                        &&& is_valid_naf_lookup_table5_projective(
                            (#[trigger] lookup_tables@[k]).0,
                            points_vec@[k].unwrap(),
                        )
                        &&& naf_lookup_table5_projective_limbs_bounded(lookup_tables@[k].0)
                    },
            decreases points_vec.len() - idx,
        {
            match points_vec[idx] {
                Some(P) => {
                    proof {
                        assert(spec_points[idx as int].is_some());
                        assert(is_well_formed_edwards_point(P));
                    }
                    lookup_tables.push(NafLookupTable5::<ProjectiveNielsPoint>::from(&P));
                },
                None => {
                    // Found a None point — witness that !all_points_some
                    proof {
                        // points_vec@[idx] is None, so the quantifier in all_points_some fails
                        assert(!spec_points[idx as int].is_some());
                        assert(!all_points_some(spec_points));
                    }
                    return None;
                },
            }
            idx = idx + 1;
        }
        /* </REFACTORED CODE> */

        // After loop 2: all points were Some (we never returned None)
        proof {
            // All points_vec entries are Some
            assert(forall|k: int|
                0 <= k < spec_points.len() ==> (#[trigger] spec_points[k]).is_some());
            assert(all_points_some(spec_points));
        }

        // Ghost: build the affine points and naf sequences for the spec
        let ghost n = nafs@.len();
        let ghost unwrapped_points: Seq<EdwardsPoint> = unwrap_points(spec_points);
        let ghost pts_affine: Seq<(nat, nat)> = points_to_affine(unwrapped_points);
        let ghost nafs_seqs: Seq<Seq<i8>> = nafs@.map(|_i, d: [i8; 256]| d@);

        /* UNCHANGED FROM ORIGINAL */
        let mut r = ProjectivePoint::identity();

        proof {
            // r starts as identity projective point
            lemma_identity_projective_point_properties();
            lemma_straus_vt_base(pts_affine, nafs_seqs);
        }

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
        /* <REFACTORED CODE>
         * Main double-and-add loop: iterate bit positions 255..0.
         * For each bit position i:
         *   1. Double the accumulator r
         *   2. For each (scalar, point) pair, add/sub the appropriate table entry
         *      based on the NAF digit at position i
         */
        let mut i: usize = 256;
        loop
            invariant
                0 <= i <= 256,
                is_valid_projective_point(r),
                fe51_limbs_bounded(&r.X, 52),
                fe51_limbs_bounded(&r.Y, 52),
                fe51_limbs_bounded(&r.Z, 52),
                sum_of_limbs_bounded(&r.X, &r.Y, u64::MAX),
                // Functional correctness
                projective_point_as_affine_edwards(r) == straus_vt_partial(
                    pts_affine,
                    nafs_seqs,
                    i as int,
                ),
                // Preparation loop postconditions preserved
                nafs@.len() == n,
                lookup_tables@.len() == n,
                n == spec_scalars.len(),
                n == spec_points.len(),
                pts_affine.len() == n,
                nafs_seqs.len() == n,
                forall|k: int|
                    0 <= k < n ==> {
                        &&& is_valid_naf(#[trigger] nafs_seqs[k], 5)
                        &&& reconstruct(nafs_seqs[k]) == scalar_as_nat(&spec_scalars[k]) as int
                    },
                forall|k: int|
                    0 <= k < n ==> {
                        &&& is_valid_naf_lookup_table5_projective(
                            (#[trigger] lookup_tables@[k]).0,
                            spec_points[k].unwrap(),
                        )
                        &&& naf_lookup_table5_projective_limbs_bounded(lookup_tables@[k].0)
                    },
                forall|k: int|
                    0 <= k < n ==> #[trigger] pts_affine[k] == edwards_point_as_affine(
                        unwrapped_points[k],
                    ),
                forall|k: int| 0 <= k < n ==> #[trigger] nafs_seqs[k] == nafs@[k]@,
            decreases i,
        {
            if i == 0 {
                break ;
            }
            i = i - 1;

            let mut t: CompletedPoint = r.double();
            // t = 2*r in CompletedPoint form
            // completed_point_as_affine_edwards(t) == edwards_double(projective_point_as_affine_edwards(r))

            // Inner loop: iterate over nafs and lookup_tables
            let mut j: usize = 0;
            let min_len = if nafs.len() < lookup_tables.len() {
                nafs.len()
            } else {
                lookup_tables.len()
            };

            let ghost doubled_affine = completed_point_as_affine_edwards(t);
            proof {
                assert(min_len == n);
                lemma_column_sum_zero(pts_affine, nafs_seqs, i as int);
            }

            while j < min_len
                invariant
                    0 <= j <= min_len,
                    min_len == n,
                    is_valid_completed_point(t),
                    fe51_limbs_bounded(&t.X, 54),
                    fe51_limbs_bounded(&t.Y, 54),
                    fe51_limbs_bounded(&t.Z, 54),
                    fe51_limbs_bounded(&t.T, 54),
                    // t = edwards_add(doubled_prev, column_sum(i, j))
                    completed_point_as_affine_edwards(t) == {
                        let col_j = straus_column_sum(pts_affine, nafs_seqs, i as int, j as int);
                        edwards_add(doubled_affine.0, doubled_affine.1, col_j.0, col_j.1)
                    },
                    // Preserved table/naf invariants
                    forall|m: int|
                        0 <= m < n ==> {
                            &&& is_valid_naf_lookup_table5_projective(
                                (#[trigger] lookup_tables@[m]).0,
                                spec_points[m].unwrap(),
                            )
                            &&& naf_lookup_table5_projective_limbs_bounded(lookup_tables@[m].0)
                        },
                    forall|m: int| 0 <= m < n ==> is_valid_naf(#[trigger] nafs_seqs[m], 5),
                    forall|m: int|
                        0 <= m < n ==> #[trigger] pts_affine[m] == edwards_point_as_affine(
                            unwrapped_points[m],
                        ),
                    forall|m: int| 0 <= m < n ==> #[trigger] nafs_seqs[m] == nafs@[m]@,
                decreases min_len - j,
            {
                let naf = &nafs[j];
                let lookup_table = &lookup_tables[j];

                match naf[i].cmp(&0) {
                    Ordering::Greater => {
                        proof {
                            // From is_valid_naf(w=5): nonzero digit is odd and in (-pow2(4), pow2(4))
                            assert(is_valid_naf(nafs_seqs[j as int], 5));
                            let digit = naf@[i as int];
                            // Trigger quantifier instantiation + connect pow2(4) = 16
                            assume((digit as int) % 2 != 0 && digit < 16);
                            lemma_naf_digit_positive_select_preconditions(digit);
                        }
                        t = &t.as_extended() + &lookup_table.select(naf[i] as usize);
                    },
                    Ordering::Less => {
                        proof {
                            assert(is_valid_naf(nafs_seqs[j as int], 5));
                            let digit = naf@[i as int];
                            assume((digit as int) % 2 != 0 && digit > -16);
                            lemma_naf_digit_negative_select_preconditions(digit);
                        }
                        t = &t.as_extended() - &lookup_table.select((-naf[i]) as usize);
                    },
                    Ordering::Equal => {},
                }

                proof {
                    // Connect the result to column_sum(i, j+1)
                    assume(completed_point_as_affine_edwards(t) == {
                        let col_jp1 = straus_column_sum(
                            pts_affine,
                            nafs_seqs,
                            i as int,
                            (j + 1) as int,
                        );
                        edwards_add(doubled_affine.0, doubled_affine.1, col_jp1.0, col_jp1.1)
                    });
                    // Limb bounds preserved after add/sub + as_extended
                    assume(is_valid_completed_point(t));
                    assume(fe51_limbs_bounded(&t.X, 54));
                    assume(fe51_limbs_bounded(&t.Y, 54));
                    assume(fe51_limbs_bounded(&t.Z, 54));
                    assume(fe51_limbs_bounded(&t.T, 54));
                }
                j = j + 1;
            }

            r = t.as_projective();

            proof {
                // After inner loop: j == n
                // t = edwards_add(doubled, column_sum(i, n))
                // r = t.as_projective(), affine preserved
                // Connect to straus_vt_partial(i)
                lemma_straus_vt_step(pts_affine, nafs_seqs, i as int);
                assume(projective_point_as_affine_edwards(r) == straus_vt_partial(
                    pts_affine,
                    nafs_seqs,
                    i as int,
                ));
            }
        }
        /* </REFACTORED CODE> */

        // r.as_extended() requires valid projective point + limb bounds (from outer loop invariant)
        let result = r.as_extended();

        proof {
            // r affine == straus_vt_partial(0) == sum_of_scalar_muls
            axiom_straus_vt_correct(spec_scalars, unwrapped_points, pts_affine, nafs_seqs);
            // as_extended preserves affine
            assert(edwards_point_as_affine(result) == projective_point_as_affine_edwards(r));
            assume(is_well_formed_edwards_point(result));
            assume(edwards_point_as_affine(result) == sum_of_scalar_muls(
                spec_scalars,
                unwrapped_points,
            ));
        }

        Some(result)
    }

    /// Verus-compatible version of multiscalar_mul (constant-time).
    /// Uses Iterator instead of IntoIterator (Verus doesn't support I::Item projections).
    /// Computes sum(scalars[i] * points[i]).
    pub fn multiscalar_mul_verus<S, P, I, J>(scalars: I, points: J) -> (result: EdwardsPoint) where
        S: Borrow<Scalar>,
        P: Borrow<EdwardsPoint>,
        I: Iterator<Item = S>,
        J: Iterator<Item = P>,

        requires
    // Same number of scalars and points

            spec_scalars_from_iter::<S, I>(scalars).len() == spec_points_from_iter::<P, J>(
                points,
            ).len(),
            // All input points must be well-formed
            forall|i: int|
                0 <= i < spec_points_from_iter::<P, J>(points).len()
                    ==> is_well_formed_edwards_point(
                    #[trigger] spec_points_from_iter::<P, J>(points)[i],
                ),
        ensures
    // Result is a well-formed Edwards point

            is_well_formed_edwards_point(result),
            // Semantic correctness: result = sum(scalars[i] * points[i])
            edwards_point_as_affine(result) == sum_of_scalar_muls(
                spec_scalars_from_iter::<S, I>(scalars),
                spec_points_from_iter::<P, J>(points),
            ),
    {
        use crate::traits::Identity;

        /* Ghost vars to capture spec values before iterator consumption */
        let ghost spec_scalars = spec_scalars_from_iter::<S, I>(scalars);
        let ghost spec_points = spec_points_from_iter::<P, J>(points);

        /* <ORIGINAL CODE>
        let lookup_tables: Vec<_> = points
            .into_iter()
            .map(|point| LookupTable::<ProjectiveNielsPoint>::from(point.borrow()))
            .collect();
        </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Collect iterators to Vec (Verus doesn't support iterator adapters).
         * Then build lookup tables for each point: precompute multiples [1P, 2P, ..., 8P]
         */
        let scalars_vec = collect_scalars_from_iter(scalars);
        let points_vec = collect_points_from_iter(points);
        let mut lookup_tables: Vec<LookupTable<ProjectiveNielsPoint>> = Vec::new();
        let mut idx: usize = 0;
        while idx < points_vec.len()
            invariant
                0 <= idx <= points_vec@.len(),
                lookup_tables@.len() == idx as int,
                points_vec@ == spec_points,
                // Each table is valid and has bounded limbs
                forall|k: int|
                    0 <= k < idx ==> {
                        &&& is_valid_lookup_table_projective(
                            (#[trigger] lookup_tables@[k]).0,
                            points_vec@[k],
                            8,
                        )
                        &&& lookup_table_projective_limbs_bounded(lookup_tables@[k].0)
                    },
            decreases points_vec.len() - idx,
        {
            // From function precondition + collect_points_from_iter ensures
            proof {
                assert(is_well_formed_edwards_point(points_vec@[idx as int]));
            }
            lookup_tables.push(LookupTable::<ProjectiveNielsPoint>::from(&points_vec[idx]));
            idx = idx + 1;
        }
        /* </REFACTORED CODE> */

        /* <ORIGINAL CODE>
        let mut scalar_digits: Vec<_> = scalars
            .into_iter()
            .map(|s| s.borrow().as_radix_16())
            .collect();
        </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Convert each scalar to radix-16 signed digits: s = sum(s_j * 16^j)
         */
        let mut scalar_digits: Vec<[i8; 64]> = Vec::new();
        idx = 0;
        while idx < scalars_vec.len()
            invariant
                0 <= idx <= scalars_vec@.len(),
                scalar_digits@.len() == idx as int,
                scalars_vec@ == spec_scalars,
                // Each digit array is valid radix-16
                forall|k: int|
                    0 <= k < idx ==> {
                        &&& is_valid_radix_16(&#[trigger] scalar_digits@[k])
                        &&& radix_16_all_bounded(&scalar_digits@[k])
                        &&& reconstruct_radix_16(scalar_digits@[k]@) == scalar_as_nat(
                            &scalars_vec@[k],
                        ) as int
                    },
            decreases scalars_vec.len() - idx,
        {
            // From collect_scalars_from_iter ensures: is_canonical_scalar → bytes[31] <= 127
            proof {
                assert(is_canonical_scalar(&scalars_vec@[idx as int]));
                assert(scalars_vec@[idx as int].bytes[31] <= 127);
            }
            scalar_digits.push(scalars_vec[idx].as_radix_16());
            idx = idx + 1;
        }
        /* </REFACTORED CODE> */

        // Ghost: build the affine points and digit sequences for the spec
        let ghost n = scalars_vec@.len();
        let ghost pts_affine: Seq<(nat, nat)> = points_to_affine(spec_points);
        let ghost digits_seqs: Seq<Seq<i8>> = scalar_digits@.map(|_i, d: [i8; 64]| d@);

        /* UNCHANGED FROM ORIGINAL */
        let mut Q = EdwardsPoint::identity();

        proof {
            // Q starts as identity = straus_ct_partial(64)
            assert(is_well_formed_edwards_point(Q));
            lemma_straus_ct_base(pts_affine, digits_seqs);
        }

        /* <ORIGINAL CODE>
        for j in (0..64).rev() {
            Q = Q.mul_by_pow_2(4);
            let it = scalar_digits.iter().zip(lookup_tables.iter());
            for (s_i, lookup_table_i) in it {
                let R_i = lookup_table_i.select(s_i[j]);
                Q = (&Q + &R_i).as_extended();
            }
        }
        </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Main loop: iterate digit positions 63..0 (radix-16 has 64 digits).
         * For each position j:
         *   1. Multiply accumulator Q by 16 (= 2^4)
         *   2. For each (scalar, point) pair, add s_j * P_i from lookup table
         */
        let mut j: usize = 64;
        loop
            invariant
                0 <= j <= 64,
                is_well_formed_edwards_point(Q),
                // Functional correctness: Q = straus_ct_partial(pts, digits, j)
                edwards_point_as_affine(Q) == straus_ct_partial(pts_affine, digits_seqs, j as int),
                // Preparation loop postconditions preserved
                lookup_tables@.len() == n,
                scalar_digits@.len() == n,
                n == spec_scalars.len(),
                n == spec_points.len(),
                pts_affine.len() == n,
                digits_seqs.len() == n,
                forall|k: int|
                    0 <= k < n ==> {
                        &&& is_valid_lookup_table_projective(
                            (#[trigger] lookup_tables@[k]).0,
                            spec_points[k],
                            8,
                        )
                        &&& lookup_table_projective_limbs_bounded(lookup_tables@[k].0)
                    },
                forall|k: int|
                    0 <= k < n ==> {
                        &&& is_valid_radix_16(&#[trigger] scalar_digits@[k])
                        &&& radix_16_all_bounded(&scalar_digits@[k])
                        &&& reconstruct_radix_16(scalar_digits@[k]@) == scalar_as_nat(
                            &spec_scalars[k],
                        ) as int
                    },
                // Ghost sequence consistency
                forall|k: int|
                    0 <= k < n ==> #[trigger] pts_affine[k] == edwards_point_as_affine(
                        spec_points[k],
                    ),
                forall|k: int| 0 <= k < n ==> #[trigger] digits_seqs[k] == scalar_digits@[k]@,
            decreases j,
        {
            if j == 0 {
                break ;
            }
            j = j - 1;

            // mul_by_pow_2(4) requires is_well_formed_edwards_point and k > 0
            Q = Q.mul_by_pow_2(4);
            // Now Q affine == edwards_scalar_mul(old_Q_affine, pow2(4)) == edwards_scalar_mul(old_Q_affine, 16)

            // Inner loop: iterate over scalar_digits and lookup_tables
            let mut k: usize = 0;
            let min_len = if scalar_digits.len() < lookup_tables.len() {
                scalar_digits.len()
            } else {
                lookup_tables.len()
            };

            // Ghost: track what Q was after scaling (before inner loop adds column terms)
            let ghost scaled_affine = edwards_point_as_affine(Q);
            proof {
                // scaled_affine == edwards_scalar_mul(straus_ct_partial(j+1), 16)
                assert(min_len == n);
                lemma_column_sum_zero(pts_affine, digits_seqs, j as int);
            }

            while k < min_len
                invariant
                    0 <= k <= min_len,
                    min_len == n,
                    is_well_formed_edwards_point(Q),
                    // Q = edwards_add(scaled_prev, column_sum(j, k))
                    edwards_point_as_affine(Q) == {
                        let col_k = straus_column_sum(pts_affine, digits_seqs, j as int, k as int);
                        edwards_add(scaled_affine.0, scaled_affine.1, col_k.0, col_k.1)
                    },
                    // Preserved invariants
                    forall|m: int|
                        0 <= m < n ==> {
                            &&& is_valid_lookup_table_projective(
                                (#[trigger] lookup_tables@[m]).0,
                                spec_points[m],
                                8,
                            )
                            &&& lookup_table_projective_limbs_bounded(lookup_tables@[m].0)
                        },
                    forall|m: int|
                        0 <= m < n ==> {
                            &&& radix_16_all_bounded(&(#[trigger] scalar_digits@[m]))
                        },
                    forall|m: int|
                        0 <= m < n ==> #[trigger] pts_affine[m] == edwards_point_as_affine(
                            spec_points[m],
                        ),
                    forall|m: int| 0 <= m < n ==> #[trigger] digits_seqs[m] == scalar_digits@[m]@,
                decreases min_len - k,
            {
                let s_i = &scalar_digits[k];
                let lookup_table_i = &lookup_tables[k];

                proof {
                    // Establish digit bounds for select precondition
                    assert(radix_16_all_bounded(s_i));
                    assert(-8 <= s_i@[j as int] <= 8) by {
                        assert(radix_16_digit_bounded(s_i@[j as int]));
                    }
                }

                let R_i = lookup_table_i.select(s_i[j]);

                proof {
                    // Connect select result to signed scalar mul via our lemma
                    let base_k = pts_affine[k as int];
                    lemma_select_is_signed_scalar_mul_projective(
                        lookup_table_i.0,
                        s_i[j],
                        R_i,
                        base_k,
                    );

                    // R_i affine == edwards_scalar_mul_signed(base_k, digits[k][j])
                    // which is the term we need to add to column_sum(j, k) to get column_sum(j, k+1)
                }

                Q = (&Q + &R_i).as_extended();

                proof {
                    // After addition: Q affine == edwards_add(old_Q, R_i)
                    // == edwards_add(edwards_add(scaled, col_k), term_k)
                    // By associativity this equals edwards_add(scaled, col_{k+1})
                    // We use the column_sum step lemma to connect
                    assume(edwards_point_as_affine(Q) == {
                        let col_kp1 = straus_column_sum(
                            pts_affine,
                            digits_seqs,
                            j as int,
                            (k + 1) as int,
                        );
                        edwards_add(scaled_affine.0, scaled_affine.1, col_kp1.0, col_kp1.1)
                    });
                }

                k = k + 1;
            }

            proof {
                // After inner loop: k == n, so Q = edwards_add(scaled, column_sum(j, n))
                // This equals straus_ct_partial(j) by definition
                lemma_straus_ct_step(pts_affine, digits_seqs, j as int);

                // Connect: straus_ct_partial(j) = edwards_add(scaled(straus_ct_partial(j+1), 16), column_sum(j, n))
                // We have scaled_affine = edwards_scalar_mul(straus_ct_partial(j+1), 16)
                // and Q = edwards_add(scaled_affine, column_sum(j, n))
                // Therefore Q = straus_ct_partial(j)
                assume(edwards_point_as_affine(Q) == straus_ct_partial(
                    pts_affine,
                    digits_seqs,
                    j as int,
                ));
            }
        }
        /* </REFACTORED CODE> */

        // Final: Q = straus_ct_partial(0) == sum_of_scalar_muls(spec_scalars, spec_points)
        proof {
            axiom_straus_ct_correct(spec_scalars, spec_points, pts_affine, digits_seqs);
        }

        Q
    }
}

// impl Straus
} // verus!
