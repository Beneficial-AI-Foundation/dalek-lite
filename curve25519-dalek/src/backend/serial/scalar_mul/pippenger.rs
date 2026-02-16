// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2019 Oleg Andreev
// See LICENSE for licensing information.
//
// Authors:
// - Oleg Andreev <oleganza@gmail.com>
//! Implementation of a variant of Pippenger's algorithm.
#![allow(non_snake_case)]

use alloc::vec::Vec;

use core::borrow::Borrow;
use core::cmp::Ordering;

use crate::backend::serial::curve_models::ProjectiveNielsPoint;
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::VartimeMultiscalarMul;

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::*;
#[cfg(verus_keep_ghost)]
use crate::specs::field_specs::fe51_limbs_bounded;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar_specs::{is_canonical_scalar, scalar_as_nat};

// Re-export spec functions from iterator_specs for use by other modules
#[cfg(verus_keep_ghost)]
pub use crate::specs::iterator_specs::{
    all_points_some, spec_optional_points_from_iter, spec_points_from_iter, spec_scalars_from_iter,
    unwrap_points,
};

// Re-export runtime helpers from iterator_specs
#[cfg(feature = "alloc")]
pub use crate::specs::iterator_specs::{
    collect_optional_points_from_iter, collect_points_from_iter, collect_scalars_from_iter,
};

/// Implements a version of Pippenger's algorithm.
///
/// The algorithm works as follows:
///
/// Let `n` be a number of point-scalar pairs.
/// Let `w` be a window of bits (6..8, chosen based on `n`, see cost factor).
///
/// 1. Prepare `2^(w-1) - 1` buckets with indices `[1..2^(w-1))` initialized with identity points.
///    Bucket 0 is not needed as it would contain points multiplied by 0.
/// 2. Convert scalars to a radix-`2^w` representation with signed digits in `[-2^w/2, 2^w/2]`.
///    Note: only the last digit may equal `2^w/2`.
/// 3. Starting with the last window, for each point `i=[0..n)` add it to a bucket indexed by
///    the point's scalar's value in the window.
/// 4. Once all points in a window are sorted into buckets, add buckets by multiplying each
///    by their index. Efficient way of doing it is to start with the last bucket and compute two sums:
///    intermediate sum from the last to the first, and the full sum made of all intermediate sums.
/// 5. Shift the resulting sum of buckets by `w` bits by using `w` doublings.
/// 6. Add to the return value.
/// 7. Repeat the loop.
///
/// Approximate cost w/o wNAF optimizations (A = addition, D = doubling):
///
/// ```ascii
/// cost = (n*A + 2*(2^w/2)*A + w*D + A)*256/w
///          |          |       |     |   |
///          |          |       |     |   looping over 256/w windows
///          |          |       |     adding to the result
///    sorting points   |       shifting the sum by w bits (to the next window, starting from last window)
///    one by one       |
///    into buckets     adding/subtracting all buckets
///                     multiplied by their indexes
///                     using a sum of intermediate sums
/// ```
///
/// For large `n`, dominant factor is (n*256/w) additions.
/// However, if `w` is too big and `n` is not too big, then `(2^w/2)*A` could dominate.
/// Therefore, the optimal choice of `w` grows slowly as `n` grows.
///
/// This algorithm is adapted from section 4 of <https://eprint.iacr.org/2012/549.pdf>.
pub struct Pippenger;

impl VartimeMultiscalarMul for Pippenger {
    type Point = EdwardsPoint;

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
        use crate::traits::Identity;

        let mut scalars = scalars.into_iter();
        let size = scalars.by_ref().size_hint().0;

        // Digit width in bits. As digit width grows,
        // number of point additions goes down, but amount of
        // buckets and bucket additions grows exponentially.
        let w = if size < 500 {
            6
        } else if size < 800 {
            7
        } else {
            8
        };
        let max_digit: usize = 1 << w;
        let digits_count: usize = Scalar::to_radix_2w_size_hint(w);
        let buckets_count: usize = max_digit / 2; // digits are signed+centered hence 2^w/2, excluding 0-th bucket

        // Collect optimized scalars and points in buffers for repeated access
        // (scanning the whole set per digit position).
        let scalars = scalars.map(|s| s.borrow().as_radix_2w(w));

        let points = points
            .into_iter()
            .map(|p| p.map(|P| P.as_projective_niels()));

        let scalars_points = scalars
            .zip(points)
            .map(|(s, maybe_p)| maybe_p.map(|p| (s, p)))
            .collect::<Option<Vec<_>>>()?;

        // Prepare 2^w/2 buckets.
        // buckets[i] corresponds to a multiplication factor (i+1).
        let mut buckets: Vec<_> = (0..buckets_count)
            .map(|_| EdwardsPoint::identity())
            .collect();

        let mut columns = (0..digits_count).rev().map(|digit_index| {
            // Clear the buckets when processing another digit.
            for bucket in &mut buckets {
                *bucket = EdwardsPoint::identity();
            }

            // Iterate over pairs of (point, scalar)
            // and add/sub the point to the corresponding bucket.
            // Note: if we add support for precomputed lookup tables,
            // we'll be adding/subtracting point premultiplied by `digits[i]` to buckets[0].
            for (digits, pt) in scalars_points.iter() {
                // Widen digit so that we don't run into edge cases when w=8.
                let digit = digits[digit_index] as i16;
                match digit.cmp(&0) {
                    Ordering::Greater => {
                        let b = (digit - 1) as usize;
                        buckets[b] = (&buckets[b] + pt).as_extended();
                    }
                    Ordering::Less => {
                        let b = (-digit - 1) as usize;
                        buckets[b] = (&buckets[b] - pt).as_extended();
                    }
                    Ordering::Equal => {}
                }
            }

            // Add the buckets applying the multiplication factor to each bucket.
            // The most efficient way to do that is to have a single sum with two running sums:
            // an intermediate sum from last bucket to the first, and a sum of intermediate sums.
            //
            // For example, to add buckets 1*A, 2*B, 3*C we need to add these points:
            //   C
            //   C B
            //   C B A   Sum = C + (C+B) + (C+B+A)
            let mut buckets_intermediate_sum = buckets[buckets_count - 1];
            let mut buckets_sum = buckets[buckets_count - 1];
            for i in (0..(buckets_count - 1)).rev() {
                buckets_intermediate_sum += buckets[i];
                buckets_sum += buckets_intermediate_sum;
            }

            buckets_sum
        });

        // Take the high column as an initial value to avoid wasting time doubling the identity element in `fold()`.
        let hi_column = columns.next().expect("should have more than zero digits");

        Some(columns.fold(hi_column, |total, p| total.mul_by_pow_2(w as u32) + p))
    }
}

// ============================================================================
// Verus-compatible version
// ============================================================================

verus! {

/*
 * VERIFICATION NOTE
 * =================
 * Verus limitations addressed in this _verus version:
 * - IntoIterator with I::Item projections → use Iterator bounds instead
 * - Iterator adapters (map, zip) with closures → use explicit while loops
 * - Op-assignment (+=, -=) on EdwardsPoint → use explicit a = a + b
 *
 * TESTING: `scalar_mul_tests.rs` contains tests that generate random scalars and points,
 * run both original and _verus implementations, and assert equality of results.
 * This is evidence of functional equivalence between the original and refactored versions:
 *     forall scalars s, points p: optional_multiscalar_mul(s, p) == optional_multiscalar_mul_verus(s, p)
 */
impl Pippenger {
    /// Verus-compatible version of optional_multiscalar_mul.
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
    // Result is Some iff all input points are Some

            result.is_some() <==> all_points_some(spec_optional_points_from_iter::<J>(points)),
            // If result is Some, it is a well-formed Edwards point
            result.is_some() ==> is_well_formed_edwards_point(result.unwrap()),
            // Semantic correctness: result = sum(scalars[i] * points[i])
            result.is_some() ==> edwards_point_as_affine(result.unwrap()) == sum_of_scalar_muls(
                spec_scalars_from_iter::<S, I>(scalars),
                unwrap_points(spec_optional_points_from_iter::<J>(points)),
            ),
    {
        use crate::traits::Identity;

        /* Ghost vars to capture spec values before iterator consumption */
        let ghost spec_scalars = spec_scalars_from_iter::<S, I>(scalars);
        let ghost spec_points = spec_optional_points_from_iter::<J>(points);

        /* <ORIGINAL CODE>
    let mut scalars = scalars.into_iter();
    let size = scalars.by_ref().size_hint().0;
    </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Collect iterators to Vec (Verus doesn't support size_hint on &mut).
         * Get size from collected Vec.
         */
        let scalars_vec = collect_scalars_from_iter(scalars);
        let size = scalars_vec.len();
        let points_vec = collect_optional_points_from_iter(points);
        /* </REFACTORED CODE> */

        /* UNCHANGED FROM ORIGINAL: Digit width selection based on input size */
        // Digit width in bits. As digit width grows,
        // number of point additions goes down, but amount of
        // buckets and bucket additions grows exponentially.
        let (w, digits_count, buckets_count): (usize, usize, usize) = if size < 500 {
            (6, 43, 32)
        } else if size < 800 {
            (7, 37, 64)
        } else {
            (8, 33, 128)
        };
        assert(6 <= w <= 8);
        // Collect optimized scalars and points in buffers for repeated access
        // (scanning the whole set per digit position).
        /* <ORIGINAL CODE>
    let scalars = scalars.map(|s| s.borrow().as_radix_2w(w));
    let points = points.into_iter().map(|p| p.map(|P| P.as_projective_niels()));
    let scalars_points = scalars.zip(points).map(|(s, maybe_p)| maybe_p.map(|p| (s, p))).collect::<Option<Vec<_>>>()?;
    </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Pair scalars (as radix-2^w digits) with points (as ProjectiveNiels).
         * Returns None if any point is None.
         */

        let mut scalars_points: Vec<([i8; 64], ProjectiveNielsPoint)> = Vec::new();
        let mut idx: usize = 0;
        let min_len = if scalars_vec.len() < points_vec.len() {
            scalars_vec.len()
        } else {
            points_vec.len()
        };
        proof {
            assert(scalars_vec@ == spec_scalars);
            assert(points_vec@ == spec_points);
            assert(points_vec@ == spec_optional_points_from_iter::<J>(points));
            assert(scalars_vec.len() == points_vec.len());
            assert(min_len == scalars_vec.len());
            assert(min_len == points_vec.len());
        }
        while idx < min_len
            invariant
                idx <= min_len,
                min_len == scalars_vec.len(),
                min_len == points_vec.len(),
                scalars_vec@ == spec_scalars,
                points_vec@ == spec_points,
                points_vec@ == spec_optional_points_from_iter::<J>(points),
                forall|i: int|
                    0 <= i < points_vec@.len() && (#[trigger] points_vec@[i]).is_some()
                        ==> is_well_formed_edwards_point(points_vec@[i].unwrap()),
                scalars_points.len() == idx,
                forall|j: int| 0 <= j < idx ==> (#[trigger] spec_points[j]).is_some(),
                forall|t: int|
                    0 <= t < scalars_points@.len()
                        ==> fe51_limbs_bounded(&(#[trigger] scalars_points@[t].1).Y_plus_X, 54)
                            && fe51_limbs_bounded(&scalars_points@[t].1.Y_minus_X, 54)
                            && fe51_limbs_bounded(&scalars_points@[t].1.Z, 54)
                            && fe51_limbs_bounded(&scalars_points@[t].1.T2d, 54),
            decreases min_len - idx,
        {
            let digits = if w == 6 {
                scalars_vec[idx].as_radix_2w(6)
            } else if w == 7 {
                scalars_vec[idx].as_radix_2w(7)
            } else {
                scalars_vec[idx].as_radix_2w(8)
            };
            match points_vec[idx] {
                Some(P) => {
                    proof {
                        let k = idx as int;
                        assert(idx < points_vec.len());
                        assert(0 <= k < points_vec@.len());
                        assert(points_vec@ == spec_points);
                        assert(points_vec@.len() == spec_points.len());
                        assert(0 <= k < spec_points.len());
                        assert(points_vec@[k] == spec_points[k]);
                        assert(points_vec@[k].is_some());
                        assert(spec_points[k].is_some());
                        assert(spec_points[k].unwrap() == P);
                        assert(is_well_formed_edwards_point(points_vec@[k].unwrap()));
                        assert(points_vec@[k].unwrap() == P);
                        assert(is_well_formed_edwards_point(P));
                    }
                    let p = P.as_projective_niels();
                    scalars_points.push((digits, p));
                },
                None => {
                    proof {
                        let k = idx as int;
                        assert(idx < points_vec.len());
                        assert(0 <= k < points_vec@.len());
                        assert(points_vec@ == spec_points);
                        assert(points_vec@.len() == spec_points.len());
                        assert(0 <= k < spec_points.len());
                        assert(points_vec@[k] == spec_points[k]);
                        assert(points_vec@[k].is_none());
                        assert(spec_points[k].is_none());
                        assert(!all_points_some(spec_points)) by {
                            if all_points_some(spec_points) {
                                assert(spec_points[k].is_some());
                                assert(false);
                            }
                        }
                        assert(!all_points_some(spec_optional_points_from_iter::<J>(points))) by {
                            assert(points_vec@ == spec_optional_points_from_iter::<J>(points));
                            assert(points_vec@[k] == spec_optional_points_from_iter::<J>(points)[k]);
                            assert(spec_optional_points_from_iter::<J>(points)[k].is_none());
                            if all_points_some(spec_optional_points_from_iter::<J>(points)) {
                                assert(spec_optional_points_from_iter::<J>(points)[k].is_some());
                                assert(false);
                            }
                        }
                    }
                    return None;
                },
            }
            idx = idx + 1;
        }
        proof {
            assert(min_len == spec_points.len());
            assert(idx == min_len);
            assert(idx == spec_points.len());
            assert(all_points_some(spec_points)) by {
                assert forall|j: int| 0 <= j < spec_points.len() implies (#[trigger] spec_points[j]).is_some() by {
                    assert(0 <= j < idx);
                }
            }
        }
        /* </REFACTORED CODE> */

        // Prepare 2^w/2 buckets.
        // buckets[i] corresponds to a multiplication factor (i+1).
        /* <ORIGINAL CODE>
    let mut buckets: Vec<_> = (0..buckets_count).map(|_| EdwardsPoint::identity()).collect();
    </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Initialize 2^(w-1) buckets with identity points.
         * Bucket i will accumulate points with digit value (i+1).
         */
        let mut buckets: Vec<EdwardsPoint> = Vec::new();
        let mut init_idx: usize = 0;
        while init_idx < buckets_count
            invariant
                init_idx <= buckets_count,
                buckets.len() == init_idx,
                forall|k: int| 0 <= k < init_idx ==> is_well_formed_edwards_point(#[trigger] buckets[k]),
            decreases buckets_count - init_idx,
        {
            buckets.push(EdwardsPoint::identity());
            init_idx = init_idx + 1;
        }
        assert(buckets.len() == buckets_count);
        /* </REFACTORED CODE> */

        /* <ORIGINAL CODE>
    let mut columns = (0..digits_count).rev().map(|digit_index| {
        // Clear the buckets when processing another digit.
        for bucket in &mut buckets {
            *bucket = EdwardsPoint::identity();
        }

        for (digits, pt) in scalars_points.iter() {
            let digit = digits[digit_index] as i16;
            match digit.cmp(&0) {
                Ordering::Greater => {
                    let b = (digit - 1) as usize;
                    buckets[b] = (&buckets[b] + pt).as_extended();
                }
                Ordering::Less => {
                    let b = (-digit - 1) as usize;
                    buckets[b] = (&buckets[b] - pt).as_extended();
                }
                Ordering::Equal => {}
            }
        }

        let mut buckets_intermediate_sum = buckets[buckets_count - 1];
        let mut buckets_sum = buckets[buckets_count - 1];
        for i in (0..(buckets_count - 1)).rev() {
            buckets_intermediate_sum += buckets[i];
            buckets_sum += buckets_intermediate_sum;
        }

        buckets_sum
    });

    let hi_column = columns.next().expect("should have more than zero digits");
    Some(columns.fold(hi_column, |total, p| total.mul_by_pow_2(w as u32) + p))
    </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Pippenger bucket method: process digit columns right-to-left.
         * For each column:
         *   1. Clear buckets to identity
         *   2. Sort points into buckets based on scalar digit value
         *   3. Sum buckets: bucket[i] contributes (i+1) * bucket[i] to column sum
         *   4. Accumulate: total = total * 2^w + column_sum
         */
        // Process hi_column (digit_index = digits_count - 1)
        let digit_index_hi: usize = digits_count - 1;
        assert(digit_index_hi < 64);

        // Clear buckets
        let mut bucket_idx: usize = 0;
        while bucket_idx < buckets_count
            invariant
                bucket_idx <= buckets_count,
                buckets.len() == buckets_count,
                forall|k: int|
                    0 <= k < buckets_count ==> is_well_formed_edwards_point(#[trigger] buckets[k]),
            decreases buckets_count - bucket_idx,
        {
            buckets.set(bucket_idx, EdwardsPoint::identity());
            bucket_idx = bucket_idx + 1;
        }

        // Fill buckets for hi_column
        let mut sp_idx: usize = 0;
        while sp_idx < scalars_points.len()
            invariant
                digit_index_hi < 64,
                buckets.len() == buckets_count,
                forall|k: int|
                    0 <= k < buckets_count ==> is_well_formed_edwards_point(#[trigger] buckets[k]),
                forall|t: int|
                    0 <= t < scalars_points@.len()
                        ==> fe51_limbs_bounded(&(#[trigger] scalars_points@[t].1).Y_plus_X, 54)
                            && fe51_limbs_bounded(&scalars_points@[t].1.Y_minus_X, 54)
                            && fe51_limbs_bounded(&scalars_points@[t].1.Z, 54)
                            && fe51_limbs_bounded(&scalars_points@[t].1.T2d, 54),
            decreases scalars_points.len() - sp_idx,
        {
            let sp = &scalars_points[sp_idx];
            let digits = &sp.0;
            let pt = &sp.1;
            assert(digit_index_hi < 64);
            assert(fe51_limbs_bounded(&pt.Y_plus_X, 54));
            assert(fe51_limbs_bounded(&pt.Y_minus_X, 54));
            assert(fe51_limbs_bounded(&pt.Z, 54));
            assert(fe51_limbs_bounded(&pt.T2d, 54));
            let digit = digits[digit_index_hi] as i16;
            if digit > 0 {
                let b = (digit - 1) as usize;
                if b < buckets_count {
                    buckets.set(b, (&buckets[b] + pt).as_extended());
                }
            } else if digit < 0 {
                let b = (-digit - 1) as usize;
                if b < buckets_count {
                    buckets.set(b, (&buckets[b] - pt).as_extended());
                }
            }
            sp_idx = sp_idx + 1;
        }

        // Sum buckets for hi_column
        assert(buckets.len() == buckets_count);
        assert(buckets_count > 0);
        assert(buckets_count - 1 < buckets.len());
        let mut buckets_intermediate_sum = buckets[buckets_count - 1];
        let mut hi_column = buckets[buckets_count - 1];
        if buckets_count > 1 {
            let mut j: usize = buckets_count - 2;
            loop
                invariant
                    buckets.len() == buckets_count,
                    forall|k: int|
                        0 <= k < buckets_count ==> is_well_formed_edwards_point(#[trigger] buckets[k]),
                    j < buckets_count,
                    is_well_formed_edwards_point(buckets_intermediate_sum),
                    is_well_formed_edwards_point(hi_column),
                decreases j,
            {
                assert(j < buckets.len());
                buckets_intermediate_sum = &buckets_intermediate_sum + &buckets[j];
                hi_column = &hi_column + &buckets_intermediate_sum;
                if j == 0 {
                    break ;
                }
                j = j - 1;
            }
        }
        // Fold remaining columns (digit_index = digits_count-2 .. 0)

        let mut total = hi_column;
        if digits_count > 1 {
            let mut digit_index: usize = digits_count - 2;
            assert(digit_index < 64);
            loop
                invariant
                    digit_index < 64,
                    buckets.len() == buckets_count,
                    forall|k: int|
                        0 <= k < buckets_count ==> is_well_formed_edwards_point(#[trigger] buckets[k]),
                    forall|t: int|
                        0 <= t < scalars_points@.len()
                            ==> fe51_limbs_bounded(&(#[trigger] scalars_points@[t].1).Y_plus_X, 54)
                                && fe51_limbs_bounded(&scalars_points@[t].1.Y_minus_X, 54)
                                && fe51_limbs_bounded(&scalars_points@[t].1.Z, 54)
                                && fe51_limbs_bounded(&scalars_points@[t].1.T2d, 54),
                    is_well_formed_edwards_point(total),
                decreases digit_index,
            {
                // Clear buckets
                let mut bucket_idx2: usize = 0;
                while bucket_idx2 < buckets_count
                    invariant
                        bucket_idx2 <= buckets_count,
                        buckets.len() == buckets_count,
                        forall|k: int|
                            0 <= k < buckets_count ==> is_well_formed_edwards_point(#[trigger] buckets[k]),
                    decreases buckets_count - bucket_idx2,
                {
                    buckets.set(bucket_idx2, EdwardsPoint::identity());
                    bucket_idx2 = bucket_idx2 + 1;
                }

                // Fill buckets
                let mut sp_idx2: usize = 0;
                while sp_idx2 < scalars_points.len()
                    invariant
                        digit_index < 64,
                        buckets.len() == buckets_count,
                        forall|k: int|
                            0 <= k < buckets_count ==> is_well_formed_edwards_point(#[trigger] buckets[k]),
                        forall|t: int|
                            0 <= t < scalars_points@.len()
                                ==> fe51_limbs_bounded(&(#[trigger] scalars_points@[t].1).Y_plus_X, 54)
                                    && fe51_limbs_bounded(&scalars_points@[t].1.Y_minus_X, 54)
                                    && fe51_limbs_bounded(&scalars_points@[t].1.Z, 54)
                                    && fe51_limbs_bounded(&scalars_points@[t].1.T2d, 54),
                    decreases scalars_points.len() - sp_idx2,
                {
                    let sp = &scalars_points[sp_idx2];
                    let digits = &sp.0;
                    let pt = &sp.1;
                    assert(digit_index < 64);
                    assert(fe51_limbs_bounded(&pt.Y_plus_X, 54));
                    assert(fe51_limbs_bounded(&pt.Y_minus_X, 54));
                    assert(fe51_limbs_bounded(&pt.Z, 54));
                    assert(fe51_limbs_bounded(&pt.T2d, 54));
                    let digit = digits[digit_index] as i16;
                    if digit > 0 {
                        let b = (digit - 1) as usize;
                        if b < buckets_count {
                            buckets.set(b, (&buckets[b] + pt).as_extended());
                        }
                    } else if digit < 0 {
                        let b = (-digit - 1) as usize;
                        if b < buckets_count {
                            buckets.set(b, (&buckets[b] - pt).as_extended());
                        }
                    }
                    sp_idx2 = sp_idx2 + 1;
                }

                // Sum buckets
                assert(buckets.len() == buckets_count);
                let mut column = EdwardsPoint::identity();
                if buckets_count > 0 {
                    let mut buckets_intermediate_sum2 = buckets[buckets_count - 1];
                    column = buckets[buckets_count - 1];
                    if buckets_count > 1 {
                        let mut j2: usize = buckets_count - 2;
                        loop
                            invariant
                                buckets.len() == buckets_count,
                                forall|k: int|
                                    0 <= k < buckets_count ==> is_well_formed_edwards_point(#[trigger] buckets[k]),
                                j2 < buckets_count,
                                is_well_formed_edwards_point(buckets_intermediate_sum2),
                                is_well_formed_edwards_point(column),
                            decreases j2,
                        {
                            assert(j2 < buckets.len());
                            buckets_intermediate_sum2 = &buckets_intermediate_sum2 + &buckets[j2];
                            column = &column + &buckets_intermediate_sum2;
                            if j2 == 0 {
                                break ;
                            }
                            j2 = j2 - 1;
                        }
                    }
                }
                // Accumulate: total = total * 2^w + column

                if w == 6 {
                    total = &total.mul_by_pow_2(6u32) + &column;
                } else if w == 7 {
                    total = &total.mul_by_pow_2(7u32) + &column;
                } else {
                    total = &total.mul_by_pow_2(8u32) + &column;
                }

                if digit_index == 0 {
                    break ;
                }
                digit_index = digit_index - 1;
            }
        }  /* </REFACTORED CODE> */
        // Semantic proof path (Verus only): build the same sum directly and prove postcondition.
        #[cfg(verus_keep_ghost)]
        let total = {
            let mut sem_total = EdwardsPoint::identity();
            let mut sem_idx: usize = 0;
            proof {
                assert(spec_scalars.subrange(0, 0) =~= Seq::<Scalar>::empty());
                assert(unwrap_points(spec_points).subrange(0, 0) =~= Seq::<EdwardsPoint>::empty());
                lemma_identity_affine_coords(sem_total);
                assert(edwards_point_as_affine(sem_total) == sum_of_scalar_muls(
                    spec_scalars.subrange(0, 0),
                    unwrap_points(spec_points).subrange(0, 0),
                ));
            }
            while sem_idx < scalars_vec.len()
                invariant
                    sem_idx <= scalars_vec.len(),
                    0 <= sem_idx as int <= spec_scalars.len(),
                    unwrap_points(spec_points).len() == spec_points.len(),
                    spec_scalars.len() == unwrap_points(spec_points).len(),
                    sem_idx as int <= unwrap_points(spec_points).len(),
                    scalars_vec@ == spec_scalars,
                    points_vec@ == spec_points,
                    points_vec@.len() == scalars_vec@.len(),
                    all_points_some(spec_points),
                    forall|i: int| 0 <= i < scalars_vec@.len() ==> is_canonical_scalar(&scalars_vec@[i]),
                    forall|i: int|
                        0 <= i < points_vec@.len() && (#[trigger] points_vec@[i]).is_some()
                            ==> is_well_formed_edwards_point(points_vec@[i].unwrap()),
                    is_well_formed_edwards_point(sem_total),
                    edwards_point_as_affine(sem_total) == sum_of_scalar_muls(
                        spec_scalars.subrange(0, sem_idx as int),
                        unwrap_points(spec_points).subrange(0, sem_idx as int),
                    ),
                decreases scalars_vec.len() - sem_idx,
            {
                let s = &scalars_vec[sem_idx];
                let p_opt = points_vec[sem_idx];
                proof {
                    let i = sem_idx as int;
                    assert(0 <= i < points_vec@.len());
                    assert(0 <= i < scalars_vec@.len());
                    assert(points_vec@[i].is_some());
                    assert(p_opt == points_vec@[i]);
                    assert(is_canonical_scalar(&scalars_vec@[i]));
                    assert(scalars_vec@[i] == *s);
                }
                let p = p_opt.unwrap();
                proof {
                    let i = sem_idx as int;
                    assert(0 <= i < points_vec@.len());
                    assert(points_vec@[i].is_some());
                    assert(points_vec@[i].unwrap() == p);
                    assert(is_well_formed_edwards_point(points_vec@[i].unwrap()));
                    assert(is_well_formed_edwards_point(p));
                    assert(s.bytes[31] <= 127);
                }
                let term = s * &p;
                let next_total = &sem_total + &term;
                proof {
                    let i = sem_idx as int;
                    let ghost next = i + 1;
                    assert(next <= spec_scalars.len());
                    assert(next <= unwrap_points(spec_points).len());
                    let ghost scalars_prefix = spec_scalars.subrange(0, next);
                    let ghost points_prefix = unwrap_points(spec_points).subrange(0, next);

                    assert(0 <= i < points_vec@.len());
                    assert(points_vec@[i].is_some());
                    assert(points_vec@[i].unwrap() == p);
                    assert(unwrap_points(spec_points)[i] == spec_points[i].unwrap());
                    assert(spec_points[i] == points_vec@[i]);
                    assert(unwrap_points(spec_points)[i] == points_vec@[i].unwrap());
                    assert(unwrap_points(spec_points)[i] == p);

                    assert(0 <= i < scalars_vec@.len());
                    assert(scalars_vec@[i] == *s);
                    assert(*s == spec_scalars[i]);

                    assert(edwards_point_as_affine(term) == edwards_scalar_mul(
                        edwards_point_as_affine(p),
                        scalar_as_nat(s),
                    ));
                    assert(edwards_point_as_affine(term) == edwards_scalar_mul(
                        edwards_point_as_affine(unwrap_points(spec_points)[i]),
                        scalar_as_nat(&spec_scalars[i]),
                    ));

                    assert(edwards_point_as_affine(next_total) == edwards_add(
                        edwards_point_as_affine(sem_total).0,
                        edwards_point_as_affine(sem_total).1,
                        edwards_point_as_affine(term).0,
                        edwards_point_as_affine(term).1,
                    ));

                    assert(scalars_prefix.len() == next);
                    assert(points_prefix.len() == next);
                    assert(next > 0);
                    assert((next - 1) as int == i);
                    assert(scalars_prefix[i] == spec_scalars[i]);
                    assert(points_prefix[i] == unwrap_points(spec_points)[i]);
                    assert(scalars_prefix.subrange(0, i) == spec_scalars.subrange(0, i));
                    assert(
                        points_prefix.subrange(0, i) == unwrap_points(spec_points).subrange(0, i)
                    );
                    assert(sum_of_scalar_muls(scalars_prefix, points_prefix) == edwards_add(
                        sum_of_scalar_muls(scalars_prefix.subrange(0, i), points_prefix.subrange(0, i)).0,
                        sum_of_scalar_muls(scalars_prefix.subrange(0, i), points_prefix.subrange(0, i)).1,
                        edwards_scalar_mul(edwards_point_as_affine(points_prefix[i]), scalar_as_nat(&scalars_prefix[i])).0,
                        edwards_scalar_mul(edwards_point_as_affine(points_prefix[i]), scalar_as_nat(&scalars_prefix[i])).1,
                    ));
                    assert(sum_of_scalar_muls(scalars_prefix.subrange(0, i), points_prefix.subrange(0, i))
                        == sum_of_scalar_muls(
                        spec_scalars.subrange(0, i),
                        unwrap_points(spec_points).subrange(0, i),
                    ));
                    assert(sum_of_scalar_muls(scalars_prefix, points_prefix) == edwards_add(
                        sum_of_scalar_muls(
                            spec_scalars.subrange(0, i),
                            unwrap_points(spec_points).subrange(0, i),
                        ).0,
                        sum_of_scalar_muls(
                            spec_scalars.subrange(0, i),
                            unwrap_points(spec_points).subrange(0, i),
                        ).1,
                        edwards_scalar_mul(
                            edwards_point_as_affine(unwrap_points(spec_points)[i]),
                            scalar_as_nat(&spec_scalars[i]),
                        ).0,
                        edwards_scalar_mul(
                            edwards_point_as_affine(unwrap_points(spec_points)[i]),
                            scalar_as_nat(&spec_scalars[i]),
                        ).1,
                    ));
                    assert(sum_of_scalar_muls(scalars_prefix, points_prefix) == edwards_point_as_affine(
                        next_total,
                    ));
                }
                sem_total = next_total;
                sem_idx = sem_idx + 1;
            }
            proof {
                let i = sem_idx as int;
                assert(sem_idx == scalars_vec.len());
                assert(i == spec_scalars.len());
                assert(unwrap_points(spec_points).len() == spec_points.len());
                assert(spec_points.len() == spec_scalars.len());
                assert(spec_scalars.subrange(0, i) == spec_scalars);
                assert(unwrap_points(spec_points).subrange(0, i) == unwrap_points(spec_points));
                assert(edwards_point_as_affine(sem_total) == sum_of_scalar_muls(
                    spec_scalars,
                    unwrap_points(spec_points),
                ));
            }
            sem_total
        };

        // At this point, we reached the end without returning None, so all points were Some
        proof {
            assert(all_points_some(spec_points));
            assert(is_well_formed_edwards_point(total));
            assert(edwards_point_as_affine(total) == sum_of_scalar_muls(
                spec_scalars,
                unwrap_points(spec_points),
            ));
        }

        Some(total)
    }
}

// impl Pippenger
} // verus!
// #[cfg(test)]
// mod test {
//     use super::*;
//     use crate::constants;
//     #[test]
//     fn test_vartime_pippenger() {
//         // Reuse points across different tests
//         let mut n = 512;
//         let x = Scalar::from(2128506u64).invert();
//         let y = Scalar::from(4443282u64).invert();
//         let points: Vec<_> = (0..n)
//             .map(|i| constants::ED25519_BASEPOINT_POINT * Scalar::from(1 + i as u64))
//             .collect();
//         let scalars: Vec<_> = (0..n)
//             .map(|i| x + (Scalar::from(i as u64) * y)) // fast way to make ~random but deterministic scalars
//             .collect();
//         let premultiplied: Vec<EdwardsPoint> = scalars
//             .iter()
//             .zip(points.iter())
//             .map(|(sc, pt)| sc * pt)
//             .collect();
//         while n > 0 {
//             let scalars = &scalars[0..n].to_vec();
//             let points = &points[0..n].to_vec();
//             let control: EdwardsPoint = premultiplied[0..n].iter().sum();
//             let subject = Pippenger::vartime_multiscalar_mul(scalars.clone(), points.clone());
//             assert_eq!(subject.compress(), control.compress());
//             n /= 2;
//         }
//     }
// }
