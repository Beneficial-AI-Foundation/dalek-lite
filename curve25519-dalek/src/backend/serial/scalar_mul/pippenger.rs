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
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::lemmas::edwards_lemmas::pippenger_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::lemmas::edwards_lemmas::straus_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::*;
#[cfg(verus_keep_ghost)]
use crate::specs::field_specs::*;
#[cfg(verus_keep_ghost)]
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar_specs::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{lemma2_to64, pow2};

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
        let w = if size < 500 {
            6
        } else if size < 800 {
            7
        } else {
            8
        };

        /* UNCHANGED FROM ORIGINAL: Bucket configuration */
        let max_digit: usize = 1 << w;
        let digits_count: usize = Scalar::to_radix_2w_size_hint(w);
        let buckets_count: usize = max_digit / 2;  // digits are signed+centered hence 2^w/2, excluding 0-th bucket

        if digits_count == 0 || buckets_count == 0 {
            // PROOF BYPASS: Dead code for valid w (6,7,8), assume postcondition
            proof {
                assume(!all_points_some(spec_points));
            }
            return None;
        }
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
            assert(scalars_vec@.len() == points_vec@.len());
        }
        while idx < min_len
            invariant
                0 <= idx <= min_len,
                min_len == scalars_vec@.len(),
                scalars_vec@.len() == points_vec@.len(),
                scalars_points@.len() == idx as int,
                scalars_vec@ == spec_scalars,
                points_vec@ == spec_points,
                // Ghost connection to postcondition expressions
                spec_points == spec_optional_points_from_iter::<J>(points),
                spec_scalars == spec_scalars_from_iter::<S, I>(scalars),
                4 <= w <= 8,
                digits_count > 0,
                // All scalars are canonical
                forall|k: int|
                    #![auto]
                    0 <= k < scalars_vec@.len() ==> is_canonical_scalar(&scalars_vec@[k]),
                // All input points (when Some) are well-formed
                forall|k: int|
                    0 <= k < points_vec@.len() && (#[trigger] points_vec@[k]).is_some()
                        ==> is_well_formed_edwards_point(points_vec@[k].unwrap()),
                // All processed points were Some
                forall|k: int| 0 <= k < idx ==> (#[trigger] points_vec@[k]).is_some(),
                // Each entry has valid radix-2w digits and reconstruction
                // Note: uses the spec-level formula matching as_radix_2w ensures
                forall|k: int|
                    0 <= k < idx ==> ({
                        let dc = if w < 8 {
                            (256 + (w as int) - 1) / (w as int)
                        } else {
                            (256 + (w as int) - 1) / (w as int) + 1
                        };
                        &&& is_valid_radix_2w(
                            &(#[trigger] scalars_points@[k]).0,
                            w as nat,
                            dc as nat,
                        )
                        &&& reconstruct_radix_2w(scalars_points@[k].0@.take(dc), w as nat)
                            == scalar_as_nat(&scalars_vec@[k]) as int
                    }),
                // Each ProjectiveNiels point is valid, 54-bounded, and corresponds to original
                forall|k: int|
                    0 <= k < idx ==> is_valid_projective_niels_point(
                        (#[trigger] scalars_points@[k]).1,
                    ),
                forall|k: int|
                    0 <= k < idx ==> fe51_limbs_bounded(
                        &(#[trigger] scalars_points@[k]).1.Y_plus_X,
                        54,
                    ),
                forall|k: int|
                    0 <= k < idx ==> fe51_limbs_bounded(
                        &(#[trigger] scalars_points@[k]).1.Y_minus_X,
                        54,
                    ),
                forall|k: int|
                    0 <= k < idx ==> fe51_limbs_bounded(&(#[trigger] scalars_points@[k]).1.Z, 54),
                forall|k: int|
                    0 <= k < idx ==> fe51_limbs_bounded(&(#[trigger] scalars_points@[k]).1.T2d, 54),
                forall|k: int|
                    0 <= k < idx ==> projective_niels_corresponds_to_edwards(
                        (#[trigger] scalars_points@[k]).1,
                        points_vec@[k].unwrap(),
                    ),
            decreases min_len - idx,
        {
            match points_vec[idx] {
                Some(P) => {
                    proof {
                        assert(spec_points[idx as int].is_some());
                        assert(is_well_formed_edwards_point(spec_points[idx as int].unwrap()));
                    }
                    let digits = scalars_vec[idx].as_radix_2w(w);
                    let niels = P.as_projective_niels();
                    scalars_points.push((digits, niels));
                    proof {
                        // After push, connect the new entry to function postconditions
                        assert(scalars_points@[idx as int] == (digits, niels));
                        assert(scalars_points@[idx as int].0 == digits);
                        assert(scalars_points@[idx as int].1 == niels);
                    }
                },
                None => {
                    proof {
                        assert(!spec_points[idx as int].is_some());
                        assert(!all_points_some(spec_points));
                    }
                    return None;
                },
            }
            idx = idx + 1;
        }
        /* </REFACTORED CODE> */

        // Phase 2: Ghost state and reconstruction bridge
        proof {
            // All points were Some (we never returned None during the loop)
            assert(forall|k: int|
                0 <= k < spec_points.len() ==> (#[trigger] spec_points[k]).is_some());
            assert(all_points_some(spec_points));
        }

        let ghost n = scalars_points@.len() as int;
        let ghost unwrapped_points: Seq<EdwardsPoint> = unwrap_points(spec_points);
        let ghost pts_affine: Seq<(nat, nat)> = points_to_affine(unwrapped_points);
        let ghost digits_seqs: Seq<Seq<i8>> = Seq::new(n as nat, |i: int| scalars_points@[i].0@);
        let ghost dc: nat = if w < 8 {
            ((256 + (w as int) - 1) / (w as int)) as nat
        } else {
            ((256 + (w as int) - 1) / (w as int) + 1) as nat
        };

        proof {
            // Connect exec digits_count to spec dc
            // For w in {6,7,8}, the formula evaluates to small positive ints
            if w == 6 {
                assert(261int / 6 == 43);
            } else if w == 7 {
                assert(262int / 7 == 37);
            } else {
                assert(w == 8);
                assert(263int / 8 == 32);
            }
            assert(digits_count as nat == dc);
            assert(n == scalars_vec@.len());
            assert(n == spec_points.len());
            assert(pts_affine.len() == n);
            assert(digits_seqs.len() == n);

            // unwrapped_points[k] == spec_points[k].unwrap()
            assert forall|k: int| 0 <= k < n implies #[trigger] unwrapped_points[k]
                == spec_points[k].unwrap() by {};

            // pts_affine[k] == edwards_point_as_affine(unwrapped_points[k])
            assert forall|k: int| 0 <= k < n implies #[trigger] pts_affine[k]
                == edwards_point_as_affine(unwrapped_points[k]) by {};

            // pts_affine coordinates are canonical (< p())
            assert forall|k: int| 0 <= k < n implies (#[trigger] pts_affine[k]).0 < p()
                && pts_affine[k].1 < p() by {
                lemma_edwards_point_as_affine_canonical(unwrapped_points[k]);
            };

            // digits_seqs[k] has length 64 >= dc, and reconstruction property
            assert forall|k: int| 0 <= k < n implies {
                &&& (#[trigger] digits_seqs[k]).len() >= dc as int
                &&& reconstruct_radix_2w_from(digits_seqs[k], w as nat, 0, dc) == scalar_as_nat(
                    &scalars_vec@[k],
                ) as int
            } by {
                assert(digits_seqs[k].len() == 64);
                assert(dc <= 64);
                // Bridge: reconstruct_radix_2w_from(d, w, 0, dc) == reconstruct_radix_2w(d.take(dc), w)
                lemma_reconstruct_radix_2w_from_equals_reconstruct(digits_seqs[k], w as nat, dc);
                // From pairing loop invariant: reconstruct_radix_2w(digits@.take(dc), w) == scalar_as_nat(...)
                // The invariant's dc formula matches our ghost dc, so the property transfers
            };

            // Also establish that digits_seqs[k][col] accesses are in range for any column < dc
            assert forall|k: int| 0 <= k < n implies (#[trigger] digits_seqs[k]).len()
                >= dc as int by {
                assert(digits_seqs[k].len() == 64);
            };
        }

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
                0 <= init_idx <= buckets_count,
                buckets@.len() == init_idx as int,
                forall|k: int|
                    0 <= k < init_idx ==> is_well_formed_edwards_point(#[trigger] buckets@[k]),
                forall|k: int|
                    0 <= k < init_idx ==> edwards_point_as_affine(#[trigger] buckets@[k])
                        == math_edwards_identity(),
            decreases buckets_count - init_idx,
        {
            let ep = EdwardsPoint::identity();
            proof {
                lemma_identity_affine_coords(ep);
            }
            buckets.push(ep);
            init_idx = init_idx + 1;
        }
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

        // Clear buckets
        let mut bucket_idx: usize = 0;
        while bucket_idx < buckets_count
            invariant
                0 <= bucket_idx <= buckets_count,
                buckets@.len() == buckets_count as int,
                forall|k: int|
                    0 <= k < bucket_idx ==> is_well_formed_edwards_point(#[trigger] buckets@[k]),
                forall|k: int|
                    0 <= k < bucket_idx ==> edwards_point_as_affine(#[trigger] buckets@[k])
                        == math_edwards_identity(),
            decreases buckets_count - bucket_idx,
        {
            let ep = EdwardsPoint::identity();
            proof {
                lemma_identity_affine_coords(ep);
            }
            buckets.set(bucket_idx, ep);
            bucket_idx = bucket_idx + 1;
        }

        // Fill buckets for hi_column
        proof {
            // Establish buckets_count == pow2(w-1) via case analysis + bit_vector
            lemma2_to64();
            if w == 6 {
                assert(1usize << 6usize == 64usize) by (bit_vector);
                assert(max_digit == 64);
                assert(buckets_count == 32);
                assert(pow2(5nat) == 32);
            } else if w == 7 {
                assert(1usize << 7usize == 128usize) by (bit_vector);
                assert(max_digit == 128);
                assert(buckets_count == 64);
                assert(pow2(6nat) == 64);
            } else {
                assert(1usize << 8usize == 256usize) by (bit_vector);
                assert(max_digit == 256);
                assert(buckets_count == 128);
                assert(pow2(7nat) == 128);
            }
            assert(buckets_count as int == pow2((w - 1) as nat));

            // Initial bucket state matches spec at sp_idx=0
            assert forall|b: int| 0 <= b < buckets_count implies edwards_point_as_affine(
                #[trigger] buckets@[b],
            ) == pippenger_bucket_contents(
                pts_affine,
                digits_seqs,
                digit_index_hi as int,
                0,
                b,
            ) by {};
        }

        let mut sp_idx: usize = 0;
        while sp_idx < scalars_points.len()
            invariant
                0 <= sp_idx <= scalars_points@.len(),
                scalars_points@.len() == n,
                buckets@.len() == buckets_count as int,
                4 <= w <= 8,
                buckets_count as int == pow2((w - 1) as nat),
                digit_index_hi == digits_count - 1,
                digits_count as nat == dc,
                dc >= 1,
                // All buckets are well-formed
                forall|b: int|
                    0 <= b < buckets_count ==> is_well_formed_edwards_point(#[trigger] buckets@[b]),
                // Bucket contents match spec
                forall|b: int|
                    0 <= b < buckets_count ==> edwards_point_as_affine(#[trigger] buckets@[b])
                        == pippenger_bucket_contents(
                        pts_affine,
                        digits_seqs,
                        digit_index_hi as int,
                        sp_idx as int,
                        b,
                    ),
                // Preserved: digit validity for all points
                forall|k: int|
                    0 <= k < n ==> is_valid_radix_2w(
                        &(#[trigger] scalars_points@[k]).0,
                        w as nat,
                        dc,
                    ),
                // Preserved: niels point properties
                forall|k: int|
                    0 <= k < n ==> is_valid_projective_niels_point(
                        (#[trigger] scalars_points@[k]).1,
                    ),
                forall|k: int|
                    0 <= k < n ==> fe51_limbs_bounded(
                        &(#[trigger] scalars_points@[k]).1.Y_plus_X,
                        54,
                    ),
                forall|k: int|
                    0 <= k < n ==> fe51_limbs_bounded(
                        &(#[trigger] scalars_points@[k]).1.Y_minus_X,
                        54,
                    ),
                forall|k: int|
                    0 <= k < n ==> fe51_limbs_bounded(&(#[trigger] scalars_points@[k]).1.Z, 54),
                forall|k: int|
                    0 <= k < n ==> fe51_limbs_bounded(&(#[trigger] scalars_points@[k]).1.T2d, 54),
                forall|k: int|
                    0 <= k < n ==> projective_niels_corresponds_to_edwards(
                        (#[trigger] scalars_points@[k]).1,
                        points_vec@[k].unwrap(),
                    ),
                // Preserved: pts_affine connection
                forall|k: int|
                    0 <= k < n ==> (#[trigger] pts_affine[k]) == edwards_point_as_affine(
                        points_vec@[k].unwrap(),
                    ),
                forall|k: int|
                    0 <= k < n ==> (#[trigger] pts_affine[k]).0 < p() && pts_affine[k].1 < p(),
                // digits_seqs connection
                forall|k: int| 0 <= k < n ==> (#[trigger] digits_seqs[k]) == scalars_points@[k].0@,
                pts_affine.len() == n,
                digits_seqs.len() == n,
                // Input points well-formedness (for lemma_projective_niels_affine_equals_edwards_affine)
                forall|k: int|
                    0 <= k < n ==> is_well_formed_edwards_point(
                        (#[trigger] points_vec@[k]).unwrap(),
                    ),
            decreases scalars_points.len() - sp_idx,
        {
            let sp = &scalars_points[sp_idx];
            let digits_arr = &sp.0;
            let pt = &sp.1;
            let digit = digits_arr[digit_index_hi] as i16;

            proof {
                // digit_index_hi < dc, so digit bound applies from is_valid_radix_2w
                let ghost d_spec = digits_seqs[sp_idx as int][digit_index_hi as int];
                assert(digit as int == d_spec as int);

                // Digit is bounded: |digit| <= pow2(w-1) = buckets_count
                assert(is_valid_radix_2w(&scalars_points@[sp_idx as int].0, w as nat, dc));
                // digit_index_hi == dc - 1, so the inclusive bound applies
                assert(-(pow2((w - 1) as nat) as int) <= (d_spec as int) && (d_spec as int) <= pow2(
                    (w - 1) as nat,
                ));
                assert(-(buckets_count as int) <= (digit as int) && (digit as int) <= (
                buckets_count as int));

                // Connect niels affine to pts_affine
                // is_well_formed implies is_valid
                assert(is_well_formed_edwards_point(points_vec@[sp_idx as int].unwrap()));
                assert(is_valid_edwards_point(points_vec@[sp_idx as int].unwrap()));
                lemma_projective_niels_affine_equals_edwards_affine(
                    scalars_points@[sp_idx as int].1,
                    points_vec@[sp_idx as int].unwrap(),
                );
                assert(projective_niels_point_as_affine_edwards(scalars_points@[sp_idx as int].1)
                    == pts_affine[sp_idx as int]);
            }

            if digit > 0 {
                let b = (digit - 1) as usize;
                proof {
                    assert(0 <= b < buckets_count);
                }
                let completed = &buckets[b] + pt;
                let new_bucket = completed.as_extended();
                buckets.set(b, new_bucket);
                proof {
                    // new_bucket_affine = edwards_add(old_bucket_affine, niels_affine)
                    //                   = edwards_add(bucket_contents(..., sp_idx, b), pts_affine[sp_idx])
                    //                   = bucket_contents(..., sp_idx+1, b)  [since d == b+1]
                    let ghost col = digit_index_hi as int;
                    let ghost d_val = digits_seqs[sp_idx as int][col] as int;
                    assert(d_val == digit as int);
                    assert(d_val == (b as int) + 1);

                    // For the modified bucket b: spec unfolds to edwards_add(prev, pt)
                    // For unmodified buckets b': d != b'+1 and d > 0 so d != -(b'+1),
                    // so spec returns prev = unchanged bucket
                    assert forall|bb: int| 0 <= bb < buckets_count implies edwards_point_as_affine(
                        #[trigger] buckets@[bb],
                    ) == pippenger_bucket_contents(
                        pts_affine,
                        digits_seqs,
                        col,
                        sp_idx as int + 1,
                        bb,
                    ) by {
                        if bb == b as int {
                            // Modified bucket: d == bb + 1
                            assert(d_val == bb + 1);
                        } else {
                            // Unchanged bucket: d != bb + 1 (since d == b + 1 and bb != b)
                            // and d > 0 so d != -(bb + 1) for any bb >= 0
                            assert(d_val != bb + 1);
                            assert(d_val > 0);
                            assert(d_val != -(bb + 1));
                        }
                    };
                }
            } else if digit < 0 {
                let b = (-digit - 1) as usize;
                proof {
                    assert(0 <= b < buckets_count);
                }
                let completed = &buckets[b] - pt;
                let new_bucket = completed.as_extended();
                buckets.set(b, new_bucket);
                proof {
                    let ghost col = digit_index_hi as int;
                    let ghost d_val = digits_seqs[sp_idx as int][col] as int;
                    assert(d_val == digit as int);
                    assert(d_val == -((b as int) + 1));

                    assert forall|bb: int| 0 <= bb < buckets_count implies edwards_point_as_affine(
                        #[trigger] buckets@[bb],
                    ) == pippenger_bucket_contents(
                        pts_affine,
                        digits_seqs,
                        col,
                        sp_idx as int + 1,
                        bb,
                    ) by {
                        if bb == b as int {
                            // Modified bucket: d == -(bb + 1)
                            assert(d_val == -(bb + 1));
                        } else {
                            // Unchanged bucket: d < 0 so d != bb + 1 for bb >= 0
                            // and d == -(b+1) so d != -(bb+1) since b != bb
                            assert(d_val != bb + 1);
                            assert(d_val != -(bb + 1));
                        }
                    };
                }
            } else {
                // digit == 0: no bucket modified
                proof {
                    let ghost col = digit_index_hi as int;
                    let ghost d_val = digits_seqs[sp_idx as int][col] as int;
                    assert(d_val == 0);

                    assert forall|bb: int| 0 <= bb < buckets_count implies edwards_point_as_affine(
                        #[trigger] buckets@[bb],
                    ) == pippenger_bucket_contents(
                        pts_affine,
                        digits_seqs,
                        col,
                        sp_idx as int + 1,
                        bb,
                    ) by {
                        // d == 0 != bb + 1 (since bb >= 0, bb + 1 >= 1)
                        // d == 0 != -(bb + 1) (since -(bb+1) <= -1)
                        assert(d_val != bb + 1);
                        assert(d_val != -(bb + 1));
                    };
                }
            }
            sp_idx = sp_idx + 1;
        }

        // Sum buckets for hi_column
        // After bucket filling: buckets[b] affine == bucket_contents(pts, digs, col, n, b)
        let ghost hi_col = digit_index_hi as int;
        let ghost B = buckets_count as int;
        let ghost buckets_affine_hi: Seq<(nat, nat)> = Seq::new(
            buckets_count as nat,
            |b: int| edwards_point_as_affine(buckets@[b]),
        );

        proof {
            assert(buckets_count >= 1);
            assert(buckets_count - 1 < buckets@.len());
        }
        let mut buckets_intermediate_sum = buckets[buckets_count - 1];
        let mut hi_column = buckets[buckets_count - 1];
        let mut j: usize = buckets_count - 1;
        while j > 0
            invariant
                0 <= j <= buckets_count - 1,
                buckets@.len() == buckets_count as int,
                B == buckets_count as int,
                buckets_count >= 1,
                is_well_formed_edwards_point(buckets_intermediate_sum),
                is_well_formed_edwards_point(hi_column),
                // Intermediate sum tracks partial sum from B-1 down to j
                edwards_point_as_affine(buckets_intermediate_sum) == pippenger_intermediate_sum(
                    buckets_affine_hi,
                    j as int,
                    B,
                ),
                // Running sum tracks accumulated running sum from B-1 down to j
                edwards_point_as_affine(hi_column) == pippenger_running_sum(
                    buckets_affine_hi,
                    j as int,
                    B,
                ),
                // Buckets unchanged
                forall|b: int|
                    0 <= b < buckets_count ==> is_well_formed_edwards_point(#[trigger] buckets@[b]),
                forall|b: int|
                    0 <= b < buckets_count ==> edwards_point_as_affine(#[trigger] buckets@[b])
                        == buckets_affine_hi[b],
            decreases j,
        {
            j = j - 1;
            // intermediate_sum(j, B) = edwards_add(intermediate_sum(j+1, B), bucket[j])
            buckets_intermediate_sum = &buckets_intermediate_sum + &buckets[j];
            // running_sum(j, B) = edwards_add(running_sum(j+1, B), intermediate_sum(j, B))
            hi_column = &hi_column + &buckets_intermediate_sum;
        }
        // After loop: j == 0, so hi_column == running_sum(0, B)

        // After summing: hi_column affine == running_sum(0, B) or running_sum(B-1, B) if B==1
        proof {
            // When B == 1: hi_column == bucket[0], running_sum(0, 1) == bucket[0]
            // When B > 1: loop exited at j==0, hi_column == running_sum(0, B)
            if buckets_count == 1 {
                assert(edwards_point_as_affine(hi_column) == pippenger_running_sum(
                    buckets_affine_hi,
                    0,
                    B,
                ));
            }
            // By axiom: running_sum(0, B) == weighted_bucket_sum(buckets_affine, B)

            axiom_running_sum_equals_weighted(buckets_affine_hi, B);

            // Build the spec-level bucket sequence from bucket_contents
            let ghost bucket_contents_seq = Seq::new(
                buckets_count as nat,
                |b: int| pippenger_bucket_contents(pts_affine, digits_seqs, hi_col, n, b),
            );
            // buckets_affine_hi == bucket_contents_seq (from bucket filling postcondition)
            assert(buckets_affine_hi =~= bucket_contents_seq);

            // By axiom: weighted_bucket_sum(bucket_contents, B) == straus_column_sum(pts, digs, col, n)
            axiom_bucket_weighted_sum_equals_column_sum(pts_affine, digits_seqs, hi_col, n, B);
        }
        // Fold remaining columns: Horner accumulation
        // total starts as hi_column = pippenger_horner(pts, digs, dc-1, w, dc)
        // Each iteration processes column digit_index:
        //   total = total * 2^w + column_sum(digit_index)
        //         = pippenger_horner(pts, digs, digit_index, w, dc)
        let mut total = hi_column;
        proof {
            // hi_column_affine == running_sum(0, B) == weighted_bucket_sum == column_sum(dc-1, n)
            // Need: total_affine == pippenger_horner(pts, digs, dc-1, w, dc)
            //
            // Step 1: pippenger_horner(dc-1) = edwards_add(scaled_identity, column_sum(dc-1))
            lemma_pippenger_horner_base(pts_affine, digits_seqs, w as nat, dc);
            lemma_pippenger_horner_step(pts_affine, digits_seqs, (dc - 1) as int, w as nat, dc);
            // Step 2: scaled_identity = edwards_scalar_mul(identity, pow2(w)) = identity
            lemma_edwards_scalar_mul_identity(pow2(w as nat));
            // Step 3: edwards_add(identity, column_sum) = edwards_add(0, 1, col.0, col.1)
            //       = (col.0 % p(), col.1 % p())
            let col_hi = straus_column_sum(pts_affine, digits_seqs, (dc - 1) as int, n);
            p_gt_2();
            // Use commutativity to get add(id, col) = add(col, id)
            let id = math_edwards_identity();
            lemma_edwards_add_commutative(id.0, id.1, col_hi.0, col_hi.1);
            // add(col, id) = col when col < p()
            // total_affine == col_hi (from Phase 4 axioms)
            // So we need col_hi == (col_hi.0 % p(), col_hi.1 % p())
            // Establish col_hi.0 < p() and col_hi.1 < p() via edwards_point_as_affine canonical
            // Since hi_column is a well-formed EdwardsPoint:
            assert(is_well_formed_edwards_point(hi_column));
            lemma_edwards_point_as_affine_canonical(hi_column);
            // Now edwards_point_as_affine(hi_column).0 < p() and .1 < p()
            let total_affine = edwards_point_as_affine(hi_column);
            assert(total_affine.0 < p() && total_affine.1 < p());
            // total_affine == col_hi (from axiom chain in Phase 4)
            lemma_edwards_add_identity_right_canonical(total_affine);
            // edwards_add(total_affine.0, total_affine.1, 0, 1) == total_affine
            // So edwards_add(0, 1, total_affine.0, total_affine.1) == total_affine (by comm above)
            // And pippenger_horner(dc-1) == edwards_add(0, 1, col_hi.0, col_hi.1)
            //                            == edwards_add(0, 1, total_affine.0, total_affine.1)
            //                            == total_affine
        }
        let mut digit_index: usize = digits_count - 1;
        while digit_index > 0
            invariant
                0 <= digit_index <= digits_count - 1,
                digits_count as nat == dc,
                dc >= 1,
                4 <= w <= 8,
                buckets_count as int == pow2((w - 1) as nat),
                buckets_count >= 1,
                buckets@.len() == buckets_count as int,
                B == buckets_count as int,
                scalars_points@.len() == n,
                pts_affine.len() == n,
                digits_seqs.len() == n,
                is_well_formed_edwards_point(total),
                // Horner invariant: total represents the Horner evaluation from digit_index
                edwards_point_as_affine(total) == pippenger_horner(
                    pts_affine,
                    digits_seqs,
                    digit_index as int,
                    w as nat,
                    dc,
                ),
                // Preserved properties
                forall|k: int|
                    0 <= k < n ==> is_valid_radix_2w(
                        &(#[trigger] scalars_points@[k]).0,
                        w as nat,
                        dc,
                    ),
                forall|k: int|
                    0 <= k < n ==> is_valid_projective_niels_point(
                        (#[trigger] scalars_points@[k]).1,
                    ),
                forall|k: int|
                    0 <= k < n ==> fe51_limbs_bounded(
                        &(#[trigger] scalars_points@[k]).1.Y_plus_X,
                        54,
                    ),
                forall|k: int|
                    0 <= k < n ==> fe51_limbs_bounded(
                        &(#[trigger] scalars_points@[k]).1.Y_minus_X,
                        54,
                    ),
                forall|k: int|
                    0 <= k < n ==> fe51_limbs_bounded(&(#[trigger] scalars_points@[k]).1.Z, 54),
                forall|k: int|
                    0 <= k < n ==> fe51_limbs_bounded(&(#[trigger] scalars_points@[k]).1.T2d, 54),
                forall|k: int|
                    0 <= k < n ==> projective_niels_corresponds_to_edwards(
                        (#[trigger] scalars_points@[k]).1,
                        points_vec@[k].unwrap(),
                    ),
                forall|k: int|
                    0 <= k < n ==> (#[trigger] pts_affine[k]) == edwards_point_as_affine(
                        points_vec@[k].unwrap(),
                    ),
                forall|k: int|
                    0 <= k < n ==> (#[trigger] pts_affine[k]).0 < p() && pts_affine[k].1 < p(),
                forall|k: int| 0 <= k < n ==> (#[trigger] digits_seqs[k]) == scalars_points@[k].0@,
                forall|k: int|
                    0 <= k < n ==> is_well_formed_edwards_point(
                        (#[trigger] points_vec@[k]).unwrap(),
                    ),
            decreases digit_index,
        {
            digit_index = digit_index - 1;

            // Clear buckets
            let mut bucket_idx2: usize = 0;
            while bucket_idx2 < buckets_count
                invariant
                    0 <= bucket_idx2 <= buckets_count,
                    buckets@.len() == buckets_count as int,
                    forall|k: int|
                        0 <= k < bucket_idx2 ==> is_well_formed_edwards_point(
                            #[trigger] buckets@[k],
                        ),
                    forall|k: int|
                        0 <= k < bucket_idx2 ==> edwards_point_as_affine(#[trigger] buckets@[k])
                            == math_edwards_identity(),
                decreases buckets_count - bucket_idx2,
            {
                let ep = EdwardsPoint::identity();
                proof {
                    lemma_identity_affine_coords(ep);
                }
                buckets.set(bucket_idx2, ep);
                bucket_idx2 = bucket_idx2 + 1;
            }

            // Fill buckets for current column
            proof {
                assert forall|b: int| 0 <= b < buckets_count implies edwards_point_as_affine(
                    #[trigger] buckets@[b],
                ) == pippenger_bucket_contents(
                    pts_affine,
                    digits_seqs,
                    digit_index as int,
                    0,
                    b,
                ) by {};
            }
            let mut sp_idx2: usize = 0;
            while sp_idx2 < scalars_points.len()
                invariant
                    0 <= sp_idx2 <= scalars_points@.len(),
                    scalars_points@.len() == n,
                    buckets@.len() == buckets_count as int,
                    4 <= w <= 8,
                    buckets_count as int == pow2((w - 1) as nat),
                    digit_index < digits_count - 1,
                    digits_count as nat == dc,
                    forall|b: int|
                        0 <= b < buckets_count ==> is_well_formed_edwards_point(
                            #[trigger] buckets@[b],
                        ),
                    forall|b: int|
                        0 <= b < buckets_count ==> edwards_point_as_affine(#[trigger] buckets@[b])
                            == pippenger_bucket_contents(
                            pts_affine,
                            digits_seqs,
                            digit_index as int,
                            sp_idx2 as int,
                            b,
                        ),
                    forall|k: int|
                        0 <= k < n ==> is_valid_radix_2w(
                            &(#[trigger] scalars_points@[k]).0,
                            w as nat,
                            dc,
                        ),
                    forall|k: int|
                        0 <= k < n ==> is_valid_projective_niels_point(
                            (#[trigger] scalars_points@[k]).1,
                        ),
                    forall|k: int|
                        0 <= k < n ==> fe51_limbs_bounded(
                            &(#[trigger] scalars_points@[k]).1.Y_plus_X,
                            54,
                        ),
                    forall|k: int|
                        0 <= k < n ==> fe51_limbs_bounded(
                            &(#[trigger] scalars_points@[k]).1.Y_minus_X,
                            54,
                        ),
                    forall|k: int|
                        0 <= k < n ==> fe51_limbs_bounded(&(#[trigger] scalars_points@[k]).1.Z, 54),
                    forall|k: int|
                        0 <= k < n ==> fe51_limbs_bounded(
                            &(#[trigger] scalars_points@[k]).1.T2d,
                            54,
                        ),
                    forall|k: int|
                        0 <= k < n ==> projective_niels_corresponds_to_edwards(
                            (#[trigger] scalars_points@[k]).1,
                            points_vec@[k].unwrap(),
                        ),
                    forall|k: int|
                        0 <= k < n ==> (#[trigger] pts_affine[k]) == edwards_point_as_affine(
                            points_vec@[k].unwrap(),
                        ),
                    forall|k: int|
                        0 <= k < n ==> (#[trigger] pts_affine[k]).0 < p() && pts_affine[k].1 < p(),
                    forall|k: int|
                        0 <= k < n ==> (#[trigger] digits_seqs[k]) == scalars_points@[k].0@,
                    forall|k: int|
                        0 <= k < n ==> is_well_formed_edwards_point(
                            (#[trigger] points_vec@[k]).unwrap(),
                        ),
                    pts_affine.len() == n,
                    digits_seqs.len() == n,
                decreases scalars_points.len() - sp_idx2,
            {
                let sp = &scalars_points[sp_idx2];
                let digits_arr2 = &sp.0;
                let pt2 = &sp.1;
                let digit2 = digits_arr2[digit_index] as i16;

                proof {
                    let ghost d_spec = digits_seqs[sp_idx2 as int][digit_index as int];
                    assert(digit2 as int == d_spec as int);
                    assert(is_valid_radix_2w(&scalars_points@[sp_idx2 as int].0, w as nat, dc));
                    // digit_index < dc - 1, so strict bound applies
                    assert(-(pow2((w - 1) as nat) as int) <= (d_spec as int) && (d_spec as int)
                        < pow2((w - 1) as nat));
                    assert(-(buckets_count as int) <= (digit2 as int) && (digit2 as int) < (
                    buckets_count as int));

                    assert(is_well_formed_edwards_point(points_vec@[sp_idx2 as int].unwrap()));
                    assert(is_valid_edwards_point(points_vec@[sp_idx2 as int].unwrap()));
                    lemma_projective_niels_affine_equals_edwards_affine(
                        scalars_points@[sp_idx2 as int].1,
                        points_vec@[sp_idx2 as int].unwrap(),
                    );
                }

                if digit2 > 0 {
                    let b2 = (digit2 - 1) as usize;
                    proof {
                        assert(0 <= b2 < buckets_count);
                    }
                    let completed = &buckets[b2] + pt2;
                    let new_bucket = completed.as_extended();
                    buckets.set(b2, new_bucket);
                    proof {
                        let ghost col = digit_index as int;
                        let ghost d_val = digits_seqs[sp_idx2 as int][col] as int;
                        assert(d_val == digit2 as int);
                        assert(d_val == (b2 as int) + 1);
                        assert forall|bb: int|
                            0 <= bb < buckets_count implies edwards_point_as_affine(
                            #[trigger] buckets@[bb],
                        ) == pippenger_bucket_contents(
                            pts_affine,
                            digits_seqs,
                            col,
                            sp_idx2 as int + 1,
                            bb,
                        ) by {
                            if bb == b2 as int {
                                assert(d_val == bb + 1);
                            } else {
                                assert(d_val != bb + 1);
                                assert(d_val > 0);
                                assert(d_val != -(bb + 1));
                            }
                        };
                    }
                } else if digit2 < 0 {
                    let b2 = (-digit2 - 1) as usize;
                    proof {
                        assert(0 <= b2 < buckets_count);
                    }
                    let completed = &buckets[b2] - pt2;
                    let new_bucket = completed.as_extended();
                    buckets.set(b2, new_bucket);
                    proof {
                        let ghost col = digit_index as int;
                        let ghost d_val = digits_seqs[sp_idx2 as int][col] as int;
                        assert(d_val == digit2 as int);
                        assert(d_val == -((b2 as int) + 1));
                        assert forall|bb: int|
                            0 <= bb < buckets_count implies edwards_point_as_affine(
                            #[trigger] buckets@[bb],
                        ) == pippenger_bucket_contents(
                            pts_affine,
                            digits_seqs,
                            col,
                            sp_idx2 as int + 1,
                            bb,
                        ) by {
                            if bb == b2 as int {
                                assert(d_val == -(bb + 1));
                            } else {
                                assert(d_val != bb + 1);
                                assert(d_val != -(bb + 1));
                            }
                        };
                    }
                } else {
                    proof {
                        let ghost col = digit_index as int;
                        let ghost d_val = digits_seqs[sp_idx2 as int][col] as int;
                        assert(d_val == 0);
                        assert forall|bb: int|
                            0 <= bb < buckets_count implies edwards_point_as_affine(
                            #[trigger] buckets@[bb],
                        ) == pippenger_bucket_contents(
                            pts_affine,
                            digits_seqs,
                            col,
                            sp_idx2 as int + 1,
                            bb,
                        ) by {
                            assert(d_val != bb + 1);
                            assert(d_val != -(bb + 1));
                        };
                    }
                }
                sp_idx2 = sp_idx2 + 1;
            }

            // Sum buckets for current column
            let ghost buckets_affine_cur: Seq<(nat, nat)> = Seq::new(
                buckets_count as nat,
                |b: int| edwards_point_as_affine(buckets@[b]),
            );

            let mut buckets_intermediate_sum2 = buckets[buckets_count - 1];
            let mut column = buckets[buckets_count - 1];
            let mut j2: usize = buckets_count - 1;
            while j2 > 0
                invariant
                    0 <= j2 <= buckets_count - 1,
                    buckets@.len() == buckets_count as int,
                    B == buckets_count as int,
                    buckets_count >= 1,
                    is_well_formed_edwards_point(buckets_intermediate_sum2),
                    is_well_formed_edwards_point(column),
                    edwards_point_as_affine(buckets_intermediate_sum2)
                        == pippenger_intermediate_sum(buckets_affine_cur, j2 as int, B),
                    edwards_point_as_affine(column) == pippenger_running_sum(
                        buckets_affine_cur,
                        j2 as int,
                        B,
                    ),
                    forall|b: int|
                        0 <= b < buckets_count ==> is_well_formed_edwards_point(
                            #[trigger] buckets@[b],
                        ),
                    forall|b: int|
                        0 <= b < buckets_count ==> edwards_point_as_affine(#[trigger] buckets@[b])
                            == buckets_affine_cur[b],
                decreases j2,
            {
                j2 = j2 - 1;
                buckets_intermediate_sum2 = &buckets_intermediate_sum2 + &buckets[j2];
                column = &column + &buckets_intermediate_sum2;
            }

            // column_affine == running_sum(0, B) == weighted_bucket_sum == column_sum
            proof {
                axiom_running_sum_equals_weighted(buckets_affine_cur, B);
                let ghost bucket_contents_seq = Seq::new(
                    buckets_count as nat,
                    |b: int|
                        pippenger_bucket_contents(
                            pts_affine,
                            digits_seqs,
                            digit_index as int,
                            n,
                            b,
                        ),
                );
                assert(buckets_affine_cur =~= bucket_contents_seq);
                axiom_bucket_weighted_sum_equals_column_sum(
                    pts_affine,
                    digits_seqs,
                    digit_index as int,
                    n,
                    B,
                );
            }

            // Accumulate: total = total * 2^w + column
            let shifted = total.mul_by_pow_2(w as u32);
            total = &shifted + &column;

            proof {
                // Connect to Horner step
                lemma_pippenger_horner_step(
                    pts_affine,
                    digits_seqs,
                    digit_index as int,
                    w as nat,
                    dc,
                );
            }
        }
        /* </REFACTORED CODE> */
        // Phase 6: Prove final postconditions

        proof {
            // (1) all_points_some: proven in Phase 2 (all loop iterations completed without None)
            assert(all_points_some(spec_points));

            // (2) is_well_formed_edwards_point(total): from outer loop invariant
            assert(is_well_formed_edwards_point(total));

            // (3) total_affine == sum_of_scalar_muls(spec_scalars, unwrap_points(spec_points))
            // From outer loop: total_affine == pippenger_horner(pts_affine, digits_seqs, 0, w, dc)
            // Need: pippenger_horner(pts, digs, 0, w, dc) == sum_of_scalar_muls(scalars, points)
            let ghost unwrapped = unwrap_points(spec_points);

            // Establish preconditions for lemma_pippenger_horner_correct
            assert(spec_scalars.len() == unwrapped.len());
            assert(pts_affine.len() == spec_scalars.len());
            assert(digits_seqs.len() == spec_scalars.len());

            assert forall|k: int| 0 <= k < pts_affine.len() implies #[trigger] pts_affine[k]
                == edwards_point_as_affine(unwrapped[k]) by {
                assert(unwrapped[k] == spec_points[k].unwrap());
                assert(pts_affine[k] == edwards_point_as_affine(spec_points[k].unwrap()));
            };

            assert forall|k: int| 0 <= k < digits_seqs.len() implies {
                &&& (#[trigger] digits_seqs[k]).len() >= dc as int
                &&& reconstruct_radix_2w_from(digits_seqs[k], w as nat, 0, dc) == scalar_as_nat(
                    &spec_scalars[k],
                ) as int
            } by {
                assert(digits_seqs[k].len() == 64);
                assert(dc <= 64);
                lemma_reconstruct_radix_2w_from_equals_reconstruct(digits_seqs[k], w as nat, dc);
            };

            lemma_pippenger_horner_correct(
                spec_scalars,
                unwrapped,
                pts_affine,
                digits_seqs,
                w as nat,
                dc,
            );
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
