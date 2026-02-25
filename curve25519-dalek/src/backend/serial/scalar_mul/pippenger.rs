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
use vstd::arithmetic::div_mod::lemma_small_mod;
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
 * VERIFIED PIPPENGER MULTISCALAR MULTIPLICATION
 * ==============================================
 *
 * Verus limitations addressed in this _verus version:
 * - IntoIterator with I::Item projections -> use Iterator bounds instead
 * - Iterator adapters (map, zip) with closures -> use explicit while loops
 * - Op-assignment (+=, -=) on EdwardsPoint -> use explicit a = a + b
 *
 * TESTING: `scalar_mul_tests.rs` contains tests that generate random scalars and points,
 * run both original and _verus implementations, and assert equality of results.
 * This is evidence of functional equivalence between the original and refactored versions:
 *     forall scalars s, points p: optional_multiscalar_mul(s, p) == optional_multiscalar_mul_verus(s, p)
 */
impl Pippenger {
    /// Initialize `count` buckets with the identity point.
    /// Replaces: `(0..count).map(|_| EdwardsPoint::identity()).collect()`
    fn init_buckets(count: usize) -> (buckets: Vec<EdwardsPoint>)
        requires
            count >= 1,
        ensures
            buckets@.len() == count as int,
            forall|k: int| 0 <= k < count ==> is_well_formed_edwards_point(#[trigger] buckets@[k]),
            forall|k: int|
                0 <= k < count ==> edwards_point_as_affine(#[trigger] buckets@[k])
                    == edwards_identity(),
    {
        use crate::traits::Identity;
        let mut buckets: Vec<EdwardsPoint> = Vec::new();
        let mut i: usize = 0;
        while i < count
            invariant
                0 <= i <= count,
                buckets@.len() == i as int,
                forall|k: int| 0 <= k < i ==> is_well_formed_edwards_point(#[trigger] buckets@[k]),
                forall|k: int|
                    0 <= k < i ==> edwards_point_as_affine(#[trigger] buckets@[k])
                        == edwards_identity(),
            decreases count - i,
        {
            let ep = EdwardsPoint::identity();
            proof {
                lemma_identity_affine_coords(ep);
            }
            buckets.push(ep);
            i = i + 1;
        }
        buckets
    }

    /// Process one digit column: clear buckets, fill by digit sign, compute weighted bucket sum.
    /// This is the Verus equivalent of the upstream closure in `columns.rev().map(|digit_index| { ... })`.
    fn process_column(
        buckets: &mut Vec<EdwardsPoint>,
        scalars_points: &Vec<([i8; 64], ProjectiveNielsPoint)>,
        digit_index: usize,
        w: usize,
        buckets_count: usize,
    ) -> (column: EdwardsPoint)
        requires
            pippenger_input_valid(
                scalars_points@,
                sp_points_affine(scalars_points@),
                sp_digits_seqs(scalars_points@),
                w as nat,
                sp_digit_count(w as nat),
            ),
            old(buckets)@.len() == buckets_count as int,
            buckets_count as int == pow2((w - 1) as nat),
            buckets_count >= 1,
            4 <= w <= 8,
            digit_index < sp_digit_count(w as nat),
            sp_digit_count(w as nat) >= 1,
            sp_digit_count(w as nat) <= 64,
        ensures
            is_well_formed_edwards_point(column),
            edwards_point_as_affine(column) == straus_column_sum(
                sp_points_affine(scalars_points@),
                sp_digits_seqs(scalars_points@),
                digit_index as int,
                scalars_points@.len() as int,
            ),
            buckets@.len() == buckets_count as int,
    {
        use crate::traits::Identity;

        // Derive ghost variables from runtime arguments (no Ghost params needed)
        let ghost pts_affine = sp_points_affine(scalars_points@);
        let ghost digits_seqs = sp_digits_seqs(scalars_points@);
        let ghost dc = sp_digit_count(w as nat);
        let ghost n_ghost: int = scalars_points@.len() as int;
        let ghost B = buckets_count as int;

        // ---- Phase 1: Clear buckets to identity ----
        let mut bucket_idx: usize = 0;
        while bucket_idx < buckets_count
            invariant
                0 <= bucket_idx <= buckets_count,
                buckets@.len() == buckets_count as int,
                forall|k: int|
                    0 <= k < bucket_idx ==> is_well_formed_edwards_point(#[trigger] buckets@[k]),
                forall|k: int|
                    0 <= k < bucket_idx ==> edwards_point_as_affine(#[trigger] buckets@[k])
                        == edwards_identity(),
            decreases buckets_count - bucket_idx,
        {
            let ep = EdwardsPoint::identity();
            proof {
                lemma_identity_affine_coords(ep);
            }
            buckets.set(bucket_idx, ep);
            bucket_idx = bucket_idx + 1;
        }

        // ---- Phase 2: Fill buckets by digit sign ----
        proof {
            assert forall|b: int| 0 <= b < buckets_count implies edwards_point_as_affine(
                #[trigger] buckets@[b],
            ) == pippenger_bucket_contents(pts_affine, digits_seqs, digit_index as int, 0, b) by {};
        }

        let mut sp_idx: usize = 0;
        while sp_idx < scalars_points.len()
            invariant
                0 <= sp_idx <= scalars_points@.len(),
                buckets@.len() == buckets_count as int,
                4 <= w <= 8,
                buckets_count as int == pow2((w - 1) as nat),
                digit_index < dc,
                dc >= 1,
                dc <= 64,
                forall|b: int|
                    0 <= b < buckets_count ==> is_well_formed_edwards_point(#[trigger] buckets@[b]),
                forall|b: int|
                    0 <= b < buckets_count ==> edwards_point_as_affine(#[trigger] buckets@[b])
                        == pippenger_bucket_contents(
                        pts_affine,
                        digits_seqs,
                        digit_index as int,
                        sp_idx as int,
                        b,
                    ),
                pippenger_input_valid(scalars_points@, pts_affine, digits_seqs, w as nat, dc),
            decreases scalars_points.len() - sp_idx,
        {
            let sp = &scalars_points[sp_idx];
            let digits_arr = &sp.0;
            let pt = &sp.1;
            let digit = digits_arr[digit_index] as i16;

            proof {
                let ghost d_spec = digits_seqs[sp_idx as int][digit_index as int];
                assert(digit as int == d_spec as int);
                assert(is_valid_radix_2w(&scalars_points@[sp_idx as int].0, w as nat, dc));
                assert(-(pow2((w - 1) as nat) as int) <= (d_spec as int) && (d_spec as int) <= pow2(
                    (w - 1) as nat,
                ));
                assert(-(buckets_count as int) <= (digit as int) && (digit as int) <= (
                buckets_count as int));
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
                    let ghost col = digit_index as int;
                    let ghost d_val = digits_seqs[sp_idx as int][col] as int;
                    assert(d_val == digit as int);
                    assert(d_val == (b as int) + 1);

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
                            assert(d_val == bb + 1);
                        } else {
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
                    let ghost col = digit_index as int;
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
                            assert(d_val == -(bb + 1));
                        } else {
                            assert(d_val != bb + 1);
                            assert(d_val != -(bb + 1));
                        }
                    };
                }
            } else {
                // digit == 0: no bucket modified
                proof {
                    let ghost col = digit_index as int;
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
                        assert(d_val != bb + 1);
                        assert(d_val != -(bb + 1));
                    };
                }
            }
            sp_idx = sp_idx + 1;
        }

        // ---- Phase 3: Sum buckets via intermediate-sum trick ----
        let ghost buckets_affine: Seq<(nat, nat)> = Seq::new(
            buckets_count as nat,
            |b: int| edwards_point_as_affine(buckets@[b]),
        );

        let mut buckets_intermediate_sum = buckets[buckets_count - 1];
        let mut column = buckets[buckets_count - 1];
        let mut j: usize = buckets_count - 1;
        while j > 0
            invariant
                0 <= j <= buckets_count - 1,
                buckets@.len() == buckets_count as int,
                B == buckets_count as int,
                buckets_count >= 1,
                is_well_formed_edwards_point(buckets_intermediate_sum),
                is_well_formed_edwards_point(column),
                edwards_point_as_affine(buckets_intermediate_sum) == pippenger_intermediate_sum(
                    buckets_affine,
                    j as int,
                    B,
                ),
                edwards_point_as_affine(column) == pippenger_running_sum(
                    buckets_affine,
                    j as int,
                    B,
                ),
                forall|b: int|
                    0 <= b < buckets_count ==> is_well_formed_edwards_point(#[trigger] buckets@[b]),
                forall|b: int|
                    0 <= b < buckets_count ==> edwards_point_as_affine(#[trigger] buckets@[b])
                        == buckets_affine[b],
            decreases j,
        {
            j = j - 1;
            buckets_intermediate_sum = &buckets_intermediate_sum + &buckets[j];
            column = &column + &buckets_intermediate_sum;
        }

        // Connect column to straus_column_sum via lemma chain
        proof {
            assert forall|b: int| 0 <= b < B implies (#[trigger] buckets_affine[b]).0 < p()
                && buckets_affine[b].1 < p() by {
                lemma_edwards_point_as_affine_canonical(buckets@[b]);
            };

            lemma_running_sum_equals_weighted(buckets_affine, B);

            let ghost bucket_contents_seq = Seq::new(
                buckets_count as nat,
                |b: int|
                    pippenger_bucket_contents(
                        pts_affine,
                        digits_seqs,
                        digit_index as int,
                        n_ghost,
                        b,
                    ),
            );
            assert(buckets_affine =~= bucket_contents_seq);

            assert forall|k: int| 0 <= k < n_ghost implies (#[trigger] pts_affine[k]).0 < p()
                && pts_affine[k].1 < p() by {};

            lemma_bucket_weighted_sum_equals_column_sum(
                pts_affine,
                digits_seqs,
                digit_index as int,
                n_ghost,
                B,
            );
        }

        column
    }

    /// Pair scalars (as radix-2^w digits) with points (as ProjectiveNiels). Returns None if any point is None.
    /// Replaces: `scalars.zip(points).map(|(s, maybe_p)| maybe_p.map(|p| (s.as_radix_2w(w), p.as_projective_niels()))).collect::<Option<Vec<_>>>()`
    fn pair_scalars_points(
        scalars_vec: &Vec<Scalar>,
        points_vec: &Vec<Option<EdwardsPoint>>,
        w: usize,
    ) -> (result: Option<Vec<([i8; 64], ProjectiveNielsPoint)>>)
        requires
            scalars_vec@.len() == points_vec@.len(),
            4 <= w <= 8,
            forall|k: int|
                #![auto]
                0 <= k < scalars_vec@.len() ==> is_canonical_scalar(&scalars_vec@[k]),
            forall|k: int|
                0 <= k < points_vec@.len() && (#[trigger] points_vec@[k]).is_some()
                    ==> is_well_formed_edwards_point(points_vec@[k].unwrap()),
        ensures
            result.is_some() <==> all_points_some(points_vec@),
            result.is_some() ==> ({
                let sp = result.unwrap();
                let dc = if w < 8 {
                    (256 + (w as int) - 1) / (w as int)
                } else {
                    (256 + (w as int) - 1) / (w as int) + 1
                };
                &&& sp@.len() == scalars_vec@.len()
                &&& forall|k: int|
                    0 <= k < sp@.len() ==> {
                        &&& is_valid_radix_2w(&(#[trigger] sp@[k]).0, w as nat, dc as nat)
                        &&& reconstruct_radix_2w(sp@[k].0@.take(dc), w as nat) == scalar_as_nat(
                            &scalars_vec@[k],
                        ) as int
                    }
                &&& forall|k: int|
                    0 <= k < sp@.len() ==> is_valid_projective_niels_point((#[trigger] sp@[k]).1)
                &&& forall|k: int|
                    0 <= k < sp@.len() ==> fe51_limbs_bounded(&(#[trigger] sp@[k]).1.Y_plus_X, 54)
                &&& forall|k: int|
                    0 <= k < sp@.len() ==> fe51_limbs_bounded(&(#[trigger] sp@[k]).1.Y_minus_X, 54)
                &&& forall|k: int|
                    0 <= k < sp@.len() ==> fe51_limbs_bounded(&(#[trigger] sp@[k]).1.Z, 54)
                &&& forall|k: int|
                    0 <= k < sp@.len() ==> fe51_limbs_bounded(&(#[trigger] sp@[k]).1.T2d, 54)
                &&& forall|k: int|
                    0 <= k < sp@.len() ==> projective_niels_corresponds_to_edwards(
                        (#[trigger] sp@[k]).1,
                        points_vec@[k].unwrap(),
                    )
            }),
    {
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
                4 <= w <= 8,
                forall|k: int|
                    #![auto]
                    0 <= k < scalars_vec@.len() ==> is_canonical_scalar(&scalars_vec@[k]),
                forall|k: int|
                    0 <= k < points_vec@.len() && (#[trigger] points_vec@[k]).is_some()
                        ==> is_well_formed_edwards_point(points_vec@[k].unwrap()),
                forall|k: int| 0 <= k < idx ==> (#[trigger] points_vec@[k]).is_some(),
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
                        assert(points_vec@[idx as int].is_some());
                        assert(is_well_formed_edwards_point(points_vec@[idx as int].unwrap()));
                        lemma_unfold_edwards(P);
                    }
                    let digits = scalars_vec[idx].as_radix_2w(w);
                    let niels = P.as_projective_niels();
                    scalars_points.push((digits, niels));
                    proof {
                        assert(scalars_points@[idx as int] == (digits, niels));
                        assert(scalars_points@[idx as int].0 == digits);
                        assert(scalars_points@[idx as int].1 == niels);
                    }
                },
                None => {
                    proof {
                        assert(!points_vec@[idx as int].is_some());
                        assert(!all_points_some(points_vec@));
                    }
                    return None;
                },
            }
            idx = idx + 1;
        }
        proof {
            assert(forall|k: int|
                0 <= k < points_vec@.len() ==> (#[trigger] points_vec@[k]).is_some());
            assert(all_points_some(points_vec@));
        }
        Some(scalars_points)
    }

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

        let scalars_points = match Pippenger::pair_scalars_points(&scalars_vec, &points_vec, w) {
            Some(sp) => sp,
            None => {
                proof {
                    assert(!all_points_some(spec_points));
                }
                return None;
            },
        };
        proof {
            assert(all_points_some(spec_points));
        }
        /* </REFACTORED CODE> */

        // Ghost state setup
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

            assert forall|k: int| 0 <= k < n implies #[trigger] unwrapped_points[k]
                == spec_points[k].unwrap() by {};
            assert forall|k: int| 0 <= k < n implies #[trigger] pts_affine[k]
                == edwards_point_as_affine(unwrapped_points[k]) by {};
            assert forall|k: int| 0 <= k < n implies (#[trigger] pts_affine[k]).0 < p()
                && pts_affine[k].1 < p() by {
                lemma_edwards_point_as_affine_canonical(unwrapped_points[k]);
            };
            assert forall|k: int| 0 <= k < n implies {
                &&& (#[trigger] digits_seqs[k]).len() >= dc as int
                &&& reconstruct_radix_2w_from(digits_seqs[k], w as nat, 0, dc) == scalar_as_nat(
                    &scalars_vec@[k],
                ) as int
            } by {
                assert(digits_seqs[k].len() == 64);
                assert(dc <= 64);
                lemma_reconstruct_radix_2w_from_equals_reconstruct(digits_seqs[k], w as nat, dc);
            };
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
        let mut buckets = Pippenger::init_buckets(buckets_count);
        /* </REFACTORED CODE> */

        // Establish buckets_count == pow2(w-1) and pippenger_input_valid
        proof {
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

            // Establish niels affine == pts_affine (needed by pippenger_input_valid)
            assert forall|k: int| 0 <= k < n implies projective_niels_point_as_affine_edwards(
                (#[trigger] scalars_points@[k]).1,
            ) == pts_affine[k] by {
                assert(is_well_formed_edwards_point(points_vec@[k].unwrap()));
                assert(is_valid_edwards_point(points_vec@[k].unwrap()));
                lemma_projective_niels_affine_equals_edwards_affine(
                    scalars_points@[k].1,
                    points_vec@[k].unwrap(),
                );
            };

            // Bridge: spec functions equal caller's ghost vars
            assert(sp_points_affine(scalars_points@) =~= pts_affine);
            assert(sp_digits_seqs(scalars_points@) =~= digits_seqs);
            assert(sp_digit_count(w as nat) == dc);
        }

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
         * Matches upstream structure: process hi_column separately (avoids
         * wasted mul_by_pow_2 on identity), then fold remaining columns.
         * The upstream closure is replaced by process_column helper (Verus
         * doesn't support closures with map/fold).
         */

        // Take the high column as an initial value to avoid wasting time
        // doubling the identity element in `fold()`.
        let hi_column = Pippenger::process_column(
            &mut buckets,
            &scalars_points,
            digits_count - 1,
            w,
            buckets_count,
        );

        // Prove hi_column == H(dc-1)
        proof {
            let ghost col = straus_column_sum(
                pts_affine,
                digits_seqs,
                (dc - 1) as int,
                pts_affine.len() as int,
            );
            // H(dc) = O
            lemma_pippenger_horner_base(pts_affine, digits_seqs, w as nat, dc);
            // H(dc-1) = edwards_add([2^w]*H(dc), C_{dc-1}) = edwards_add([2^w]*O, C)
            lemma_pippenger_horner_step(pts_affine, digits_seqs, (dc - 1) as int, w as nat, dc);
            // [2^w]*O = O
            assert(edwards_scalar_mul(edwards_identity(), pow2(w as nat)) == edwards_identity())
                by {
                lemma_edwards_scalar_mul_identity(pow2(w as nat));
            }
            // O + C = (C.0 % p, C.1 % p) = C (since canonical)
            assert(edwards_point_as_affine(hi_column) == pippenger_horner(
                pts_affine,
                digits_seqs,
                (dc - 1) as int,
                w as nat,
                dc,
            )) by {
                lemma_column_sum_canonical(
                    pts_affine,
                    digits_seqs,
                    (dc - 1) as int,
                    pts_affine.len() as int,
                );
                lemma_edwards_add_identity_left(col.0, col.1);
                lemma_small_mod(col.0, p());
                lemma_small_mod(col.1, p());
            }
        }

        let mut total = hi_column;
        let mut digit_index: usize = digits_count - 1;
        while digit_index > 0
            invariant
                0 < digit_index <= digits_count - 1 || digit_index == 0,
                digits_count as nat == dc,
                dc >= 1,
                dc <= 64,
                4 <= w <= 8,
                buckets_count as int == pow2((w - 1) as nat),
                buckets_count >= 1,
                buckets@.len() == buckets_count as int,
                is_well_formed_edwards_point(total),
                edwards_point_as_affine(total) == pippenger_horner(
                    pts_affine,
                    digits_seqs,
                    digit_index as int,
                    w as nat,
                    dc,
                ),
                pippenger_input_valid(scalars_points@, pts_affine, digits_seqs, w as nat, dc),
                // Bridge: spec functions equal caller's ghost vars (for process_column pre/post)
                sp_points_affine(scalars_points@) == pts_affine,
                sp_digits_seqs(scalars_points@) == digits_seqs,
                sp_digit_count(w as nat) == dc,
            decreases digit_index,
        {
            digit_index = digit_index - 1;

            // Shift total by 2^w
            let shifted = total.mul_by_pow_2(w as u32);

            // Process column at digit_index
            let column = Pippenger::process_column(
                &mut buckets,
                &scalars_points,
                digit_index,
                w,
                buckets_count,
            );

            // Accumulate: total = [2^w]*total_old + column
            total = &shifted + &column;

            proof {
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

        // Final proof: pippenger_horner(pts, digs, 0, w, dc) == sum_of_scalar_muls(scalars, points)
        proof {
            assert(spec_scalars.len() == unwrapped_points.len());
            assert(pts_affine.len() == spec_scalars.len());
            assert(digits_seqs.len() == spec_scalars.len());

            assert forall|k: int| 0 <= k < pts_affine.len() implies #[trigger] pts_affine[k]
                == edwards_point_as_affine(unwrapped_points[k]) by {
                assert(unwrapped_points[k] == spec_points[k].unwrap());
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
                unwrapped_points,
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
