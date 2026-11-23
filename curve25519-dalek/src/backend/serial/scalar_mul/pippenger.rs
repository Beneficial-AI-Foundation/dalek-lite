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

use super::iterator::collect_optional_map;
#[cfg(verus_keep_ghost)]
use crate::specs::iterator_specs::{borrowed_values, optional_iter_outcome};
use core::borrow::Borrow;
use core::cmp::Ordering;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::{map_postcondition, zip_iter_snd, zip_postcondition, IteratorSpec};

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
use vstd::arithmetic::power2::{lemma2_to64, lemma_pow2_pos, pow2};

#[cfg(verus_keep_ghost)]
use crate::specs::iterator_specs::{all_points_some, unwrap_points};

verus! {

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

    open spec fn valid_vartime_scalar(s: Scalar) -> bool {
        true
    }

    open spec fn valid_vartime_point(p: EdwardsPoint) -> bool {
        is_well_formed_edwards_point(p)
    }

    #[verifier::prophetic]
    open spec fn valid_vartime_scalar_hint<I: Iterator>(si: I) -> bool {
        crate::core_assumes::by_ref_preserves_items(si)
    }

    #[verifier::prophetic]
    open spec fn valid_vartime_point_hint<J: Iterator>(pi: J) -> bool {
        true
    }

    open spec fn vartime_sum(ss: Seq<Scalar>, ps: Seq<EdwardsPoint>, r: EdwardsPoint) -> bool {
        edwards_msm_result(ss, ps, r)
    }

    fn optional_multiscalar_mul<I, J>(scalars: I, points: J) -> (out: Option<EdwardsPoint>) where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator<Item = Option<EdwardsPoint>>,
     {
        let mut scalar_iter = scalars.into_iter();
        let ghost si = scalar_iter;
        assert(call_ensures(I::into_iter, (scalars,), si));
        assert(crate::core_assumes::by_ref_preserves_items(si));
        let hint = crate::core_assumes::by_ref_size_hint(&mut scalar_iter);
        assert(crate::core_assumes::by_ref_hint_outcome(si, scalar_iter, hint));
        assert(scalar_iter.obeys_prophetic_iter_laws());
        assert(scalar_iter.remaining() == si.remaining() && scalar_iter.produces()
            == si.produces());
        let size = hint.0;
        let w: usize = if size < 500 {
            6
        } else if size < 800 {
            7
        } else {
            8
        };

        // Convert the scalar and point of each pair lazily. Collection stops at the first missing point.
        let digits_for = |item: I::Item| -> (d: [i8; 64])
            ensures
                exists|s: Scalar| #[trigger]
                    call_ensures(Borrow::borrow, (&item,), &s) && radix_digits_for(d, s, w),
            {
                let s = item.borrow();
                assert(call_ensures(Borrow::borrow, (&item,), s));
                let d = s.as_radix_2w(w);
                assert(radix_digits_for(d, *s, w));
                d
            };
        let niels_for_point = |point: Option<EdwardsPoint>| -> (niels: Option<
            ProjectiveNielsPoint,
        >)
            requires
                point.is_some() ==> is_well_formed_edwards_point(point.unwrap()),
            ensures
                niels.is_some() == point.is_some(),
                niels.is_some() ==> niels_for(niels.unwrap(), point.unwrap()),
            {
                match point {
                    Some(p) => {
                        proof {
                            lemma_unfold_edwards(p);
                        }
                        Some(p.as_projective_niels())
                    },
                    None => None,
                }
            };
        let result = Self::collect_pairs(
            scalar_iter,
            points,
            digits_for,
            niels_for_point,
            Ghost(w),
        );
        let ghost pi = choose|pi: J::IntoIter| #[trigger]
            call_ensures(J::into_iter, (points,), pi) && prepared_pair_outcome(
                scalar_iter,
                pi,
                result,
                w,
            );
        assert(prepared_pair_outcome(scalar_iter, pi, result, w));
        let pairs = match result {
            None => {
                assert(optional_iter_outcome(
                    si,
                    pi,
                    None,
                    |ss, ps, r| Self::vartime_sum(ss, ps, r),
                ));
                return None;
            },
            Some(v) => v,
        };
        proof {
            lemma_prepared_outcome(scalar_iter, pi, pairs, w);
        }
        let total = Self::sum_columns(pairs, w);
        assert(optional_iter_outcome(
            scalar_iter,
            pi,
            Some(total),
            |ss, ps, r| Self::vartime_sum(ss, ps, r),
        ));
        assert(optional_iter_outcome(
            si,
            pi,
            Some(total),
            |ss, ps, r| Self::vartime_sum(ss, ps, r),
        ));
        Some(total)
    }
}

spec fn radix_digits_for(d: [i8; 64], s: Scalar, w: usize) -> bool {
    let dc = sp_digit_count(w as nat);
    &&& is_valid_radix_2w(&d, w as nat, dc)
    &&& reconstruct_radix_2w(d@.take(dc as int), w as nat) == scalar_as_nat(&s) as int
}

spec fn niels_for(n: ProjectiveNielsPoint, p: EdwardsPoint) -> bool {
    &&& is_valid_projective_niels_point(n)
    &&& fe51_limbs_bounded(&n.Y_plus_X, 54)
    &&& fe51_limbs_bounded(&n.Y_minus_X, 54)
    &&& fe51_limbs_bounded(&n.Z, 54)
    &&& fe51_limbs_bounded(&n.T2d, 54)
    &&& projective_niels_corresponds_to_edwards(n, p)
}

impl Pippenger {
    /// Initialize `count` buckets with the identity point.
    /// Replaces: `(0..count).map(|_| EdwardsPoint::identity()).collect()`
    fn init_buckets(count: usize) -> (buckets: Vec<EdwardsPoint>)
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
    ///
    /// This is the Verus equivalent of the upstream closure body in:
    /// ```text
    /// let mut columns = (0..digits_count).rev().map(|digit_index| {
    ///     for bucket in &mut buckets { *bucket = EdwardsPoint::identity(); }
    ///     for (digits, pt) in scalars_points.iter() {
    ///         let digit = digits[digit_index] as i16;
    ///         match digit.cmp(&0) {
    ///             Ordering::Greater => { let b = (digit-1) as usize;  buckets[b] = (&buckets[b] + pt).as_extended(); }
    ///             Ordering::Less   => { let b = (-digit-1) as usize; buckets[b] = (&buckets[b] - pt).as_extended(); }
    ///             Ordering::Equal  => {}
    ///         }
    ///     }
    ///     let mut buckets_intermediate_sum = buckets[buckets_count - 1];
    ///     let mut buckets_sum = buckets[buckets_count - 1];
    ///     for i in (0..(buckets_count - 1)).rev() {
    ///         buckets_intermediate_sum += buckets[i];
    ///         buckets_sum += buckets_intermediate_sum;
    ///     }
    ///     buckets_sum
    /// });
    /// ```
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
            6 <= w <= 8,
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
            final(buckets)@.len() == buckets_count as int,
    {
        use crate::traits::Identity;

        // Derive ghost variables from runtime arguments (no Ghost params needed)
        let ghost pts_affine = sp_points_affine(scalars_points@);
        let ghost digits_seqs = sp_digits_seqs(scalars_points@);
        let ghost dc = sp_digit_count(w as nat);
        let ghost n_ghost: int = scalars_points@.len() as int;
        let ghost B = buckets_count as int;

        // buckets_count == pow2(w-1) >= pow2(3) >= 1 since w >= 4
        proof {
            lemma_pow2_pos((w - 1) as nat);
        }

        // ---- Phase 1: Clear buckets to identity ----
        // UPSTREAM: for bucket in &mut buckets { *bucket = EdwardsPoint::identity(); }
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
        // UPSTREAM:
        //   for (digits, pt) in scalars_points.iter() {
        //       let digit = digits[digit_index] as i16;
        //       match digit.cmp(&0) {
        //           Ordering::Greater => { let b = (digit - 1) as usize;  buckets[b] = (&buckets[b] + pt).as_extended(); }
        //           Ordering::Less    => { let b = (-digit - 1) as usize; buckets[b] = (&buckets[b] - pt).as_extended(); }
        //           Ordering::Equal   => {}
        //       }
        //   }
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
                6 <= w <= 8,
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
                assert(is_valid_radix_2w(&scalars_points@[sp_idx as int].0, w as nat, dc));
                assert(-(buckets_count as int) <= (digit as int) && (digit as int) <= (
                buckets_count as int));
            }

            let ghost col = digit_index as int;
            let ghost d_val = digits_seqs[sp_idx as int][col] as int;

            if digit > 0 {
                let b = (digit - 1) as usize;
                let completed = &buckets[b] + pt;
                let new_bucket = completed.as_extended();
                buckets.set(b, new_bucket);
                proof {
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
                        } else {
                            assert(d_val > 0);
                            assert(d_val != -(bb + 1));
                        }
                    };
                }
            } else if digit < 0 {
                let b = (-digit - 1) as usize;
                let completed = &buckets[b] - pt;
                let new_bucket = completed.as_extended();
                buckets.set(b, new_bucket);
                proof {
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
                        } else {
                        }
                    };
                }
            } else {
                // digit == 0: no bucket modified
                proof {
                    assert forall|bb: int| 0 <= bb < buckets_count implies edwards_point_as_affine(
                        #[trigger] buckets@[bb],
                    ) == pippenger_bucket_contents(
                        pts_affine,
                        digits_seqs,
                        col,
                        sp_idx as int + 1,
                        bb,
                    ) by {};
                }
            }
            sp_idx = sp_idx + 1;
        }

        // ---- Phase 3: Sum buckets via intermediate-sum trick ----
        // UPSTREAM:
        //   let mut buckets_intermediate_sum = buckets[buckets_count - 1];
        //   let mut buckets_sum = buckets[buckets_count - 1];
        //   for i in (0..(buckets_count - 1)).rev() {
        //       buckets_intermediate_sum += buckets[i];
        //       buckets_sum += buckets_intermediate_sum;
        //   }
        //   buckets_sum
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

            assert forall|b: int| 0 <= b < B implies is_on_edwards_curve(
                (#[trigger] buckets_affine[b]).0,
                buckets_affine[b].1,
            ) by {
                lemma_edwards_point_as_affine_on_curve(buckets@[b]);
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
            lemma_pippenger_input_on_curve(scalars_points@, pts_affine, digits_seqs, w as nat, dc);
            assert forall|k: int| 0 <= k < n_ghost implies is_on_edwards_curve(
                (#[trigger] pts_affine[k]).0,
                pts_affine[k].1,
            ) by {};

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

    /// Slice adapter for the variable-time iterator method.
    /// Computes sum(scalars[i] * points[i]) if every points[i] is Some.
    /// The scalars can be any 256-bit values: the radix-2^w digits for w >= 6 need no bound.
    pub fn optional_multiscalar_mul_verus(
        scalars: &[Scalar],
        points: &[Option<EdwardsPoint>],
    ) -> (result: Option<EdwardsPoint>)
        requires
    // Same number of scalars and points

            scalars@.len() == points@.len(),
            // All input points (when Some) must be well-formed
            forall|i: int|
                0 <= i < points@.len() && (#[trigger] points@[i]).is_some()
                    ==> is_well_formed_edwards_point(points@[i].unwrap()),
        ensures
    // Result is Some iff all input points are Some

            result.is_some() <==> all_points_some(points@),
            // If result is Some, it is a well-formed Edwards point
            result.is_some() ==> is_well_formed_edwards_point(result.unwrap()),
            // Semantic correctness: result = sum(scalars[i] * points[i])
            result.is_some() ==> edwards_point_as_affine(result.unwrap()) == sum_of_scalar_muls(
                scalars@,
                unwrap_points(points@),
            ),
    {
        broadcast use crate::traits::group_multiscalar_inputs;

        let si = scalars.iter();
        let source = points.iter();
        let copy = |p: &Option<EdwardsPoint>| -> (r: Option<EdwardsPoint>)
            ensures
                r == *p,
            { *p };
        let pi = source.map(copy);
        proof {
            vstd::std_specs::iter::map_postcondition(source, copy, pi);
        }
        let result = Self::optional_multiscalar_mul(si, pi);
        proof {
            if result.is_some() {
                assert(pi.remaining() =~= points@);
                let ss = choose|ss: Seq<Scalar>| #[trigger]
                    borrowed_values(si.remaining(), ss) && Self::vartime_sum(
                        ss,
                        pi.remaining().map(|_, p: Option<EdwardsPoint>| p.unwrap()),
                        result.unwrap(),
                    );
                crate::traits::lemma_msm_referenced_values(scalars@, ss);
            } else {
                let k = choose|k: int|
                    0 <= k < pi.remaining().len() && pi.produces()[k] && (
                    #[trigger] pi.remaining()[k]).is_none();
                assert(points@[k].is_none());
            }
        }
        result
    }
}

/// Connect the column sum to the particular scalar and point values produced by these iterators.
proof fn lemma_prepared_outcome<I: Iterator, J: Iterator<Item = Option<EdwardsPoint>>>(
    si: I,
    pi: J,
    pairs: Vec<([i8; 64], ProjectiveNielsPoint)>,
    w: usize,
) where I::Item: Borrow<Scalar>
    requires
        6 <= w <= 8,
        prepared_pair_outcome(si, pi, Some(pairs), w),
        crate::specs::iterator_specs::valid_optional_points(
            pi,
            |p| is_well_formed_edwards_point(p),
        ),
    ensures
        pippenger_input_valid(
            pairs@,
            sp_points_affine(pairs@),
            sp_digits_seqs(pairs@),
            w as nat,
            sp_digit_count(w as nat),
        ),
        forall|total: EdwardsPoint|
            is_well_formed_edwards_point(total) && (#[trigger] edwards_point_as_affine(total))
                == pippenger_horner(
                sp_points_affine(pairs@),
                sp_digits_seqs(pairs@),
                0,
                w as nat,
                sp_digit_count(w as nat),
            ) ==> optional_iter_outcome(
                si,
                pi,
                Some(total),
                |ss, ps, r| Pippenger::vartime_sum(ss, ps, r),
            ),
{
    let ss = choose|ss: Seq<Scalar>| #[trigger]
        borrowed_values(si.remaining(), ss) && forall|k: int|
            0 <= k < pairs@.len() ==> radix_digits_for((#[trigger] pairs@[k]).0, ss[k], w);
    let pts = unwrap_points(pi.remaining());
    assert forall|k: int| 0 <= k < pairs@.len() implies {
        &&& is_well_formed_edwards_point(#[trigger] pts[k])
        &&& niels_for(pairs@[k].1, pts[k])
        &&& radix_digits_for(pairs@[k].0, ss[k], w)
    } by {
        assert(niels_for(pairs@[k].1, pi.remaining()[k].unwrap()));
        assert(pi.produces()[k] && pi.remaining()[k].is_some());
    }
    lemma_prepared_sum(pairs@, ss, pts, w);
    assert forall|k: int| 0 <= k < si.remaining().len() implies #[trigger] si.produces()[k] by {
        assert(niels_for(pairs@[k].1, pts[k]));
    }
    assert forall|k: int| 0 <= k < pi.remaining().len() implies #[trigger] pi.produces()[k]
        && pi.remaining()[k].is_some() by {
        assert(niels_for(pairs@[k].1, pts[k]));
    }
    assert forall|total: EdwardsPoint|
        is_well_formed_edwards_point(total) && (#[trigger] edwards_point_as_affine(total))
            == pippenger_horner(
            sp_points_affine(pairs@),
            sp_digits_seqs(pairs@),
            0,
            w as nat,
            sp_digit_count(w as nat),
        ) implies optional_iter_outcome(
        si,
        pi,
        Some(total),
        |ss, ps, r| Pippenger::vartime_sum(ss, ps, r),
    ) by {
        assert(Pippenger::vartime_sum(ss, pts, total));
    }
}

/// Evaluating the prepared digit columns gives the sum of the original scalar-point products.
proof fn lemma_prepared_sum(
    pairs: Seq<([i8; 64], ProjectiveNielsPoint)>,
    ss: Seq<Scalar>,
    pts: Seq<EdwardsPoint>,
    w: usize,
)
    requires
        6 <= w <= 8,
        ss.len() == pts.len(),
        pairs.len() == pts.len(),
        forall|k: int|
            #![trigger pts[k]]
            #![trigger pairs[k]]
            0 <= k < pairs.len() ==> is_well_formed_edwards_point(pts[k]) && niels_for(
                pairs[k].1,
                pts[k],
            ) && radix_digits_for(pairs[k].0, ss[k], w),
    ensures
        pippenger_input_valid(
            pairs,
            sp_points_affine(pairs),
            sp_digits_seqs(pairs),
            w as nat,
            sp_digit_count(w as nat),
        ),
        pippenger_horner(
            sp_points_affine(pairs),
            sp_digits_seqs(pairs),
            0,
            w as nat,
            sp_digit_count(w as nat),
        ) == sum_of_scalar_muls(ss, pts),
{
    let affine = sp_points_affine(pairs);
    let ds = sp_digits_seqs(pairs);
    let dc = sp_digit_count(w as nat);
    assert(dc <= 64) by {
        assert(sp_digit_count(6) == 43 && sp_digit_count(7) == 37 && sp_digit_count(8) == 33)
            by (compute);
        assert(w == 6 || w == 7 || w == 8);
    }
    assert forall|k: int| 0 <= k < pairs.len() implies {
        &&& #[trigger] affine[k] == edwards_point_as_affine(pts[k])
        &&& affine[k].0 < p() && affine[k].1 < p()
    } by {
        lemma_projective_niels_affine_equals_edwards_affine(pairs[k].1, pts[k]);
        lemma_edwards_point_as_affine_canonical(pts[k]);
    }
    assert forall|k: int| 0 <= k < ds.len() implies {
        &&& (#[trigger] ds[k]).len() >= dc
        &&& reconstruct_radix_2w_from(ds[k], w as nat, 0, dc) == scalar_as_nat(&ss[k]) as int
    } by {
        assert(radix_digits_for(pairs[k].0, ss[k], w));
        lemma_reconstruct_radix_2w_from_equals_reconstruct(ds[k], w as nat, dc);
    }
    lemma_pippenger_horner_correct(ss, pts, affine, ds, w as nat, dc);
}

#[verifier::prophetic]
spec fn prepared_pair_outcome<I: Iterator, J: Iterator<Item = Option<EdwardsPoint>>>(
    si: I,
    pi: J,
    out: Option<Vec<([i8; 64], ProjectiveNielsPoint)>>,
    w: usize,
) -> bool where I::Item: Borrow<Scalar> {
    match out {
        None => exists|k: int|
            0 <= k < pi.remaining().len() && pi.produces()[k] && (
            #[trigger] pi.remaining()[k]).is_none(),
        Some(v) => {
            &&& v@.len() == si.remaining().len() && v@.len() == pi.remaining().len()
            &&& forall|k: int|
                0 <= k < v@.len() ==> si.produces()[k] && pi.produces()[k]
                    && pi.remaining()[k].is_some() && niels_for(
                    (#[trigger] v@[k]).1,
                    pi.remaining()[k].unwrap(),
                )
            &&& exists|ss: Seq<Scalar>| #[trigger]
                borrowed_values(si.remaining(), ss) && forall|k: int|
                    0 <= k < v@.len() ==> radix_digits_for((#[trigger] v@[k]).0, ss[k], w)
        },
    }
}

impl Pippenger {
    /// Zip both lazy maps and collect until the first missing point.
    fn collect_pairs<I, J, D, N>(
        si: I,
        points: J,
        digits_for: D,
        niels_for_point: N,
        Ghost(w): Ghost<usize>,
    ) -> (out: Option<Vec<([i8; 64], ProjectiveNielsPoint)>>) where
        I: Iterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator<Item = Option<EdwardsPoint>>,
        D: FnMut(I::Item) -> [i8; 64],
        N: FnMut(Option<EdwardsPoint>) -> Option<ProjectiveNielsPoint>,

        requires
            si.obeys_prophetic_iter_laws(),
            forall|x: I::Item| #[trigger] digits_for.requires((x,)),
            forall|x: I::Item, d: [i8; 64]| #[trigger]
                digits_for.ensures((x,), d) ==> exists|s: Scalar| #[trigger]
                    call_ensures(Borrow::borrow, (&x,), &s) && radix_digits_for(d, s, w),
            forall|pi: J::IntoIter| #[trigger]
                call_ensures(J::into_iter, (points,), pi) ==> {
                    &&& pi.obeys_prophetic_iter_laws()
                    &&& pi.remaining().len() == si.remaining().len()
                    &&& forall|k: int|
                        0 <= k < pi.remaining().len() && pi.produces()[k]
                            ==> niels_for_point.requires((#[trigger] pi.remaining()[k],))
                },
            forall|p: Option<EdwardsPoint>, n: Option<ProjectiveNielsPoint>| #[trigger]
                niels_for_point.ensures((p,), n) ==> {
                    &&& n.is_some() == p.is_some()
                    &&& n.is_some() ==> niels_for(n.unwrap(), p.unwrap())
                },
        ensures
            exists|pi: J::IntoIter| #[trigger]
                call_ensures(J::into_iter, (points,), pi) && prepared_pair_outcome(si, pi, out, w),
    {
        let digits = si.map(digits_for);
        proof {
            map_postcondition(si, digits_for, digits);
        }
        let pi = points.into_iter();
        assert(call_ensures(J::into_iter, (points,), pi));
        let niels = pi.map(niels_for_point);
        proof {
            map_postcondition(pi, niels_for_point, niels);
        }
        let zipped = digits.zip(niels);
        proof {
            zip_postcondition(digits, niels, zipped);
            assert(zip_iter_snd(zipped) == niels);
            assert(zipped.remaining().len() == si.remaining().len());
            assert forall|k: int| 0 <= k < zipped.remaining().len() implies {
                &&& #[trigger] zipped.remaining()[k] == (
                    digits.remaining()[k],
                    niels.remaining()[k],
                )
                &&& zipped.produces()[k] == (digits.produces()[k] && niels.produces()[k])
            } by {}
        }
        let pair = |entry: ([i8; 64], Option<ProjectiveNielsPoint>)| -> (out: Option<
            ([i8; 64], ProjectiveNielsPoint),
        >)
            ensures
                out == (if entry.1.is_some() {
                    Some((entry.0, entry.1.unwrap()))
                } else {
                    None
                }),
            {
                match entry.1 {
                    Some(p) => Some((entry.0, p)),
                    None => None,
                }
            };
        let pairs = match collect_optional_map(zipped, pair) {
            Some(v) => v,
            None => {
                proof {
                    let k = choose|k: int|
                        0 <= k < zipped.remaining().len() && zipped.produces()[k] && pair.ensures(
                            (#[trigger] zipped.remaining()[k],),
                            None,
                        );
                    assert(niels.remaining()[k].is_none());
                    assert(pi.remaining()[k].is_none());
                    assert(prepared_pair_outcome(si, pi, None, w));
                }
                return None;
            },
        };
        let ghost ss = Seq::new(
            pairs@.len(),
            |k: int|
                choose|s: Scalar| #[trigger]
                    call_ensures(Borrow::borrow, (&si.remaining()[k],), &s) && radix_digits_for(
                        pairs@[k].0,
                        s,
                        w,
                    ),
        );
        proof {
            assert forall|k: int| 0 <= k < pairs@.len() implies {
                &&& #[trigger] si.produces()[k]
                &&& pi.produces()[k]
                &&& pi.remaining()[k].is_some()
                &&& call_ensures(Borrow::borrow, (&si.remaining()[k],), &ss[k])
                &&& radix_digits_for(pairs@[k].0, ss[k], w)
                &&& niels_for(pairs@[k].1, pi.remaining()[k].unwrap())
            } by {
                assert(pair.ensures((zipped.remaining()[k],), Some(pairs@[k])));
                assert(niels.remaining()[k] == Some(pairs@[k].1));
                assert(digits_for.ensures((si.remaining()[k],), pairs@[k].0));
            }
        }
        assert(borrowed_values(si.remaining(), ss));
        assert(prepared_pair_outcome(si, pi, Some(pairs), w));
        Some(pairs)
    }

    /// Sum the columns of the prepared radix digits and projective Niels points.
    fn sum_columns(scalars_points: Vec<([i8; 64], ProjectiveNielsPoint)>, w: usize) -> (result:
        EdwardsPoint)
        requires
            6 <= w <= 8,
            pippenger_input_valid(
                scalars_points@,
                sp_points_affine(scalars_points@),
                sp_digits_seqs(scalars_points@),
                w as nat,
                sp_digit_count(w as nat),
            ),
        ensures
            is_well_formed_edwards_point(result),
            edwards_point_as_affine(result) == pippenger_horner(
                sp_points_affine(scalars_points@),
                sp_digits_seqs(scalars_points@),
                0,
                w as nat,
                sp_digit_count(w as nat),
            ),
    {
        let ghost pts_affine = sp_points_affine(scalars_points@);
        let ghost digits_seqs = sp_digits_seqs(scalars_points@);
        let ghost dc = sp_digit_count(w as nat);

        /* UNCHANGED FROM ORIGINAL: Bucket configuration */
        let max_digit: usize = 1 << w;
        let digits_count: usize = Scalar::to_radix_2w_size_hint(w);
        let buckets_count: usize = max_digit / 2;  // digits are signed+centered hence 2^w/2, excluding 0-th bucket

        proof {
            assert(6 <= w <= 8);
            if w == 6 {
                assert(1usize << 6usize == 64usize) by (bit_vector);
                assert(max_digit == 64usize);
                assert(buckets_count == 32usize);
                assert(digits_count == ((256 + 6 - 1) / (6int)) as usize);
                assert(261int / 6 == 43);
                assert(digits_count == 43usize);
            } else if w == 7 {
                assert(1usize << 7usize == 128usize) by (bit_vector);
                assert(max_digit == 128usize);
                assert(buckets_count == 64usize);
                assert(digits_count == ((256 + 7 - 1) / (7int)) as usize);
                assert(262int / 7 == 37);
                assert(digits_count == 37usize);
            } else {
                assert(1usize << 8usize == 256usize) by (bit_vector);
                assert(max_digit == 256usize);
                assert(buckets_count == 128usize);
                assert(digits_count == ((256 + 8 - 1) / (8int) + 1) as usize);
                assert(263int / 8 + 1 == 33);
                assert(digits_count == 33usize);
            }
            assert(digits_count > 0);
            assert(buckets_count > 0);
        }

        assert(digits_count as nat == dc);
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

        // UPSTREAM: let hi_column = columns.next().expect("should have more than zero digits");
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
            // Unfold pippenger_horner and prove hi_column == H(dc-1)
            // H(dc) = O, H(dc-1) = edwards_add([2^w]*O, C) = C
            assert(edwards_point_as_affine(hi_column) == pippenger_horner(
                pts_affine,
                digits_seqs,
                (dc - 1) as int,
                w as nat,
                dc,
            )) by {
                reveal_with_fuel(pippenger_horner, 2);
                lemma_edwards_scalar_mul_identity(pow2(w as nat));
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

        // UPSTREAM: Some(columns.fold(hi_column, |total, p| total.mul_by_pow_2(w as u32) + p))
        let mut total = hi_column;
        let mut digit_index: usize = digits_count - 1;
        while digit_index > 0
            invariant
                0 < digit_index <= digits_count - 1 || digit_index == 0,
                digits_count as nat == dc,
                dc >= 1,
                dc <= 64,
                6 <= w <= 8,
                buckets_count as int == pow2((w - 1) as nat),
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

            // UPSTREAM (fold body): total.mul_by_pow_2(w as u32) + p
            let shifted = total.mul_by_pow_2(w as u32);
            let column = Pippenger::process_column(
                &mut buckets,
                &scalars_points,
                digit_index,
                w,
                buckets_count,
            );

            total = &shifted + &column;

            proof {
                reveal(pippenger_horner);
            }
        }
        /* </REFACTORED CODE> */

        total
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
