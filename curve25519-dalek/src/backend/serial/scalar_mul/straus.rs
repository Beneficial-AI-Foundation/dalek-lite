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

#[cfg(verus_keep_ghost)]
use super::iterator::mapped_borrows;
use super::iterator::{collect_borrowed_map, collect_optional_map};
#[cfg(verus_keep_ghost)]
use crate::specs::iterator_specs::{borrowed_values, optional_iter_outcome};
use alloc::vec::Vec;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;

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
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar_specs::*;
#[cfg(verus_keep_ghost)]
use crate::specs::window_specs::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::pow2;

#[cfg(verus_keep_ghost)]
use crate::specs::iterator_specs::{all_points_some, unwrap_points};

verus! {

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

#[cfg(feature = "zeroize")]
#[verifier::external_body]
fn zeroize_scalar_digits(digits: &mut Vec<[i8; 64]>) {
    zeroize::Zeroize::zeroize(digits);
}

impl MultiscalarMul for Straus {
    type Point = EdwardsPoint;

    open spec fn valid_msm_point(point: EdwardsPoint) -> bool {
        is_well_formed_edwards_point(point)
    }

    /// Straus collects the points before converting the scalar source. Each conversion
    /// must yield a valid iterator, and the two iterators must have the same length.
    #[verifier::prophetic]
    open spec fn valid_msm_inputs<I: IntoIterator, J: IntoIterator>(
        scalars: I,
        points: J,
    ) -> bool where I::Item: Borrow<Scalar>, J::Item: Borrow<EdwardsPoint> {
        &&& forall|pi: J::IntoIter| #[trigger]
            call_ensures(J::into_iter, (points,), pi)
                ==> crate::specs::iterator_specs::valid_msm_items(pi, |p| Self::valid_msm_point(p))
        &&& forall|si: I::IntoIter| #[trigger]
            call_ensures(I::into_iter, (scalars,), si)
                ==> crate::specs::iterator_specs::valid_msm_items(
                si,
                |s: Scalar| s.bytes[31] <= 127,
            )
        &&& forall|si: I::IntoIter, pi: J::IntoIter| #[trigger]
            call_ensures(I::into_iter, (scalars,), si) && #[trigger] call_ensures(
                J::into_iter,
                (points,),
                pi,
            ) ==> si.remaining().len() == pi.remaining().len()
    }

    open spec fn msm_sum(
        scalars: Seq<Scalar>,
        points: Seq<EdwardsPoint>,
        result: EdwardsPoint,
    ) -> bool {
        edwards_msm_result(scalars, points, result)
    }

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
    fn multiscalar_mul<I, J>(scalars: I, points: J) -> (out: EdwardsPoint) where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator,
        J::Item: Borrow<EdwardsPoint>,
     {
        /* <ORIGINAL CODE>
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
        </ORIGINAL CODE> */
        let pi = points.into_iter();
        assert(call_ensures(J::into_iter, (points,), pi));
        let table_for = |p: &EdwardsPoint| -> (t: LookupTable<ProjectiveNielsPoint>)
            ensures
                straus_table_for(t, *p),
            { LookupTable::<ProjectiveNielsPoint>::from(p) };
        let tables = collect_borrowed_map(pi, table_for);
        let si = scalars.into_iter();
        assert(call_ensures(I::into_iter, (scalars,), si));
        let digits_for = |s: &Scalar| -> (d: [i8; 64])
            requires
                s.bytes[31] <= 127,
            ensures
                straus_digits_for(d, *s),
            { s.as_radix_16() };
        #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
        let mut digits = collect_borrowed_map(si, digits_for);
        let ghost ps = choose|ps: Seq<EdwardsPoint>| #[trigger]
            mapped_borrows(pi.remaining(), tables@, table_for, ps);
        let ghost ss = choose|ss: Seq<Scalar>| #[trigger]
            mapped_borrows(si.remaining(), digits@, digits_for, ss);
        proof {
            assert forall|k: int| 0 <= k < ps.len() implies is_well_formed_edwards_point(
                #[trigger] ps[k],
            ) by {
                assert(call_ensures(core::borrow::Borrow::borrow, (&pi.remaining()[k],), &ps[k]));
            }
            assert(prepared_inputs(tables@, digits@, ss, ps));
        }
        let out = Straus::multiscalar_mul_prepared(tables.as_slice(), digits.as_slice());
        #[cfg(feature = "zeroize")]
        zeroize_scalar_digits(&mut digits);
        assert(borrowed_values(si.remaining(), ss));
        assert(borrowed_values(pi.remaining(), ps));
        assert(Self::msm_sum(ss, ps, out));
        out
    }
}

spec fn vartime_table_for(
    table: NafLookupTable5<ProjectiveNielsPoint>,
    point: EdwardsPoint,
) -> bool {
    &&& is_valid_naf_lookup_table5_projective(table.0, point)
    &&& naf_lookup_table5_projective_limbs_bounded(table.0)
    &&& forall|j: int| 0 <= j < 8 ==> is_valid_projective_niels_point(#[trigger] table.0[j])
}

/*
 * VERIFICATION NOTE
 * =================
 * The constant-time iterator and slice methods prepare their inputs separately
 * and use the same verified arithmetic kernel, `multiscalar_mul_prepared`.
 * The variable-time iterator method builds the NAFs and lookup tables.
 * Its arithmetic kernel uses indexed loops with invariants.
 *
 * ALGORITHM OVERVIEW
 * ==================
 * Both VT and CT compute Q = sum(s_k * P_k) via column-wise Horner evaluation.
 *
 * Variable-time (VT) -- NAF width 5, 256 bit positions:
 *   Each scalar s_k is decomposed into NAF digits n_{k,i} (i = 0..255).
 *   Define col(i, j) = sum_{k=0}^{j-1} [n_{k,i}] * P_k   (column sum for bit i)
 *   The Horner recurrence is:
 *     H(256) = O
 *     H(i)   = [2] * H(i+1) + col(i, n)       for i = 255..0
 *   Then Q = H(0) = straus_vt_partial(pts_affine, nafs_seqs, 0).
 *
 * Constant-time (CT) -- radix-16 signed digits, 64 digit positions:
 *   Each scalar s_k is decomposed into radix-16 digits d_{k,j} (j = 0..63).
 *   Define col(j, k) = sum_{m=0}^{k-1} [d_{m,j}] * P_m   (column sum for digit j)
 *   The Horner recurrence is:
 *     H(64) = O
 *     H(j)  = [16] * H(j+1) + col(j, n)       for j = 63..0
 *   Then Q = H(0) = straus_ct_partial(pts_affine, digits_seqs, 0).
 *
 * Both loops use `straus_vt_input_valid` / `straus_ct_input_valid` from
 * straus_lemmas.rs to bundle ~8 quantified loop invariants into a single call.
 * Correctness is proved by `lemma_straus_vt_correct` / `lemma_straus_ct_correct`.
 */

impl Straus {
    /// Slice adapter for the variable-time iterator method.
    /// Computes sum(scalars[i] * points[i]) if every points[i] is Some.
    #[verifier::rlimit(30)]
    pub fn optional_multiscalar_mul_verus(
        scalars: &[Scalar],
        points: &[Option<EdwardsPoint>],
    ) -> (result: Option<EdwardsPoint>)
        requires
    // Same number of scalars and points

            scalars@.len() == points@.len(),
            // Bit 255 of every scalar is clear (Scalar invariant #1)
            forall|i: int| #![auto] 0 <= i < scalars@.len() ==> scalars@[i].bytes[31] <= 127,
            // All input points (when Some) must be well-formed
            forall|i: int|
                0 <= i < points@.len() && (#[trigger] points@[i]).is_some()
                    ==> is_well_formed_edwards_point(points@[i].unwrap()),
        ensures
    // Result is Some if and only if all input points are Some

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

impl VartimeMultiscalarMul for Straus {
    type Point = EdwardsPoint;

    open spec fn valid_vartime_point(p: EdwardsPoint) -> bool {
        is_well_formed_edwards_point(p)
    }

    #[verifier::prophetic]
    open spec fn valid_vartime_scalar_hint<I: Iterator>(si: I) -> bool {
        true
    }

    #[verifier::prophetic]
    open spec fn valid_vartime_point_hint<J: Iterator>(pi: J) -> bool {
        true
    }

    open spec fn vartime_sum(ss: Seq<Scalar>, ps: Seq<EdwardsPoint>, r: EdwardsPoint) -> bool {
        edwards_msm_result(ss, ps, r)
    }

    /// Variable-time Straus using a non-adjacent form of width \\(5\\).
    ///
    /// This is completely similar to the constant-time code, but we
    /// use a non-adjacent form for the scalar, and do not do table
    /// lookups in constant time.
    ///
    /// The non-adjacent form has signed, odd digits.  Using only odd
    /// digits halves the table size (since we only need odd
    /// multiples), or gives fewer additions for the same table size.
    #[verifier::rlimit(30)]
    fn optional_multiscalar_mul<I, J>(scalars: I, points: J) -> (out: Option<EdwardsPoint>) where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator<Item = Option<EdwardsPoint>>,
     {
        let si = scalars.into_iter();
        assert(call_ensures(I::into_iter, (scalars,), si));
        let naf_for = |s: &Scalar| -> (d: [i8; 256])
            requires
                s.bytes[31] <= 127,
            ensures
                is_valid_naf(d@, 5),
                reconstruct(d@) == scalar_as_nat(s) as int,
            {
                proof {
                    crate::lemmas::common_lemmas::to_nat_lemmas::lemma_u8_32_as_nat_lt_pow2_255(
                        &s.bytes,
                    );
                }
                s.non_adjacent_form(5)
            };
        let nafs = collect_borrowed_map(si, naf_for);
        let ghost ss = choose|ss: Seq<Scalar>| mapped_borrows(si.remaining(), nafs@, naf_for, ss);

        let pi = points.into_iter();
        assert(call_ensures(J::into_iter, (points,), pi));
        let table_for = |point: Option<EdwardsPoint>| -> (table: Option<
            NafLookupTable5<ProjectiveNielsPoint>,
        >)
            requires
                point.is_some() ==> is_well_formed_edwards_point(point.unwrap()),
            ensures
                table.is_some() == point.is_some(),
                table.is_some() ==> vartime_table_for(table.unwrap(), point.unwrap()),
            {
                match point {
                    Some(p) => Some(NafLookupTable5::<ProjectiveNielsPoint>::from(&p)),
                    None => None,
                }
            };
        let tables = match collect_optional_map(pi, table_for) {
            Some(tables) => tables,
            None => {
                proof {
                    let k = choose|k: int|
                        0 <= k < pi.remaining().len() && pi.produces()[k] && table_for.ensures(
                            (#[trigger] pi.remaining()[k],),
                            None,
                        );
                    assert(pi.remaining()[k].is_none());
                    assert(optional_iter_outcome(
                        si,
                        pi,
                        None,
                        |ss, ps, r| Self::vartime_sum(ss, ps, r),
                    ));
                }
                return None;
            },
        };
        proof {
            assert forall|k: int| 0 <= k < tables@.len() implies {
                &&& #[trigger] pi.produces()[k]
                &&& pi.remaining()[k].is_some()
                &&& vartime_table_for(tables@[k], pi.remaining()[k].unwrap())
            } by {
                assert(table_for.ensures((pi.remaining()[k],), Some(tables@[k])));
            }
        }
        proof {
            assert forall|k: int| 0 <= k < nafs@.len() implies {
                &&& is_valid_naf((#[trigger] nafs@[k])@, 5)
                &&& reconstruct(nafs@[k]@) == scalar_as_nat(&ss[k]) as int
            } by {
                assert(naf_for.ensures((&ss[k],), nafs@[k]));
            }
            assert forall|k: int| 0 <= k < tables@.len() implies {
                &&& vartime_table_for(#[trigger] tables@[k], pi.remaining()[k].unwrap())
                &&& is_well_formed_edwards_point(pi.remaining()[k].unwrap())
            } by {
                assert(pi.produces()[k]);
            }
        }
        let lookup_tables = tables;
        let ghost spec_scalars = ss;
        let ghost spec_points = pi.remaining();
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
            // Establish unwrapped_points[k] == spec_points[k].unwrap()
            // (from Seq::map definition: unwrap_points(s) = s.map(|_, opt| opt.unwrap()))
            assert forall|m: int| 0 <= m < n implies #[trigger] unwrapped_points[m]
                == spec_points[m].unwrap() by {};
            assert forall|m: int| 0 <= m < n implies is_valid_edwards_point(
                #[trigger] unwrapped_points[m],
            ) by {
                assert(pi.produces()[m]);
                assert(is_well_formed_edwards_point(pi.remaining()[m].unwrap()));
            }
            // pts_affine coordinates are always < p()
            assert forall|m: int| 0 <= m < n implies (#[trigger] pts_affine[m]).0 < p()
                && pts_affine[m].1 < p() by {
                lemma_edwards_point_as_affine_canonical(unwrapped_points[m]);
            }
            assert forall|m: int| 0 <= m < n implies is_on_edwards_curve(
                (#[trigger] pts_affine[m]).0,
                pts_affine[m].1,
            ) by {
                lemma_edwards_point_as_affine_on_curve(unwrapped_points[m]);
            }
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
        while i > 0
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
                // Preparation loop postconditions preserved (bundled)
                straus_vt_input_valid(
                    nafs@,
                    lookup_tables@,
                    nafs_seqs,
                    pts_affine,
                    spec_scalars,
                    spec_points,
                    unwrapped_points,
                    n,
                ),
                // Scalar reconstruction (kept separate from predicate to avoid inner-loop rlimit)
                forall|k: int|
                    0 <= k < n ==> reconstruct(#[trigger] nafs_seqs[k]) == scalar_as_nat(
                        &spec_scalars[k],
                    ) as int,
            decreases i,
        {
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
                // doubled_affine coords < p() (field_mul returns (a*b)%p < p)
                p_gt_2();
                // edwards_add(doubled, identity) == doubled
                lemma_edwards_add_identity_right_canonical(doubled_affine);
                assert(is_on_edwards_curve(doubled_affine.0, doubled_affine.1));
            }

            while j < min_len
                invariant
                    0 <= j <= min_len,
                    min_len == n,
                    0 <= i < 256,
                    is_valid_completed_point(t),
                    fe51_limbs_bounded(&t.X, 54),
                    fe51_limbs_bounded(&t.Y, 54),
                    fe51_limbs_bounded(&t.Z, 54),
                    fe51_limbs_bounded(&t.T, 54),
                    is_on_edwards_curve(doubled_affine.0, doubled_affine.1),
                    // t = edwards_add(doubled_prev, column_sum(i, j))
                    completed_point_as_affine_edwards(t) == {
                        let col_j = straus_column_sum(pts_affine, nafs_seqs, i as int, j as int);
                        edwards_add(doubled_affine.0, doubled_affine.1, col_j.0, col_j.1)
                    },
                    // Preserved preparation invariants (bundled to reduce rlimit)
                    straus_vt_input_valid(
                        nafs@,
                        lookup_tables@,
                        nafs_seqs,
                        pts_affine,
                        spec_scalars,
                        spec_points,
                        unwrapped_points,
                        n,
                    ),
                decreases min_len - j,
            {
                let naf = &nafs[j];
                let lookup_table = &lookup_tables[j];

                match naf[i].cmp(&0) {
                    Ordering::Greater => {
                        proof {
                            let digit = naf@[i as int];
                            assert(1 <= digit && digit <= 15 && (digit as int) % 2 != 0) by {
                                assert(is_valid_naf(nafs_seqs[j as int], 5));
                                assert(pow2(4) == 16) by {
                                    vstd::arithmetic::power2::lemma2_to64();
                                }
                            }
                            lemma_naf_digit_positive_select_preconditions(digit);
                        }
                        /* ORIGINAL CODE: t = &t.as_extended() + &lookup_table.select(naf[i] as usize) */
                        let R_j = lookup_table.select(naf[i] as usize);
                        t = &t.as_extended() + &R_j;
                        proof {
                            let base_j = pts_affine[j as int];
                            let digit_val = nafs_seqs[j as int][i as int];
                            let term_j = edwards_scalar_mul_signed(base_j, digit_val as int);
                            let col_j = straus_column_sum(
                                pts_affine,
                                nafs_seqs,
                                i as int,
                                j as int,
                            );
                            let ghost digit_i8 = naf@[i as int];

                            // Scope the select lemma to limit Z3 quantifier pressure
                            assert(projective_niels_point_as_affine_edwards(R_j)
                                == edwards_scalar_mul_signed(base_j, digit_i8 as int)) by {
                                assert(base_j == edwards_point_as_affine(
                                    spec_points[j as int].unwrap(),
                                ));
                                lemma_naf_select_is_signed_scalar_mul_projective(
                                    lookup_table.0,
                                    digit_i8,
                                    R_j,
                                    base_j,
                                    true,
                                );
                            }

                            assert(completed_point_as_affine_edwards(t) == {
                                let col_next = straus_column_sum(
                                    pts_affine,
                                    nafs_seqs,
                                    i as int,
                                    (j + 1) as int,
                                );
                                edwards_add(
                                    doubled_affine.0,
                                    doubled_affine.1,
                                    col_next.0,
                                    col_next.1,
                                )
                            }) by {
                                lemma_column_sum_on_curve(
                                    pts_affine,
                                    nafs_seqs,
                                    i as int,
                                    j as int,
                                );
                                lemma_edwards_scalar_mul_signed_on_curve(base_j, digit_val as int);
                                axiom_edwards_add_associative(
                                    doubled_affine.0,
                                    doubled_affine.1,
                                    col_j.0,
                                    col_j.1,
                                    term_j.0,
                                    term_j.1,
                                );
                            }
                        }
                    },
                    Ordering::Less => {
                        proof {
                            let digit = naf@[i as int];
                            assert(-15 <= digit && digit <= -1 && (digit as int) % 2 != 0) by {
                                assert(is_valid_naf(nafs_seqs[j as int], 5));
                                assert(pow2(4) == 16) by {
                                    vstd::arithmetic::power2::lemma2_to64();
                                }
                            }
                            lemma_naf_digit_negative_select_preconditions(digit);
                        }
                        /* ORIGINAL CODE: t = &t.as_extended() - &lookup_table.select(-naf[i] as usize) */
                        let R_j = lookup_table.select((-naf[i]) as usize);
                        t = &t.as_extended() - &R_j;
                        proof {
                            let base_j = pts_affine[j as int];
                            let digit_val = nafs_seqs[j as int][i as int];
                            let term_j = edwards_scalar_mul_signed(base_j, digit_val as int);
                            let col_j = straus_column_sum(
                                pts_affine,
                                nafs_seqs,
                                i as int,
                                j as int,
                            );

                            let ghost neg_digit = (-(naf@[i as int])) as i8;

                            // select(|d|) decodes to [|d|]*P
                            assert(projective_niels_point_as_affine_edwards(R_j)
                                == edwards_scalar_mul_signed(base_j, neg_digit as int)) by {
                                assert(base_j == edwards_point_as_affine(
                                    spec_points[j as int].unwrap(),
                                ));
                                lemma_naf_select_is_signed_scalar_mul_projective(
                                    lookup_table.0,
                                    neg_digit,
                                    R_j,
                                    base_j,
                                    true,
                                );
                            }

                            // sub(t, R_j) = add(t, neg(R_j))
                            // neg([|d|]*P) = [-|d|]*P = [d]*P  (since d < 0, |d| = -d)
                            assert(term_j == edwards_neg(
                                projective_niels_point_as_affine_edwards(R_j),
                            )) by {
                                assert(base_j.0 < p() && base_j.1 < p());
                                lemma_neg_of_signed_scalar_mul(base_j, neg_digit as int);
                                assert(digit_val as int == -(neg_digit as int));
                            }

                            assert(completed_point_as_affine_edwards(t) == {
                                let col_next = straus_column_sum(
                                    pts_affine,
                                    nafs_seqs,
                                    i as int,
                                    (j + 1) as int,
                                );
                                edwards_add(
                                    doubled_affine.0,
                                    doubled_affine.1,
                                    col_next.0,
                                    col_next.1,
                                )
                            }) by {
                                lemma_column_sum_on_curve(
                                    pts_affine,
                                    nafs_seqs,
                                    i as int,
                                    j as int,
                                );
                                lemma_edwards_scalar_mul_signed_on_curve(base_j, digit_val as int);
                                axiom_edwards_add_associative(
                                    doubled_affine.0,
                                    doubled_affine.1,
                                    col_j.0,
                                    col_j.1,
                                    term_j.0,
                                    term_j.1,
                                );
                            }
                        }
                    },
                    Ordering::Equal => {
                        proof {
                            // digit == 0: column sum doesn't change
                            assert(straus_column_sum(
                                pts_affine,
                                nafs_seqs,
                                i as int,
                                (j + 1) as int,
                            ) == straus_column_sum(pts_affine, nafs_seqs, i as int, j as int)) by {
                                lemma_column_sum_canonical(
                                    pts_affine,
                                    nafs_seqs,
                                    i as int,
                                    j as int,
                                );
                                lemma_column_sum_step_zero_digit(
                                    pts_affine,
                                    nafs_seqs,
                                    i as int,
                                    j as int,
                                );
                            }
                        }
                    },
                }
                j = j + 1;
            }

            r = t.as_projective();

            proof {
                // After inner loop: j == n, t = edwards_add(doubled, column_sum(i, n))
                // r = t.as_projective(), affine preserved
                // straus_vt_step(i): vt_partial(i) = edwards_add(doubled(vt_partial(i+1)), column_sum(i, n))
                // doubled_affine = edwards_double(projective_point_as_affine_edwards(r_old))
                //                = edwards_double(straus_vt_partial(i+1))  [from outer invariant]
                // So r affine = t affine = edwards_add(doubled_affine, col(i,n)) = straus_vt_partial(i)
                lemma_straus_vt_step(pts_affine, nafs_seqs, i as int);
            }
        }
        /* </REFACTORED CODE> */

        // r.as_extended() requires valid projective point + 54-bit limbs
        proof {
            crate::lemmas::field_lemmas::add_lemmas::lemma_fe51_limbs_bounded_weaken(&r.X, 52, 54);
            crate::lemmas::field_lemmas::add_lemmas::lemma_fe51_limbs_bounded_weaken(&r.Y, 52, 54);
            crate::lemmas::field_lemmas::add_lemmas::lemma_fe51_limbs_bounded_weaken(&r.Z, 52, 54);
        }
        let result = r.as_extended();

        proof {
            // Each NAF has length 256 (from [i8; 256]@ mapping)
            assert forall|k: int| 0 <= k < nafs_seqs.len() implies {
                &&& (#[trigger] nafs_seqs[k]).len() == 256
                &&& is_valid_naf(nafs_seqs[k], 5)
                &&& reconstruct(nafs_seqs[k]) == scalar_as_nat(&spec_scalars[k]) as int
            } by {
                assert(nafs_seqs[k] == nafs@[k]@);
            };

            // r affine == straus_vt_partial(0) == sum_of_scalar_muls
            lemma_straus_vt_correct(spec_scalars, unwrapped_points, pts_affine, nafs_seqs);
            assert(edwards_point_as_affine(result) == projective_point_as_affine_edwards(r));
            // is_well_formed follows from ProjectivePoint::as_extended postcondition
            assert(is_well_formed_edwards_point(result));
        }

        proof {
            lemma_straus_result(si, pi, ss, result);
        }
        Some(result)
    }
}

/// Transfer the sum over the prepared inputs to the original iterators.
proof fn lemma_straus_result<I, J>(si: I, pi: J, ss: Seq<Scalar>, result: EdwardsPoint) where
    I: Iterator,
    I::Item: Borrow<Scalar>,
    J: Iterator<Item = Option<EdwardsPoint>>,

    requires
        forall|k: int| 0 <= k < si.remaining().len() ==> #[trigger] si.produces()[k],
        forall|k: int|
            0 <= k < pi.remaining().len() ==> #[trigger] pi.produces()[k]
                && pi.remaining()[k].is_some(),
        borrowed_values(si.remaining(), ss),
        Straus::vartime_sum(ss, unwrap_points(pi.remaining()), result),
    ensures
        optional_iter_outcome(si, pi, Some(result), |ss, ps, r| Straus::vartime_sum(ss, ps, r)),
{
    let ps = pi.remaining().map(|_, p: Option<EdwardsPoint>| p.unwrap());
    assert(ps =~= unwrap_points(pi.remaining()));
    assert(Straus::vartime_sum(ss, ps, result));
}

impl Straus {
    /// Verified version of multiscalar_mul (constant-time) over slices.
    /// Computes sum(scalars[i] * points[i]).
    pub fn multiscalar_mul_verus(scalars: &[Scalar], points: &[EdwardsPoint]) -> (result:
        EdwardsPoint)
        requires
    // Same number of scalars and points

            scalars@.len() == points@.len(),
            // Bit 255 of every scalar is clear (Scalar invariant #1)
            forall|i: int| #![auto] 0 <= i < scalars@.len() ==> scalars@[i].bytes[31] <= 127,
            // All input points must be well-formed
            forall|i: int|
                0 <= i < points@.len() ==> is_well_formed_edwards_point(#[trigger] points@[i]),
        ensures
            is_well_formed_edwards_point(result),
            // Semantic correctness: result = sum(scalars[i] * points[i])
            edwards_point_as_affine(result) == sum_of_scalar_muls(scalars@, points@),
    {
        let ghost spec_scalars = scalars@;
        let ghost spec_points = points@;

        /* <ORIGINAL CODE>
        let lookup_tables: Vec<_> = points
            .into_iter()
            .map(|point| LookupTable::<ProjectiveNielsPoint>::from(point.borrow()))
            .collect();
        </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Build lookup tables for each point: precompute multiples [1P, 2P, ..., 8P]
         * (Verus doesn't support iterator adapters.)
         */
        let mut lookup_tables: Vec<LookupTable<ProjectiveNielsPoint>> = Vec::new();
        let mut idx: usize = 0;
        while idx < points.len()
            invariant
                0 <= idx <= points@.len(),
                lookup_tables@.len() == idx as int,
                points@ == spec_points,
                // All input points are well-formed (from function precondition)
                forall|k: int|
                    0 <= k < points@.len() ==> is_well_formed_edwards_point(#[trigger] points@[k]),
                // Each table is valid, has bounded limbs, and entries are valid
                forall|k: int|
                    0 <= k < idx ==> {
                        &&& is_valid_lookup_table_projective(
                            (#[trigger] lookup_tables@[k]).0,
                            points@[k],
                            8,
                        )
                        &&& lookup_table_projective_limbs_bounded(lookup_tables@[k].0)
                        &&& forall|j: int|
                            0 <= j < 8 ==> is_valid_projective_niels_point(
                                #[trigger] lookup_tables@[k].0[j],
                            )
                    },
            decreases points.len() - idx,
        {
            lookup_tables.push(LookupTable::<ProjectiveNielsPoint>::from(&points[idx]));
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
        // Reserve every digit array up front so reallocation cannot leave a copy behind.
        let mut scalar_digits: Vec<[i8; 64]> = Vec::with_capacity(scalars.len());
        idx = 0;
        while idx < scalars.len()
            invariant
                0 <= idx <= scalars@.len(),
                scalar_digits@.len() == idx as int,
                scalars@ == spec_scalars,
                // Bit 255 of every scalar is clear (from the precondition)
                forall|k: int| #![auto] 0 <= k < scalars@.len() ==> scalars@[k].bytes[31] <= 127,
                // Each digit array is valid radix-16
                forall|k: int|
                    #![auto]
                    0 <= k < idx ==> {
                        &&& is_valid_radix_16(&#[trigger] scalar_digits@[k])
                        &&& radix_16_all_bounded(&scalar_digits@[k])
                        &&& reconstruct_radix_16(scalar_digits@[k]@) == scalar_as_nat(
                            &scalars@[k],
                        ) as int
                    },
            decreases scalars.len() - idx,
        {
            scalar_digits.push(scalars[idx].as_radix_16());
            idx = idx + 1;
        }
        /* </REFACTORED CODE> */

        assert(prepared_inputs(lookup_tables@, scalar_digits@, spec_scalars, spec_points));
        let result = Self::multiscalar_mul_prepared(
            lookup_tables.as_slice(),
            scalar_digits.as_slice(),
        );
        #[cfg(feature = "zeroize")]
        zeroize_scalar_digits(&mut scalar_digits);
        result
    }

    /// Compute the multiscalar sum from the lookup tables and scalar digits prepared by the caller.
    fn multiscalar_mul_prepared(
        lookup_tables: &[LookupTable<ProjectiveNielsPoint>],
        scalar_digits: &[[i8; 64]],
    ) -> (result: EdwardsPoint)
        requires
            exists|ss: Seq<Scalar>, ps: Seq<EdwardsPoint>| #[trigger]
                prepared_inputs(lookup_tables@, scalar_digits@, ss, ps),
        ensures
            is_well_formed_edwards_point(result),
            forall|ss: Seq<Scalar>, ps: Seq<EdwardsPoint>| #[trigger]
                prepared_inputs(lookup_tables@, scalar_digits@, ss, ps) ==> edwards_point_as_affine(
                    result,
                ) == sum_of_scalar_muls(ss, ps),
    {
        let ghost (spec_scalars, spec_points) = choose|ss: Seq<Scalar>, ps: Seq<EdwardsPoint>|
         #[trigger]
            prepared_inputs(lookup_tables@, scalar_digits@, ss, ps);
        let ghost n = spec_scalars.len();
        let ghost pts_affine: Seq<(nat, nat)> = points_to_affine(spec_points);
        let ghost digits_seqs: Seq<Seq<i8>> = scalar_digits@.map(|_i, d: [i8; 64]| d@);

        /* UNCHANGED FROM ORIGINAL */
        let mut Q = EdwardsPoint::identity();

        proof {
            // Q starts as identity = straus_ct_partial(64)
            assert(is_well_formed_edwards_point(Q));
            lemma_straus_ct_base(pts_affine, digits_seqs);
            // Connect: identity point has affine (0, 1) = edwards_identity
            lemma_identity_affine_coords(Q);
            assert(edwards_point_as_affine(Q) == edwards_identity());
            assert(edwards_point_as_affine(Q) == straus_ct_partial(pts_affine, digits_seqs, 64));
            assert forall|m: int| 0 <= m < n implies is_on_edwards_curve(
                (#[trigger] pts_affine[m]).0,
                pts_affine[m].1,
            ) by {
                lemma_edwards_point_as_affine_on_curve(spec_points[m]);
            }
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
        while j > 0
            invariant
                0 <= j <= 64,
                is_well_formed_edwards_point(Q),
                // Functional correctness: Q = straus_ct_partial(pts, digits, j)
                edwards_point_as_affine(Q) == straus_ct_partial(pts_affine, digits_seqs, j as int),
                // Preparation loop postconditions preserved (bundled)
                straus_ct_input_valid(
                    scalar_digits@,
                    lookup_tables@,
                    digits_seqs,
                    pts_affine,
                    spec_scalars,
                    spec_points,
                    n,
                ),
                // Scalar digit validity + reconstruction (kept separate from predicate to avoid inner-loop rlimit)
                forall|k: int|
                    #![auto]
                    0 <= k < n ==> is_valid_radix_16(&#[trigger] scalar_digits@[k]),
                forall|k: int|
                    0 <= k < n ==> reconstruct_radix_16((#[trigger] scalar_digits@[k])@)
                        == scalar_as_nat(&spec_scalars[k]) as int,
            decreases j,
        {
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
                assert(min_len == n);
                // At k=0: col(j,0) = O (identity), so edwards_add(scaled, O) == scaled
                lemma_edwards_point_as_affine_canonical(Q);
                lemma_edwards_add_identity_right_canonical(scaled_affine);
                lemma_edwards_point_as_affine_on_curve(Q);
            }

            while k < min_len
                invariant
                    0 <= k <= min_len,
                    min_len == n,
                    0 <= j < 64,
                    is_well_formed_edwards_point(Q),
                    is_on_edwards_curve(scaled_affine.0, scaled_affine.1),
                    // Q = edwards_add(scaled_prev, column_sum(j, k))
                    edwards_point_as_affine(Q) == {
                        let col_k = straus_column_sum(pts_affine, digits_seqs, j as int, k as int);
                        edwards_add(scaled_affine.0, scaled_affine.1, col_k.0, col_k.1)
                    },
                    // Preserved preparation invariants (bundled)
                    straus_ct_input_valid(
                        scalar_digits@,
                        lookup_tables@,
                        digits_seqs,
                        pts_affine,
                        spec_scalars,
                        spec_points,
                        n,
                    ),
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
                    // Scope the select lemma to limit Z3 quantifier pressure
                    let base_k = pts_affine[k as int];
                    let ghost digit_kj = s_i@[j as int];
                    assert(projective_niels_point_as_affine_edwards(R_i)
                        == edwards_scalar_mul_signed(base_k, digit_kj as int)) by {
                        assert(base_k == edwards_point_as_affine(spec_points[k as int]));
                        lemma_select_is_signed_scalar_mul_projective(
                            lookup_table_i.0,
                            digit_kj,
                            R_i,
                            base_k,
                        );
                    }
                }

                Q = (&Q + &R_i).as_extended();

                proof {
                    // After add + as_extended:
                    // Q_new_affine == spec_edwards_add_projective_niels(Q_old, R_i)
                    //              == edwards_add(Q_old_affine, R_i_affine)
                    // Q_old_affine == edwards_add(scaled, col_k) [from invariant]
                    // R_i_affine == term_k [from select lemma]
                    let col_k = straus_column_sum(pts_affine, digits_seqs, j as int, k as int);
                    let base_k = pts_affine[k as int];
                    let digit_kj = digits_seqs[k as int][j as int];
                    let term_k = edwards_scalar_mul_signed(base_k, digit_kj as int);

                    // By associativity: edwards_add(edwards_add(S, Ck), R) == edwards_add(S, edwards_add(Ck, R))
                    lemma_column_sum_on_curve(pts_affine, digits_seqs, j as int, k as int);
                    lemma_edwards_scalar_mul_signed_on_curve(base_k, digit_kj as int);
                    axiom_edwards_add_associative(
                        scaled_affine.0,
                        scaled_affine.1,
                        col_k.0,
                        col_k.1,
                        term_k.0,
                        term_k.1,
                    );
                    // Column sum step: edwards_add(col_k, term_k) == col_{k+1}
                    // digits_seqs[k] has length 64 (view of [i8; 64])
                    assert(digits_seqs[k as int] == scalar_digits@[k as int]@);
                    assert(digits_seqs[k as int].len() == 64);
                }

                k = k + 1;
            }

            proof {
                // After inner loop: k == n, so Q = edwards_add(scaled, column_sum(j, n))
                // This equals straus_ct_partial(j) by definition
                lemma_straus_ct_step(pts_affine, digits_seqs, j as int);

                // scaled_affine == edwards_scalar_mul(straus_ct_partial(j+1), pow2(4))
                // pow2(4) == 16
                vstd::arithmetic::power2::lemma2_to64();
                assert(pow2(4) == 16nat);
                // So scaled_affine == edwards_scalar_mul(straus_ct_partial(j+1), 16)
                // And Q == edwards_add(scaled_affine, column_sum(j, n)) == straus_ct_partial(j)
            }
        }
        /* </REFACTORED CODE> */

        // Final: Q = straus_ct_partial(0) == sum_of_scalar_muls(spec_scalars, spec_points)
        proof {
            // Axiom preconditions
            assert(spec_scalars.len() == spec_points.len());
            assert(pts_affine.len() == spec_scalars.len()) by {
                assert(pts_affine.len() == n);
                assert(n == spec_scalars.len());
            };
            assert(digits_seqs.len() == spec_scalars.len()) by {
                assert(digits_seqs.len() == n);
                assert(n == spec_scalars.len());
            };

            // Bridge: pts_affine == affine forms of spec_points
            assert forall|k: int| 0 <= k < pts_affine.len() implies #[trigger] pts_affine[k]
                == edwards_point_as_affine(spec_points[k]) by {};

            // Bridge radix_16_all_bounded (array) to radix_16_all_bounded_seq (Seq) + len == 64
            assert forall|k: int| 0 <= k < digits_seqs.len() implies {
                &&& (#[trigger] digits_seqs[k]).len() == 64
                &&& radix_16_all_bounded_seq(digits_seqs[k])
                &&& reconstruct_radix_16(digits_seqs[k]) == scalar_as_nat(&spec_scalars[k]) as int
            } by {
                assert(digits_seqs[k] == scalar_digits@[k]@);
                assert(radix_16_all_bounded(&scalar_digits@[k]));
                assert(reconstruct_radix_16(scalar_digits@[k]@) == scalar_as_nat(
                    &spec_scalars[k],
                ) as int);
            };

            assert forall|ss: Seq<Scalar>, ps: Seq<EdwardsPoint>| #[trigger]
                prepared_inputs(
                    lookup_tables@,
                    scalar_digits@,
                    ss,
                    ps,
                ) implies edwards_point_as_affine(Q) == sum_of_scalar_muls(ss, ps) by {
                assert forall|k: int| 0 <= k < pts_affine.len() implies #[trigger] pts_affine[k]
                    == edwards_point_as_affine(ps[k]) by {
                    let first = lookup_tables@[k].0[0];
                    assert(projective_niels_point_as_affine_edwards(first) == edwards_scalar_mul(
                        edwards_point_as_affine(ps[k]),
                        1,
                    ));
                    assert(projective_niels_point_as_affine_edwards(first) == edwards_scalar_mul(
                        edwards_point_as_affine(spec_points[k]),
                        1,
                    ));
                }
                assert forall|k: int| 0 <= k < digits_seqs.len() implies reconstruct_radix_16(
                    #[trigger] digits_seqs[k],
                ) == scalar_as_nat(&ss[k]) as int by {
                    assert(straus_digits_for(scalar_digits@[k], ss[k]));
                }
                lemma_straus_ct_correct(ss, ps, pts_affine, digits_seqs);
            }
        }

        Q
    }
}

/// Inputs represented by the prepared Straus tables and digits.
spec fn prepared_inputs(
    tables: Seq<LookupTable<ProjectiveNielsPoint>>,
    digits: Seq<[i8; 64]>,
    ss: Seq<Scalar>,
    ps: Seq<EdwardsPoint>,
) -> bool {
    &&& ss.len() == ps.len() && ss.len() == digits.len() && ps.len() == tables.len()
    &&& forall|k: int| 0 <= k < ps.len() ==> is_well_formed_edwards_point(#[trigger] ps[k])
    &&& forall|k: int| 0 <= k < ps.len() ==> straus_table_for(#[trigger] tables[k], ps[k])
    &&& forall|k: int| 0 <= k < ss.len() ==> straus_digits_for(#[trigger] digits[k], ss[k])
}

spec fn straus_table_for(table: LookupTable<ProjectiveNielsPoint>, point: EdwardsPoint) -> bool {
    &&& is_valid_lookup_table_projective(table.0, point, 8)
    &&& lookup_table_projective_limbs_bounded(table.0)
    &&& forall|j: int| 0 <= j < 8 ==> is_valid_projective_niels_point(#[trigger] table.0[j])
}

spec fn straus_digits_for(digits: [i8; 64], scalar: Scalar) -> bool {
    &&& is_valid_radix_16(&digits)
    &&& radix_16_all_bounded(&digits)
    &&& reconstruct_radix_16(digits@) == scalar_as_nat(&scalar) as int
}

// impl Straus
} // verus!
