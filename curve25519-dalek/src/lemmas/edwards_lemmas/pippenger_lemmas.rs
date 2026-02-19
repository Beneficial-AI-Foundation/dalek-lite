//! Lemmas for Pippenger (bucket method) multiscalar multiplication.
//!
//! This module contains specs and proofs connecting Pippenger's bucket-based
//! evaluation to the `sum_of_scalar_muls` specification.
//!
//! ## Key specs:
//! - `pippenger_bucket_contents`: What each bucket holds after processing n points
//! - `pippenger_horner`: Horner accumulator over digit columns with window w
//!
//! ## Key lemmas:
//! - `axiom_bucket_weighted_sum_equals_column_sum`: Bucket method = column sum
//! - `lemma_pippenger_horner_step`: Unfolds Horner one step
//! - `lemma_pippenger_single`: Single-point Horner = scalar multiplication
//! - `lemma_pippenger_horner_correct`: Multi-point correctness theorem
#![allow(non_snake_case)]
#![allow(unused_imports)]

use crate::backend::serial::curve_models::ProjectiveNielsPoint;
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;

#[cfg(verus_keep_ghost)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
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
use vstd::arithmetic::power2::pow2;

use vstd::prelude::*;

verus! {

// =============================================================================
// Spec: bucket contents after processing n points at a given column
// =============================================================================
/// What bucket `b` (0-indexed, representing digit value b+1) holds after
/// processing `n` points at digit column `col`.
///
/// If point i has digit (b+1) at column col, it's added to the bucket.
/// If point i has digit -(b+1), it's subtracted.
/// Otherwise, the bucket is unchanged.
pub open spec fn pippenger_bucket_contents(
    points_affine: Seq<(nat, nat)>,
    all_digits: Seq<Seq<i8>>,
    col: int,
    n: int,
    b: int,
) -> (nat, nat)
    decreases n,
{
    if n <= 0 {
        math_edwards_identity()
    } else {
        let prev = pippenger_bucket_contents(points_affine, all_digits, col, n - 1, b);
        let d = all_digits[n - 1][col] as int;
        let pt = points_affine[n - 1];
        if d == (b + 1) {
            edwards_add(prev.0, prev.1, pt.0, pt.1)
        } else if d == -(b + 1) {
            edwards_sub(prev.0, prev.1, pt.0, pt.1)
        } else {
            prev
        }
    }
}

// =============================================================================
// Spec: weighted sum of buckets (what the intermediate-sum trick computes)
// =============================================================================
/// Weighted sum: sum_{b=0}^{num_buckets-1} (b+1) * bucket[b]
///
/// This is the mathematical definition of what Pippenger's bucket sum produces.
pub open spec fn pippenger_weighted_bucket_sum(
    buckets_affine: Seq<(nat, nat)>,
    num_buckets: int,
) -> (nat, nat)
    decreases num_buckets,
{
    if num_buckets <= 0 {
        math_edwards_identity()
    } else {
        let prev = pippenger_weighted_bucket_sum(buckets_affine, num_buckets - 1);
        let bucket = buckets_affine[num_buckets - 1];
        let weighted = edwards_scalar_mul(bucket, num_buckets as nat);
        edwards_add(prev.0, prev.1, weighted.0, weighted.1)
    }
}

// =============================================================================
// Spec: intermediate sum (running sum from bucket B-1 down to b)
// =============================================================================
/// intermediate_sum(b, B) = bucket[B-1] + bucket[B-2] + ... + bucket[b]
pub open spec fn pippenger_intermediate_sum(buckets_affine: Seq<(nat, nat)>, b: int, B: int) -> (
    nat,
    nat,
)
    decreases B - b,
{
    if b >= B {
        math_edwards_identity()
    } else if b == B - 1 {
        buckets_affine[b]
    } else {
        let next = pippenger_intermediate_sum(buckets_affine, b + 1, B);
        edwards_add(next.0, next.1, buckets_affine[b].0, buckets_affine[b].1)
    }
}

// =============================================================================
// Spec: running sum of intermediate sums (the output of the bucket sum trick)
// =============================================================================
/// running_sum(b, B) = sum_{k=b}^{B-1} intermediate_sum(k, B)
///
/// At b=0 this equals the weighted bucket sum: sum_{b=0}^{B-1} (b+1)*bucket[b]
pub open spec fn pippenger_running_sum(buckets_affine: Seq<(nat, nat)>, b: int, B: int) -> (
    nat,
    nat,
)
    decreases B - b,
{
    if b >= B {
        math_edwards_identity()
    } else if b == B - 1 {
        buckets_affine[b]
    } else {
        let rest = pippenger_running_sum(buckets_affine, b + 1, B);
        let inter = pippenger_intermediate_sum(buckets_affine, b, B);
        edwards_add(rest.0, rest.1, inter.0, inter.1)
    }
}

// =============================================================================
// Spec: Pippenger Horner accumulator (generalized from straus_ct_partial)
// =============================================================================
/// Horner accumulation over digit columns with window size w.
///
///   pippenger_horner(from_col) = pow2(w) * pippenger_horner(from_col+1) + column_sum(from_col)
///
/// This reuses `straus_column_sum` since the column sum is the same mathematical object
/// regardless of whether it's computed via direct accumulation (Straus) or buckets (Pippenger).
#[verifier::opaque]
pub open spec fn pippenger_horner(
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
    from_col: int,
    w: nat,
    digits_count: nat,
) -> (nat, nat)
    decreases digits_count as int - from_col,
{
    if from_col >= digits_count as int {
        math_edwards_identity()
    } else {
        let prev = pippenger_horner(points_affine, digits, from_col + 1, w, digits_count);
        let scaled = edwards_scalar_mul(prev, pow2(w));
        let col = straus_column_sum(points_affine, digits, from_col, points_affine.len() as int);
        edwards_add(scaled.0, scaled.1, col.0, col.1)
    }
}

// =============================================================================
// Lemma: Unfold pippenger_horner one step
// =============================================================================
pub proof fn lemma_pippenger_horner_step(
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
    j: int,
    w: nat,
    digits_count: nat,
)
    requires
        0 <= j < digits_count as int,
    ensures
        pippenger_horner(points_affine, digits, j, w, digits_count) == {
            let prev = pippenger_horner(points_affine, digits, j + 1, w, digits_count);
            let scaled = edwards_scalar_mul(prev, pow2(w));
            let col = straus_column_sum(points_affine, digits, j, points_affine.len() as int);
            edwards_add(scaled.0, scaled.1, col.0, col.1)
        },
{
    reveal(pippenger_horner);
}

// =============================================================================
// Lemma: Base case — pippenger_horner at digits_count is identity
// =============================================================================
pub proof fn lemma_pippenger_horner_base(
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
    w: nat,
    digits_count: nat,
)
    ensures
        pippenger_horner(points_affine, digits, digits_count as int, w, digits_count)
            == math_edwards_identity(),
{
    reveal(pippenger_horner);
}

// =============================================================================
// Lemma: Zero-points Horner is identity
// =============================================================================
pub proof fn lemma_pippenger_zero_points_from(
    pts: Seq<(nat, nat)>,
    digs: Seq<Seq<i8>>,
    j: int,
    w: nat,
    digits_count: nat,
)
    requires
        pts.len() == 0,
        digs.len() == 0,
        0 <= j <= digits_count as int,
    ensures
        pippenger_horner(pts, digs, j, w, digits_count) == math_edwards_identity(),
    decreases digits_count as int - j,
{
    if j >= digits_count as int {
        lemma_pippenger_horner_base(pts, digs, w, digits_count);
    } else {
        lemma_pippenger_horner_step(pts, digs, j, w, digits_count);
        lemma_pippenger_zero_points_from(pts, digs, j + 1, w, digits_count);
        // [pow2(w)]*identity = identity
        lemma_edwards_scalar_mul_identity(pow2(w));
        let id = math_edwards_identity();
        p_gt_2();
        lemma_edwards_add_identity_right_canonical(id);
    }
}

// =============================================================================
// Lemma: Single-point Horner = [reconstruct_radix_2w_from(d, w, j, dc)] * P
// =============================================================================
pub proof fn lemma_pippenger_single(P: (nat, nat), d: Seq<i8>, j: int, w: nat, digits_count: nat)
    requires
        d.len() >= digits_count as int,
        P.0 < p(),
        P.1 < p(),
        0 <= j <= digits_count as int,
        w >= 1,
    ensures
        pippenger_horner(seq![(P)], seq![(d)], j, w, digits_count) == edwards_scalar_mul_signed(
            P,
            reconstruct_radix_2w_from(d, w, j, digits_count),
        ),
    decreases digits_count as int - j,
{
    if j >= digits_count as int {
        // Base: pippenger_horner(..., dc) == identity
        lemma_pippenger_horner_base(seq![(P)], seq![(d)], w, digits_count);
        // reconstruct_radix_2w_from(d, w, dc, dc) == 0
        // edwards_scalar_mul_signed(P, 0) == identity
        reveal(edwards_scalar_mul_signed);
        reveal_with_fuel(edwards_scalar_mul, 1);
    } else {
        // Unfold pippenger_horner one step
        lemma_pippenger_horner_step(seq![(P)], seq![(d)], j, w, digits_count);

        // IH: pippenger_horner(seq![P], seq![d], j+1, w, dc) == [reconstruct_from(d, w, j+1, dc)]*P
        lemma_pippenger_single(P, d, j + 1, w, digits_count);
        let r_next = reconstruct_radix_2w_from(d, w, j + 1, digits_count);

        // [pow2(w)] * [r_next]*P == [pow2(w) * r_next]*P
        lemma_edwards_scalar_mul_signed_composition(P, r_next, pow2(w));

        // column_sum(seq![P], seq![d], j, 1) == [d[j]]*P
        lemma_column_sum_single(P, d, j);

        // [pow2(w)*r_next]*P + [d[j]]*P == [pow2(w)*r_next + d[j]]*P
        axiom_edwards_scalar_mul_signed_additive(P, pow2(w) as int * r_next, d[j] as int);

        // pow2(w)*r_next + d[j] == reconstruct_radix_2w_from(d, w, j, dc)
        // (from definition: reconstruct(d, w, j, dc) = d[j] + pow2(w) * reconstruct(d, w, j+1, dc))
        assert(d[j] as int + pow2(w) as int * r_next == reconstruct_radix_2w_from(
            d,
            w,
            j,
            digits_count,
        ));
    }
}

// =============================================================================
// Lemma: Pippenger peel-last (splitting off the last point)
// =============================================================================
/// The Horner evaluation over n points equals the sum of:
/// - the Horner evaluation over the first (n-1) points, plus
/// - the Horner evaluation for the last point alone.
pub proof fn lemma_pippenger_peel_last(
    pts: Seq<(nat, nat)>,
    digs: Seq<Seq<i8>>,
    j: int,
    w: nat,
    digits_count: nat,
)
    requires
        pts.len() >= 1,
        digs.len() == pts.len(),
        0 <= j <= digits_count as int,
        forall|k: int| 0 <= k < digs.len() ==> (#[trigger] digs[k]).len() >= digits_count as int,
        forall|k: int| 0 <= k < pts.len() ==> (#[trigger] pts[k]).0 < p() && pts[k].1 < p(),
    ensures
        pippenger_horner(pts, digs, j, w, digits_count) == ({
            let prefix_result = pippenger_horner(
                pts.drop_last(),
                digs.drop_last(),
                j,
                w,
                digits_count,
            );
            let single_result = pippenger_horner(
                seq![(pts.last())],
                seq![(digs.last())],
                j,
                w,
                digits_count,
            );
            edwards_add(prefix_result.0, prefix_result.1, single_result.0, single_result.1)
        }),
    decreases digits_count as int - j,
{
    let n = pts.len() as int;
    let pts_prefix = pts.drop_last();
    let digs_prefix = digs.drop_last();
    let pts_single = seq![(pts.last())];
    let digs_single = seq![(digs.last())];

    if j >= digits_count as int {
        // Base case: all three terms are identity
        lemma_pippenger_horner_base(pts, digs, w, digits_count);
        lemma_pippenger_horner_base(pts_prefix, digs_prefix, w, digits_count);
        lemma_pippenger_horner_base(pts_single, digs_single, w, digits_count);
        p_gt_2();
        lemma_edwards_add_identity_right_canonical(math_edwards_identity());
    } else {
        // Unfold pippenger_horner for all three
        lemma_pippenger_horner_step(pts, digs, j, w, digits_count);
        lemma_pippenger_horner_step(pts_prefix, digs_prefix, j, w, digits_count);
        lemma_pippenger_horner_step(pts_single, digs_single, j, w, digits_count);

        // IH at j+1
        lemma_pippenger_peel_last(pts, digs, j + 1, w, digits_count);

        let prev_full = pippenger_horner(pts, digs, j + 1, w, digits_count);
        let prev_prefix = pippenger_horner(pts_prefix, digs_prefix, j + 1, w, digits_count);
        let prev_single = pippenger_horner(pts_single, digs_single, j + 1, w, digits_count);

        // By IH: prev_full == edwards_add(prev_prefix, prev_single)
        // [pow2(w)]*prev_full == [pow2(w)]*edwards_add(prev_prefix, prev_single)
        //                     == edwards_add([pow2(w)]*prev_prefix, [pow2(w)]*prev_single)
        axiom_edwards_scalar_mul_distributive(prev_prefix, prev_single, pow2(w));

        let scaled_prefix = edwards_scalar_mul(prev_prefix, pow2(w));
        let scaled_single = edwards_scalar_mul(prev_single, pow2(w));

        // Column sum splitting
        let col_full = straus_column_sum(pts, digs, j, n);
        let col_prefix = straus_column_sum(pts_prefix, digs_prefix, j, (n - 1));
        let col_single = straus_column_sum(pts_single, digs_single, j, 1);

        lemma_column_sum_prefix_eq(pts, digs, pts_prefix, digs_prefix, j, n - 1);
        lemma_column_sum_single(pts.last(), digs.last(), j);

        // Four-way reassociation: (A+B) + (C+D) = (A+C) + (B+D)
        let a = scaled_prefix;
        let b = scaled_single;
        let c = col_prefix;
        let d_val = col_single;

        let ab = edwards_add(a.0, a.1, b.0, b.1);
        let cd = edwards_add(c.0, c.1, d_val.0, d_val.1);
        let bd = edwards_add(b.0, b.1, d_val.0, d_val.1);
        let ac = edwards_add(a.0, a.1, c.0, c.1);

        axiom_edwards_add_associative(a.0, a.1, b.0, b.1, cd.0, cd.1);
        axiom_edwards_add_associative(b.0, b.1, c.0, c.1, d_val.0, d_val.1);
        lemma_edwards_add_commutative(b.0, b.1, c.0, c.1);
        axiom_edwards_add_associative(c.0, c.1, b.0, b.1, d_val.0, d_val.1);
        axiom_edwards_add_associative(a.0, a.1, c.0, c.1, bd.0, bd.1);

        assert(edwards_add(ab.0, ab.1, cd.0, cd.1) == edwards_add(ac.0, ac.1, bd.0, bd.1));
    }
}

// =============================================================================
// Lemma: reconstruct_radix_2w_from(d, w, 0, dc) == reconstruct_radix_2w(d.take(dc), w)
// =============================================================================
pub proof fn lemma_reconstruct_radix_2w_from_equals_reconstruct(
    d: Seq<i8>,
    w: nat,
    digits_count: nat,
)
    requires
        d.len() >= digits_count as int,
    ensures
        reconstruct_radix_2w_from(d, w, 0, digits_count) == reconstruct_radix_2w(
            d.take(digits_count as int),
            w,
        ),
{
    lemma_reconstruct_radix_2w_from_eq_helper(d, w, 0, digits_count);
    assert(d.subrange(0, digits_count as int) =~= d.take(digits_count as int));
}

proof fn lemma_reconstruct_radix_2w_from_eq_helper(d: Seq<i8>, w: nat, k: int, digits_count: nat)
    requires
        d.len() >= digits_count as int,
        0 <= k <= digits_count as int,
    ensures
        reconstruct_radix_2w_from(d, w, k, digits_count) == reconstruct_radix_2w(
            d.subrange(k, digits_count as int),
            w,
        ),
    decreases digits_count as int - k,
{
    let sub = d.subrange(k, digits_count as int);
    if k >= digits_count as int {
        assert(sub.len() == 0);
    } else {
        lemma_reconstruct_radix_2w_from_eq_helper(d, w, k + 1, digits_count);
        let sub_next = d.subrange(k + 1, digits_count as int);
        assert(sub[0] == d[k]);
        assert(sub.len() == (digits_count as int - k));
        // sub.skip(1) == d.subrange(k+1, dc)
        assert forall|i: int| 0 <= i < sub.skip(1).len() implies sub.skip(1)[i] == sub_next[i] by {
            assert(sub.skip(1)[i] == sub[i + 1]);
            assert(sub[i + 1] == d[k + 1 + i]);
            assert(sub_next[i] == d[k + 1 + i]);
        }
        assert(sub.skip(1) =~= sub_next);
    }
}

// =============================================================================
// Main Pippenger correctness theorem
// =============================================================================
/// Proves: pippenger_horner(points_affine, digits, 0, w, dc) == sum_of_scalar_muls(scalars, points_ep)
///
/// Proof by induction on n (number of points), mirroring lemma_straus_ct_correct.
pub proof fn lemma_pippenger_horner_correct(
    scalars: Seq<Scalar>,
    points_ep: Seq<EdwardsPoint>,
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
    w: nat,
    digits_count: nat,
)
    requires
        scalars.len() == points_ep.len(),
        points_affine.len() == scalars.len(),
        digits.len() == scalars.len(),
        w >= 1,
        forall|k: int|
            0 <= k < points_affine.len() ==> #[trigger] points_affine[k] == edwards_point_as_affine(
                points_ep[k],
            ),
        forall|k: int|
            0 <= k < digits.len() ==> {
                &&& (#[trigger] digits[k]).len() >= digits_count as int
                &&& reconstruct_radix_2w_from(digits[k], w, 0, digits_count) == scalar_as_nat(
                    &scalars[k],
                ) as int
            },
    ensures
        pippenger_horner(points_affine, digits, 0, w, digits_count) == sum_of_scalar_muls(
            scalars,
            points_ep,
        ),
    decreases scalars.len(),
{
    let n = scalars.len();

    if n == 0 {
        lemma_pippenger_zero_points_from(points_affine, digits, 0, w, digits_count);
    } else {
        let last = (n - 1) as int;
        let pts_prefix = points_affine.drop_last();
        let digs_prefix = digits.drop_last();
        let scalars_prefix = scalars.subrange(0, last);
        let points_prefix = points_ep.subrange(0, last);

        // Preconditions for prefix
        assert forall|k: int| 0 <= k < pts_prefix.len() implies #[trigger] pts_prefix[k]
            == edwards_point_as_affine(points_prefix[k]) by {
            assert(pts_prefix[k] == points_affine[k]);
            assert(points_prefix[k] == points_ep[k]);
        }
        assert forall|k: int| 0 <= k < digs_prefix.len() implies {
            &&& (#[trigger] digs_prefix[k]).len() >= digits_count as int
            &&& reconstruct_radix_2w_from(digs_prefix[k], w, 0, digits_count) == scalar_as_nat(
                &scalars_prefix[k],
            ) as int
        } by {
            assert(digs_prefix[k] == digits[k]);
            assert(scalars_prefix[k] == scalars[k]);
        }

        // IH: prefix is correct
        lemma_pippenger_horner_correct(
            scalars_prefix,
            points_prefix,
            pts_prefix,
            digs_prefix,
            w,
            digits_count,
        );

        // Points are canonical
        assert forall|k: int| 0 <= k < points_affine.len() implies (#[trigger] points_affine[k]).0
            < p() && points_affine[k].1 < p() by {
            lemma_edwards_point_as_affine_canonical(points_ep[k]);
        }

        // Digits lengths for peel_last
        assert forall|k: int| 0 <= k < digits.len() implies (#[trigger] digits[k]).len()
            >= digits_count as int by {}

        // Split: pippenger_horner(pts, digs, 0) = prefix_result + single_result
        lemma_pippenger_peel_last(points_affine, digits, 0, w, digits_count);

        // Single point Horner = [scalar_last] * P_last
        let P_last = points_affine.last();
        let d_last = digits.last();
        lemma_pippenger_single(P_last, d_last, 0, w, digits_count);

        // Connect signed to unsigned scalar_mul
        let scalar_nat = scalar_as_nat(&scalars[last]);
        assert(reconstruct_radix_2w_from(d_last, w, 0, digits_count) == scalar_nat as int);
        reveal(edwards_scalar_mul_signed);
    }
}

// =============================================================================
// Axiom: Bucket weighted sum equals column sum
// =============================================================================
/// The weighted bucket sum equals the column sum (straus_column_sum).
///
/// This is the key mathematical bridge: the bucket method sorts points by digit
/// value, so bucket[b] = sum of points with digit (b+1) - sum with digit -(b+1).
/// Then sum_{b} (b+1)*bucket[b] = sum_{i} digit[i]*point[i] = column sum.
///
/// Proof sketch: For each point i with digit d_i at the column:
/// - If d_i > 0: it's added to bucket[d_i - 1], contributing d_i * point_i
/// - If d_i < 0: it's subtracted from bucket[-d_i - 1], contributing d_i * point_i
/// - If d_i == 0: no contribution (correct since 0 * point_i = identity)
///
/// TODO: Prove by induction on n; currently admitted.
pub proof fn axiom_bucket_weighted_sum_equals_column_sum(
    points_affine: Seq<(nat, nat)>,
    all_digits: Seq<Seq<i8>>,
    col: int,
    n: int,
    num_buckets: int,
)
    requires
        0 <= col,
        0 <= n <= points_affine.len(),
        n <= all_digits.len(),
        num_buckets > 0,
        forall|k: int| 0 <= k < n ==> col < (#[trigger] all_digits[k]).len(),
        forall|k: int|
            0 <= k < n ==> -(num_buckets as int) <= ((#[trigger] all_digits[k])[col] as int) <= (
            num_buckets as int),
    ensures
        ({
            let buckets = Seq::new(
                num_buckets as nat,
                |b: int| pippenger_bucket_contents(points_affine, all_digits, col, n, b),
            );
            pippenger_weighted_bucket_sum(buckets, num_buckets)
        }) == straus_column_sum(points_affine, all_digits, col, n),
{
    admit();
}

// =============================================================================
// Axiom: Intermediate-sum trick equals weighted bucket sum
// =============================================================================
/// The running-sum-of-intermediate-sums trick computes the weighted bucket sum.
///
/// The intermediate-sum trick processes buckets B-1, B-2, ..., 0:
///   intermediate_sum accumulates: bucket[B-1], then bucket[B-1]+bucket[B-2], etc.
///   running_sum accumulates intermediate sums, effectively computing
///   sum_{b=0}^{B-1} (b+1) * bucket[b].
///
/// TODO: Prove by induction on B; currently admitted.
pub proof fn axiom_running_sum_equals_weighted(buckets_affine: Seq<(nat, nat)>, B: int)
    requires
        B > 0,
        buckets_affine.len() == B,
    ensures
        pippenger_running_sum(buckets_affine, 0, B) == pippenger_weighted_bucket_sum(
            buckets_affine,
            B,
        ),
{
    admit();
}

} // verus!
