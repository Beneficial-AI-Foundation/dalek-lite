//! Lemmas for Straus (interleaved window) multiscalar multiplication.
//!
//! This module contains proofs connecting the Straus algorithm's column-wise Horner
//! evaluation to the `sum_of_scalar_muls` specification.
//!
//! ## Key lemmas:
//! - `lemma_select_is_signed_scalar_mul_projective`: LookupTable<ProjectiveNielsPoint> select correctness
//! - `lemma_naf_select_is_signed_scalar_mul_projective`: NafLookupTable5<ProjectiveNielsPoint> select+negate correctness
//! - `lemma_column_sum_step`: Unfolds `straus_column_sum(j, k+1)` one step
//! - `lemma_straus_ct_step` / `lemma_straus_vt_step`: Unfold opaque Horner specs
//! - `lemma_straus_ct_correct` / `lemma_straus_vt_correct`: Main correctness theorems
#![allow(non_snake_case)]

use crate::backend::serial::curve_models::ProjectiveNielsPoint;
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;

#[cfg(verus_keep_ghost)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
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

use vstd::prelude::*;

verus! {

// =============================================================================
// Select lemma for LookupTable<ProjectiveNielsPoint>
// =============================================================================
/// Lemma: The result of select(x) on a valid ProjectiveNiels lookup table
/// equals [x]*basepoint in affine coords (signed scalar multiplication).
///
/// This mirrors `lemma_select_is_signed_scalar_mul` (for AffineNielsPoint)
/// from mul_base_lemmas.rs, adapted for ProjectiveNielsPoint.
///
/// For a digit x in [-8, 8]:
/// - x > 0: `table[x-1]` decodes to `[x]*P`
/// - x == 0: identity decodes to `[0]*P = O`
/// - x < 0: `negate(table[-x-1])` decodes to `[-x]*P` negated = `[x]*P`
pub proof fn lemma_select_is_signed_scalar_mul_projective(
    table: [ProjectiveNielsPoint; 8],
    x: i8,
    result: ProjectiveNielsPoint,
    basepoint: (nat, nat),
)
    requires
        -8 <= x <= 8,
        // Table entries decode to multiples of basepoint
        forall|j: int|
            0 <= j < 8 ==> projective_niels_point_as_affine_edwards(#[trigger] table[j])
                == edwards_scalar_mul(basepoint, (j + 1) as nat),
        // select's postconditions:
        (x > 0 ==> result == table[(x - 1) as int]),
        (x == 0 ==> result == identity_projective_niels()),
        (x < 0 ==> result == negate_projective_niels(table[((-x) - 1) as int])),
    ensures
        projective_niels_point_as_affine_edwards(result) == edwards_scalar_mul_signed(
            basepoint,
            x as int,
        ),
{
    reveal(edwards_scalar_mul_signed);

    if x > 0 {
        let j = (x - 1) as int;
        assert(0 <= j < 8);
        assert(projective_niels_point_as_affine_edwards(table[j]) == edwards_scalar_mul(
            basepoint,
            (j + 1) as nat,
        ));
        assert((j + 1) as nat == x as nat);
    } else if x == 0 {
        lemma_identity_projective_niels_is_identity();
        reveal_with_fuel(edwards_scalar_mul, 1);
        assert(edwards_scalar_mul(basepoint, 0) == math_edwards_identity());
    } else {
        // x < 0: result == negate_projective_niels(table[((-x) - 1) as int])
        let j = ((-x) - 1) as int;
        assert(0 <= j < 8);
        assert(projective_niels_point_as_affine_edwards(table[j]) == edwards_scalar_mul(
            basepoint,
            (j + 1) as nat,
        ));
        assert((j + 1) as nat == (-x) as nat);

        lemma_negate_projective_niels_is_edwards_neg(table[j]);
        assert(projective_niels_point_as_affine_edwards(negate_projective_niels(table[j]))
            == edwards_neg(edwards_scalar_mul(basepoint, (-x) as nat)));
    }
}

// =============================================================================
// Select lemma for NafLookupTable5<ProjectiveNielsPoint>
// =============================================================================
/// Lemma: For NafLookupTable5, selecting/negating based on a NAF digit gives
/// the correct signed scalar multiple of the basepoint.
///
/// NAF digits can be:
/// - digit > 0 (odd, 1..15): select(digit) gives table[digit/2] = [digit]*P
/// - digit < 0 (odd, -15..-1): negate(select(-digit)) gives -[|-digit|]*P = [digit]*P
/// - digit == 0: no operation (identity contribution)
pub proof fn lemma_naf_select_is_signed_scalar_mul_projective(
    table: [ProjectiveNielsPoint; 8],
    digit: i8,
    result: ProjectiveNielsPoint,
    basepoint: (nat, nat),
    is_add: bool,  // true if digit > 0, false if digit < 0
)
    requires
        digit != 0,
        // NAF width-5 bounds: nonzero digits are odd and in (-16, 16)
        -16 < digit < 16,
        (digit as int) % 2 != 0,
        // Table validity: table[j] decodes to [(2j+1)]*P
        forall|j: int|
            0 <= j < 8 ==> projective_niels_point_as_affine_edwards(#[trigger] table[j])
                == edwards_scalar_mul(basepoint, (2 * j + 1) as nat),
        // For digit > 0: result = table[digit/2] (from select(digit as usize))
        is_add ==> digit > 0 && result == table[((digit as int) / 2) as int],
        // For digit < 0: result = negate(table[(-digit)/2]) (from select then negate)
        !is_add ==> digit < 0 && result == negate_projective_niels(
            table[(((-digit) as int) / 2) as int],
        ),
    ensures
        projective_niels_point_as_affine_edwards(result) == edwards_scalar_mul_signed(
            basepoint,
            digit as int,
        ),
{
    reveal(edwards_scalar_mul_signed);

    if is_add {
        // digit > 0, odd: result = table[digit/2]
        let j = ((digit as int) / 2) as int;
        assert(0 <= j < 8);
        // table[j] = [(2j+1)]*P and 2j+1 = digit (since digit is odd)
        assert(projective_niels_point_as_affine_edwards(table[j]) == edwards_scalar_mul(
            basepoint,
            (2 * j + 1) as nat,
        ));
        assert((2 * j + 1) as nat == digit as nat);
    } else {
        // digit < 0, odd: result = negate(table[(-digit)/2])
        let abs_digit = (-digit) as int;
        let j = (abs_digit / 2) as int;
        assert(0 <= j < 8);
        assert(projective_niels_point_as_affine_edwards(table[j]) == edwards_scalar_mul(
            basepoint,
            (2 * j + 1) as nat,
        ));
        assert((2 * j + 1) as nat == abs_digit as nat);

        lemma_negate_projective_niels_is_edwards_neg(table[j]);
        assert(projective_niels_point_as_affine_edwards(negate_projective_niels(table[j]))
            == edwards_neg(edwards_scalar_mul(basepoint, abs_digit as nat)));
    }
}

// =============================================================================
// Column sum step lemma
// =============================================================================
/// Unfolds `straus_column_sum(points, digits, j, k+1)` by one step.
pub proof fn lemma_column_sum_step(
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
    j: int,
    k: int,
)
    requires
        k >= 0,
        k < points_affine.len(),
        k < digits.len(),
        0 <= j,
        j < digits[k].len(),
    ensures
        straus_column_sum(points_affine, digits, j, k + 1) == {
            let prev = straus_column_sum(points_affine, digits, j, k);
            let term = edwards_scalar_mul_signed(points_affine[k], digits[k][j] as int);
            edwards_add(prev.0, prev.1, term.0, term.1)
        },
{
    // Direct from definition (k+1 > 0 so we enter the else branch)
}

// =============================================================================
// Straus CT step lemma (unfold opaque spec)
// =============================================================================
/// Unfolds `straus_ct_partial(points, digits, j)` by one step when `j < 64`.
pub proof fn lemma_straus_ct_step(points_affine: Seq<(nat, nat)>, digits: Seq<Seq<i8>>, j: int)
    requires
        0 <= j < 64,
    ensures
        straus_ct_partial(points_affine, digits, j) == {
            let prev = straus_ct_partial(points_affine, digits, j + 1);
            let scaled = edwards_scalar_mul(prev, 16);
            let col = straus_column_sum(points_affine, digits, j, points_affine.len() as int);
            edwards_add(scaled.0, scaled.1, col.0, col.1)
        },
{
    reveal(straus_ct_partial);
}

/// Base case: `straus_ct_partial(points, digits, 64) == identity`.
pub proof fn lemma_straus_ct_base(points_affine: Seq<(nat, nat)>, digits: Seq<Seq<i8>>)
    ensures
        straus_ct_partial(points_affine, digits, 64) == math_edwards_identity(),
{
    reveal(straus_ct_partial);
}

// =============================================================================
// Straus VT step lemma (unfold opaque spec)
// =============================================================================
/// Unfolds `straus_vt_partial(points, nafs, i)` by one step when `i < 256`.
pub proof fn lemma_straus_vt_step(points_affine: Seq<(nat, nat)>, nafs: Seq<Seq<i8>>, i: int)
    requires
        0 <= i < 256,
    ensures
        straus_vt_partial(points_affine, nafs, i) == {
            let prev = straus_vt_partial(points_affine, nafs, i + 1);
            let doubled = edwards_double(prev.0, prev.1);
            let col = straus_column_sum(points_affine, nafs, i, points_affine.len() as int);
            edwards_add(doubled.0, doubled.1, col.0, col.1)
        },
{
    reveal(straus_vt_partial);
}

/// Base case: `straus_vt_partial(points, nafs, 256) == identity`.
pub proof fn lemma_straus_vt_base(points_affine: Seq<(nat, nat)>, nafs: Seq<Seq<i8>>)
    ensures
        straus_vt_partial(points_affine, nafs, 256) == math_edwards_identity(),
{
    reveal(straus_vt_partial);
}

// =============================================================================
// Straus CT correctness theorem
// =============================================================================
// axiom_straus_ct_correct removed — replaced by lemma_straus_ct_correct (fully proved)
// =============================================================================
// Straus VT correctness theorem
// =============================================================================
// axiom_straus_vt_correct removed — replaced by lemma_straus_vt_correct (fully proved)
// =============================================================================
// Helper: radix_16_all_bounded for Seq<i8>
// =============================================================================
/// Spec predicate: all digits in a Seq<i8> are in [-8, 8].
/// This is the Seq analog of `radix_16_all_bounded` which works on arrays.
pub open spec fn radix_16_all_bounded_seq(digits: Seq<i8>) -> bool {
    forall|k: int| 0 <= k < digits.len() ==> -8 <= #[trigger] digits[k] <= 8
}

// =============================================================================
// Column sum with zero digits is identity
// =============================================================================
/// When n <= 0, the column sum is the identity.
pub proof fn lemma_column_sum_zero(points_affine: Seq<(nat, nat)>, digits: Seq<Seq<i8>>, j: int)
    ensures
        straus_column_sum(points_affine, digits, j, 0) == math_edwards_identity(),
{
    // Direct from definition (n <= 0 case)
}

// =============================================================================
// Column sum add-one-term lemma (for inner loop invariant)
// =============================================================================
/// Adding one term to the column sum: connects the inner loop body to the spec.
///
/// If `prev == straus_column_sum(pts, digits, j, k)` and we add
/// `[digits[k][j]] * pts[k]`, the result equals `straus_column_sum(pts, digits, j, k+1)`.
pub proof fn lemma_column_sum_add_term(
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
    j: int,
    k: int,
    prev_affine: (nat, nat),
    term_affine: (nat, nat),
)
    requires
        0 <= k < points_affine.len(),
        0 <= k < digits.len(),
        0 <= j,
        j < digits[k].len(),
        prev_affine == straus_column_sum(points_affine, digits, j, k),
        term_affine == edwards_scalar_mul_signed(points_affine[k], digits[k][j] as int),
    ensures
        edwards_add(prev_affine.0, prev_affine.1, term_affine.0, term_affine.1)
            == straus_column_sum(points_affine, digits, j, k + 1),
{
    // Direct from straus_column_sum definition unfolding
}

// =============================================================================
// NAF digit select preconditions
// =============================================================================
/// For a NAF digit d > 0 from a valid NAF(5), d is odd and d < 16.
/// This establishes the select preconditions: (d as usize) & 1 == 1 and (d as usize) < 16.
pub proof fn lemma_naf_digit_positive_select_preconditions(digit: i8)
    requires
        digit > 0,
        (digit as int) % 2 != 0,
        digit < 16,
    ensures
        (digit as usize) & 1usize == 1usize,
        (digit as usize) < 16,
{
    assert((digit as usize) < 16);
    assert((digit as usize) & 1usize == 1usize) by (bit_vector)
        requires
            digit > 0i8,
            digit < 16i8,
            (digit as int) % 2 != 0,
    ;
}

/// For a NAF digit d < 0 from a valid NAF(5), -d is odd and -d < 16.
/// This establishes the select preconditions for the negated digit.
pub proof fn lemma_naf_digit_negative_select_preconditions(digit: i8)
    requires
        digit < 0,
        (digit as int) % 2 != 0,
        digit > -16,
    ensures
        ((-digit) as usize) & 1usize == 1usize,
        ((-digit) as usize) < 16,
{
    assert(((-digit) as usize) < 16);
    assert(((-digit) as usize) & 1usize == 1usize) by (bit_vector)
        requires
            digit < 0i8,
            digit > -16i8,
            (digit as int) % 2 != 0,
    ;
}

// =============================================================================
// Affine coordinates are always canonical (< p())
// =============================================================================
/// edwards_point_as_affine always returns coordinates < p() because field_mul
/// returns (a * b) % p() which is always < p().
pub proof fn lemma_edwards_point_as_affine_canonical(point: EdwardsPoint)
    ensures
        edwards_point_as_affine(point).0 < p(),
        edwards_point_as_affine(point).1 < p(),
{
    p_gt_2();
    // edwards_point_as_affine = (field_mul(X, inv(Z)), field_mul(Y, inv(Z)))
    // field_mul(a, b) = field_canonical(a * b) = (a * b) % p()
    // and x % p() < p() for p() > 0
}

// =============================================================================
// Column sum produces canonical coordinates
// =============================================================================
/// The column sum always returns coordinates < p(), given canonical input points.
pub proof fn lemma_column_sum_canonical(
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
    j: int,
    n: int,
)
    requires
        n >= 0,
        n <= points_affine.len(),
        n <= digits.len(),
        0 <= j,
        forall|k: int| 0 <= k < n ==> j < (#[trigger] digits[k]).len(),
        forall|k: int|
            0 <= k < n ==> (#[trigger] points_affine[k]).0 < p() && points_affine[k].1 < p(),
    ensures
        straus_column_sum(points_affine, digits, j, n).0 < p(),
        straus_column_sum(points_affine, digits, j, n).1 < p(),
    decreases n,
{
    if n <= 0 {
        // identity = (0, 1), both < p()
        p_gt_2();
    } else {
        lemma_column_sum_canonical(points_affine, digits, j, n - 1);
        let prev = straus_column_sum(points_affine, digits, j, n - 1);
        // term is canonical because edwards_scalar_mul_signed returns canonical coords
        lemma_edwards_scalar_mul_signed_canonical(points_affine[n - 1], digits[n - 1][j] as int);
        // edwards_add of canonical inputs produces canonical output
        let term = edwards_scalar_mul_signed(points_affine[n - 1], digits[n - 1][j] as int);
        lemma_edwards_add_canonical(prev.0, prev.1, term.0, term.1);
    }
}

// =============================================================================
// Column sum step for zero digit (Equal case in VT inner loop)
// =============================================================================
/// When the digit is 0, the column sum doesn't change.
/// This handles the Equal case in the variable-time inner loop.
pub proof fn lemma_column_sum_step_zero_digit(
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
    j: int,
    k: int,
)
    requires
        0 <= k < points_affine.len(),
        0 <= k < digits.len(),
        0 <= j,
        j < digits[k].len(),
        digits[k][j] == 0,
        // column sum up to k is canonical
        straus_column_sum(points_affine, digits, j, k).0 < p(),
        straus_column_sum(points_affine, digits, j, k).1 < p(),
    ensures
        straus_column_sum(points_affine, digits, j, k + 1) == straus_column_sum(
            points_affine,
            digits,
            j,
            k,
        ),
{
    let col_k = straus_column_sum(points_affine, digits, j, k);
    let term = edwards_scalar_mul_signed(points_affine[k], 0int);
    // edwards_scalar_mul_signed(_, 0) == edwards_scalar_mul(_, 0) == identity
    reveal_with_fuel(edwards_scalar_mul, 1);
    assert(term == math_edwards_identity());
    assert(term == (0nat, 1nat));
    // edwards_add(col_k, identity) == col_k (when col_k is canonical)
    lemma_edwards_add_identity_right_canonical(col_k);
}

// =============================================================================
// Column sum prefix independence
// =============================================================================
/// column_sum only accesses pts[k] and digs[k] for k < n, so
/// column_sum(pts1, digs1, j, n) == column_sum(pts2, digs2, j, n)
/// when pts1 and pts2 agree on [0..n) and digs1 and digs2 agree on [0..n).
pub proof fn lemma_column_sum_prefix_eq(
    pts1: Seq<(nat, nat)>,
    digs1: Seq<Seq<i8>>,
    pts2: Seq<(nat, nat)>,
    digs2: Seq<Seq<i8>>,
    j: int,
    n: int,
)
    requires
        n >= 0,
        n <= pts1.len(),
        n <= pts2.len(),
        n <= digs1.len(),
        n <= digs2.len(),
        forall|k: int| 0 <= k < n ==> #[trigger] pts1[k] == pts2[k],
        forall|k: int| 0 <= k < n ==> #[trigger] digs1[k] == digs2[k],
    ensures
        straus_column_sum(pts1, digs1, j, n) == straus_column_sum(pts2, digs2, j, n),
    decreases n,
{
    if n > 0 {
        lemma_column_sum_prefix_eq(pts1, digs1, pts2, digs2, j, n - 1);
        // At k = n-1: pts1[n-1] == pts2[n-1] and digs1[n-1] == digs2[n-1]
        // So the recursive step produces the same result
    }
}

// =============================================================================
// Column sum for single point equals signed scalar mul (when canonical)
// =============================================================================
/// For a single point with canonical coordinates, column_sum equals
/// the signed scalar multiplication of the digit with the point.
pub proof fn lemma_column_sum_single(P: (nat, nat), d: Seq<i8>, j: int)
    requires
        0 <= j < d.len(),
        P.0 < p(),
        P.1 < p(),
    ensures
        straus_column_sum(seq![(P)], seq![(d)], j, 1) == edwards_scalar_mul_signed(P, d[j] as int),
{
    let pts = seq![(P)];
    let digs = seq![(d)];
    // Verify indexing
    assert(pts[0] == P);
    assert(digs[0] == d);
    assert(digs[0][j] == d[j]);

    // column_sum(pts, digs, j, 1) by definition:
    //   prev = column_sum(pts, digs, j, 0) = identity
    //   term = edwards_scalar_mul_signed(pts[0], digs[0][j])
    //   result = edwards_add(prev, term) = edwards_add(identity, term)
    let prev = straus_column_sum(pts, digs, j, 0);
    assert(prev == math_edwards_identity());

    let term = edwards_scalar_mul_signed(P, d[j] as int);
    lemma_edwards_scalar_mul_signed_canonical(P, d[j] as int);

    // edwards_add(identity, term) = edwards_add(term, identity) = term
    let id = math_edwards_identity();
    lemma_edwards_add_commutative(id.0, id.1, term.0, term.1);
    lemma_edwards_add_identity_right_canonical(term);
}

// =============================================================================
// Single-point Horner CT: straus_ct_partial(seq![P], seq![d], j) == [reconstruct_from(d,j)]*P
// =============================================================================
/// For a single canonical point P and radix-16 digits d (len 64),
/// the single-point Horner evaluation equals [reconstruct_radix_16_from(d, j)] * P.
pub proof fn lemma_straus_ct_single(P: (nat, nat), d: Seq<i8>, j: int)
    requires
        d.len() == 64,
        P.0 < p(),
        P.1 < p(),
        0 <= j <= 64,
    ensures
        straus_ct_partial(seq![(P)], seq![(d)], j) == edwards_scalar_mul_signed(
            P,
            reconstruct_radix_16_from(d, j),
        ),
    decreases 64 - j,
{
    if j >= 64 {
        // Base: straus_ct_partial(..., 64) == identity
        lemma_straus_ct_base(seq![(P)], seq![(d)]);
        // reconstruct_radix_16_from(d, 64) == 0
        // edwards_scalar_mul_signed(P, 0) == identity
        reveal(edwards_scalar_mul_signed);
        reveal_with_fuel(edwards_scalar_mul, 1);
    } else {
        // Unfold straus_ct_partial one step
        lemma_straus_ct_step(seq![(P)], seq![(d)], j);
        // straus_ct_partial(seq![P], seq![d], j)
        //   == edwards_add([16]*straus_ct_partial(seq![P], seq![d], j+1), column_sum(seq![P], seq![d], j, 1))

        // IH: straus_ct_partial(seq![P], seq![d], j+1) == [reconstruct_from(d, j+1)]*P
        lemma_straus_ct_single(P, d, j + 1);
        let r_next = reconstruct_radix_16_from(d, j + 1);

        // [16] * [r_next]*P == [16 * r_next]*P
        lemma_edwards_scalar_mul_signed_composition(P, r_next, 16);

        // column_sum(seq![P], seq![d], j, 1) == [d[j]]*P
        lemma_column_sum_single(P, d, j);

        // [16*r_next]*P + [d[j]]*P == [16*r_next + d[j]]*P
        axiom_edwards_scalar_mul_signed_additive(P, 16 * r_next, d[j] as int);

        // 16*r_next + d[j] == reconstruct_radix_16_from(d, j)
        // (from definition: reconstruct_from(d, j) = d[j] + 16 * reconstruct_from(d, j+1))
        assert(d[j] as int + 16 * r_next == reconstruct_radix_16_from(d, j));
    }
}

// =============================================================================
// Straus CT partial peel-last: splitting off the last point
// =============================================================================
/// The Horner evaluation over n points equals the sum of:
/// - the Horner evaluation over the first (n-1) points, plus
/// - the Horner evaluation for the last point alone.
///
/// Proof by induction on (64 - j), using:
/// - scalar_mul distributivity: [16]*(A+B) = [16]*A + [16]*B
/// - group associativity
/// - column_sum prefix independence
pub proof fn lemma_straus_ct_partial_peel_last(pts: Seq<(nat, nat)>, digs: Seq<Seq<i8>>, j: int)
    requires
        pts.len() >= 1,
        digs.len() == pts.len(),
        0 <= j <= 64,
        // All digits have length 64
        forall|k: int| 0 <= k < digs.len() ==> (#[trigger] digs[k]).len() == 64,
        // All points are canonical
        forall|k: int| 0 <= k < pts.len() ==> (#[trigger] pts[k]).0 < p() && pts[k].1 < p(),
    ensures
        straus_ct_partial(pts, digs, j) == ({
            let prefix_result = straus_ct_partial(pts.drop_last(), digs.drop_last(), j);
            let single_result = straus_ct_partial(seq![(pts.last())], seq![(digs.last())], j);
            edwards_add(prefix_result.0, prefix_result.1, single_result.0, single_result.1)
        }),
    decreases 64 - j,
{
    let n = pts.len() as int;
    let pts_prefix = pts.drop_last();
    let digs_prefix = digs.drop_last();
    let pts_single = seq![(pts.last())];
    let digs_single = seq![(digs.last())];

    if j >= 64 {
        // Base case: all three terms are identity
        lemma_straus_ct_base(pts, digs);
        lemma_straus_ct_base(pts_prefix, digs_prefix);
        lemma_straus_ct_base(pts_single, digs_single);
        // edwards_add(identity, identity) == identity
        p_gt_2();
        lemma_edwards_add_identity_right_canonical(math_edwards_identity());
    } else {
        // Unfold straus_ct_partial for all three
        lemma_straus_ct_step(pts, digs, j);
        lemma_straus_ct_step(pts_prefix, digs_prefix, j);
        lemma_straus_ct_step(pts_single, digs_single, j);

        // IH at j+1
        lemma_straus_ct_partial_peel_last(pts, digs, j + 1);

        let prev_full = straus_ct_partial(pts, digs, j + 1);
        let prev_prefix = straus_ct_partial(pts_prefix, digs_prefix, j + 1);
        let prev_single = straus_ct_partial(pts_single, digs_single, j + 1);

        // By IH: prev_full == edwards_add(prev_prefix, prev_single)
        // [16]*prev_full == [16]*edwards_add(prev_prefix, prev_single)
        //               == edwards_add([16]*prev_prefix, [16]*prev_single)  (distributivity)
        axiom_edwards_scalar_mul_distributive(prev_prefix, prev_single, 16);

        let scaled_prefix = edwards_scalar_mul(prev_prefix, 16);
        let scaled_single = edwards_scalar_mul(prev_single, 16);

        // column_sum(pts, digs, j, n) == edwards_add(column_sum(pts, digs, j, n-1), term)
        // And column_sum(pts, digs, j, n-1) == column_sum(pts_prefix, digs_prefix, j, n-1)
        let col_full = straus_column_sum(pts, digs, j, n);
        let col_prefix = straus_column_sum(pts_prefix, digs_prefix, j, (n - 1));
        let col_single = straus_column_sum(pts_single, digs_single, j, 1);

        // Prove column_sum prefix independence
        lemma_column_sum_prefix_eq(pts, digs, pts_prefix, digs_prefix, j, n - 1);
        // So: straus_column_sum(pts, digs, j, n-1) == col_prefix

        // column_sum for the single point
        lemma_column_sum_single(pts.last(), digs.last(), j);
        // col_single == [digs.last()[j]] * pts.last()

        // Now we need: col_full == edwards_add(col_prefix, col_single)
        // From definition: col_full = edwards_add(column_sum(pts, digs, j, n-1), term)
        // where term = edwards_scalar_mul_signed(pts[n-1], digs[n-1][j])
        // And column_sum(pts, digs, j, n-1) == col_prefix (proved above)
        // And term == col_single (since both equal [digs.last()[j]] * pts.last())

        // We need to show: straus_ct_partial(pts, digs, j) combines correctly.
        // straus_ct_partial(pts, digs, j) = edwards_add(scaled_full, col_full)
        // where scaled_full = edwards_scalar_mul(prev_full, 16)
        //                   = edwards_add(scaled_prefix, scaled_single)

        // Want: edwards_add(edwards_add(A,B), edwards_add(C,D))
        //     = edwards_add(edwards_add(A,C), edwards_add(B,D))
        // where A = scaled_prefix, B = scaled_single, C = col_prefix, D = col_single

        // This follows from associativity and commutativity:
        // (A+B) + (C+D) = A + (B + (C + D))           [assoc]
        //               = A + ((B + C) + D)             [assoc on inner]
        //               = A + ((C + B) + D)             [comm on B,C]
        //               = A + (C + (B + D))             [assoc on inner]
        //               = (A + C) + (B + D)             [assoc]

        let a = scaled_prefix;
        let b = scaled_single;
        let c = col_prefix;
        let d_val = col_single;

        // (A+B) + (C+D)
        let ab = edwards_add(a.0, a.1, b.0, b.1);
        let cd = edwards_add(c.0, c.1, d_val.0, d_val.1);
        let bc = edwards_add(b.0, b.1, c.0, c.1);
        let cb = edwards_add(c.0, c.1, b.0, b.1);
        let bd = edwards_add(b.0, b.1, d_val.0, d_val.1);
        let ac = edwards_add(a.0, a.1, c.0, c.1);

        // Step 1: (A+B) + (C+D) = A + (B + (C+D))
        axiom_edwards_add_associative(a.0, a.1, b.0, b.1, cd.0, cd.1);
        let b_cd = edwards_add(b.0, b.1, cd.0, cd.1);

        // Step 2: B + (C+D) = (B+C) + D
        axiom_edwards_add_associative(b.0, b.1, c.0, c.1, d_val.0, d_val.1);

        // Step 3: B+C = C+B
        lemma_edwards_add_commutative(b.0, b.1, c.0, c.1);

        // Step 4: (C+B) + D = C + (B+D)
        axiom_edwards_add_associative(c.0, c.1, b.0, b.1, d_val.0, d_val.1);

        // Step 5: A + (C + (B+D)) = (A+C) + (B+D)
        axiom_edwards_add_associative(a.0, a.1, c.0, c.1, bd.0, bd.1);

        // Chain: (A+B)+(C+D) = A+(B+(C+D)) = A+((B+C)+D) = A+((C+B)+D) = A+(C+(B+D)) = (A+C)+(B+D)
        assert(edwards_add(ab.0, ab.1, cd.0, cd.1) == edwards_add(ac.0, ac.1, bd.0, bd.1));
    }
}

// =============================================================================
// Main CT correctness theorem
// =============================================================================
/// Proves: straus_ct_partial(points_affine, digits, 0) == sum_of_scalar_muls(scalars, points_ep)
///
/// Proof by induction on n (number of points):
/// - n=0: both sides are identity
/// - n→n+1: peel off last point using lemma_straus_ct_partial_peel_last,
///   apply IH for prefix, use lemma_straus_ct_single for the last point
pub proof fn lemma_straus_ct_correct(
    scalars: Seq<Scalar>,
    points_ep: Seq<EdwardsPoint>,
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
)
    requires
        scalars.len() == points_ep.len(),
        points_affine.len() == scalars.len(),
        digits.len() == scalars.len(),
        forall|k: int|
            0 <= k < points_affine.len() ==> #[trigger] points_affine[k] == edwards_point_as_affine(
                points_ep[k],
            ),
        forall|k: int|
            0 <= k < digits.len() ==> {
                &&& (#[trigger] digits[k]).len() == 64
                &&& radix_16_all_bounded_seq(digits[k])
                &&& reconstruct_radix_16(digits[k]) == scalar_as_nat(&scalars[k]) as int
            },
    ensures
        straus_ct_partial(points_affine, digits, 0) == sum_of_scalar_muls(scalars, points_ep),
    decreases scalars.len(),
{
    let n = scalars.len();

    if n == 0 {
        // Both sides are identity
        lemma_straus_ct_base(points_affine, digits);
        // straus_ct_partial(..., 0) with 0 points: all column_sums are identity,
        // so Horner evaluation is identity
        // Actually, straus_ct_partial starts at j=0, and at each step
        // column_sum(..., j, 0) = identity, and [16]*identity + identity = identity.
        // Let's just unfold the base case directly.
        // For n=0 points, straus_ct_partial degenerates to identity at every j.
        lemma_straus_ct_zero_points(points_affine, digits);
    } else {
        // Inductive case: peel off last point
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
            &&& (#[trigger] digs_prefix[k]).len() == 64
            &&& radix_16_all_bounded_seq(digs_prefix[k])
            &&& reconstruct_radix_16(digs_prefix[k]) == scalar_as_nat(&scalars_prefix[k]) as int
        } by {
            assert(digs_prefix[k] == digits[k]);
            assert(scalars_prefix[k] == scalars[k]);
        }

        // IH: prefix is correct
        lemma_straus_ct_correct(scalars_prefix, points_prefix, pts_prefix, digs_prefix);

        // Points are canonical (from edwards_point_as_affine)
        assert forall|k: int| 0 <= k < points_affine.len() implies (#[trigger] points_affine[k]).0
            < p() && points_affine[k].1 < p() by {
            lemma_edwards_point_as_affine_canonical(points_ep[k]);
        }

        // Split: straus_ct_partial(pts, digs, 0) = prefix_result + single_result
        lemma_straus_ct_partial_peel_last(points_affine, digits, 0);

        // Single point Horner = [scalar_last] * P_last
        let P_last = points_affine.last();
        let d_last = digits.last();
        lemma_straus_ct_single(P_last, d_last, 0);
        // straus_ct_partial(seq![P_last], seq![d_last], 0) == [reconstruct_radix_16_from(d_last, 0)] * P_last

        // Connect reconstruct_radix_16_from(d, 0) to reconstruct_radix_16(d)
        lemma_reconstruct_radix_16_from_equals_reconstruct(d_last);
        // So: [reconstruct_radix_16(d_last)] * P_last == [scalar_as_nat(scalars[last])] * P_last

        // Connect signed to unsigned scalar_mul
        let scalar_nat = scalar_as_nat(&scalars[last]);
        assert(reconstruct_radix_16(d_last) == scalar_nat as int);
        reveal(edwards_scalar_mul_signed);

        // Now combine: sum_of_scalar_muls(scalars, points_ep) decomposes as
        // edwards_add(sum_of_scalar_muls(prefix), [scalar_last]*P_last)
        // which matches our splitting.
    }
}

// =============================================================================
// Helper: straus_ct_partial with 0 points is always identity
// =============================================================================
pub proof fn lemma_straus_ct_zero_points(pts: Seq<(nat, nat)>, digs: Seq<Seq<i8>>)
    requires
        pts.len() == 0,
        digs.len() == 0,
    ensures
        straus_ct_partial(pts, digs, 0) == math_edwards_identity(),
    decreases 64int,
{
    // When there are 0 points, every column_sum is identity, and the Horner evaluation
    // produces identity. Prove by induction on 64-j.
    lemma_straus_ct_zero_points_from(pts, digs, 0);
}

pub proof fn lemma_straus_ct_zero_points_from(pts: Seq<(nat, nat)>, digs: Seq<Seq<i8>>, j: int)
    requires
        pts.len() == 0,
        digs.len() == 0,
        0 <= j <= 64,
    ensures
        straus_ct_partial(pts, digs, j) == math_edwards_identity(),
    decreases 64 - j,
{
    if j >= 64 {
        lemma_straus_ct_base(pts, digs);
    } else {
        lemma_straus_ct_step(pts, digs, j);
        lemma_straus_ct_zero_points_from(pts, digs, j + 1);
        // straus_ct_partial(pts, digs, j) = [16]*identity + column_sum(pts, digs, j, 0)
        // column_sum(..., 0) = identity
        // [16]*identity = identity (scalar mul of identity)
        lemma_edwards_scalar_mul_identity(16);
        let id = math_edwards_identity();
        p_gt_2();
        lemma_edwards_add_identity_right_canonical(id);
    }
}

// =============================================================================
// Helper: reconstruct_radix_16_from(d, 0) == reconstruct_radix_16(d) for len-64
// =============================================================================
pub proof fn lemma_reconstruct_radix_16_from_equals_reconstruct(d: Seq<i8>)
    requires
        d.len() == 64,
    ensures
        reconstruct_radix_16_from(d, 0) == reconstruct_radix_16(d),
{
    lemma_reconstruct_radix_16_from_eq_helper(d, 0);
    // Helper gives: reconstruct_radix_16_from(d, 0) == reconstruct_radix_2w(d.subrange(0, 64), 4)
    // Need: d.subrange(0, 64) == d
    assert(d.subrange(0, 64int) =~= d);
    // reconstruct_radix_16(d) == reconstruct_radix_2w(d, 4) by definition
}

proof fn lemma_reconstruct_radix_16_from_eq_helper(d: Seq<i8>, k: int)
    requires
        d.len() == 64,
        0 <= k <= 64,
    ensures
        reconstruct_radix_16_from(d, k) == reconstruct_radix_2w(d.subrange(k, 64int), 4),
    decreases 64 - k,
{
    let sub = d.subrange(k, 64int);
    if k >= 64 {
        assert(sub.len() == 0);
    } else {
        lemma_reconstruct_radix_16_from_eq_helper(d, k + 1);
        let sub_next = d.subrange(k + 1, 64int);
        assert(sub[0] == d[k]);
        assert(sub.len() == (64 - k));
        // Key: sub.skip(1) extensionally equals d.subrange(k+1, 64)
        assert forall|i: int| 0 <= i < sub.skip(1).len() implies sub.skip(1)[i] == sub_next[i] by {
            assert(sub.skip(1)[i] == sub[i + 1]);
            assert(sub[i + 1] == d[k + 1 + i]);
            assert(sub_next[i] == d[k + 1 + i]);
        }
        assert(sub.skip(1) =~= sub_next);
        assert(pow2(4) == 16) by {
            vstd::arithmetic::power2::lemma2_to64();
        }
    }
}

// =============================================================================
// Helper: edwards_scalar_mul of identity is identity
// =============================================================================
pub proof fn lemma_edwards_scalar_mul_identity(n: nat)
    ensures
        edwards_scalar_mul(math_edwards_identity(), n) == math_edwards_identity(),
    decreases n,
{
    let id = math_edwards_identity();
    if n == 0 {
        reveal_with_fuel(edwards_scalar_mul, 1);
    } else if n == 1 {
        // [1]*id = edwards_add(id, [0]*id) = edwards_add(id, id) -- wait, no.
        // edwards_scalar_mul(P, 1) by definition:
        //   n != 0: edwards_add(P.0, P.1, edwards_scalar_mul(P, 0).0, edwards_scalar_mul(P, 0).1)
        //         = edwards_add(id.0, id.1, id.0, id.1)  [since scalar_mul(id, 0) = id]
        reveal_with_fuel(edwards_scalar_mul, 2);
        p_gt_2();
        lemma_edwards_add_identity_right_canonical(id);
    } else {
        // n >= 2
        lemma_edwards_scalar_mul_identity((n - 1) as nat);
        lemma_edwards_scalar_mul_succ(id, (n - 1) as nat);
        p_gt_2();
        lemma_edwards_add_identity_right_canonical(id);
    }
}

// =============================================================================
// VT proof helpers
// =============================================================================
/// edwards_double(P) == edwards_scalar_mul(P, 2) for any P.
pub proof fn lemma_double_is_scalar_mul_2(P: (nat, nat))
    ensures
        edwards_double(P.0, P.1) == edwards_scalar_mul(P, 2),
{
    // edwards_double(P) = edwards_add(P, P)
    // edwards_scalar_mul(P, 2) = edwards_add(P, edwards_scalar_mul(P, 1))
    //                          = edwards_add(P, edwards_add(P, edwards_scalar_mul(P, 0)))
    //                          = edwards_add(P, edwards_add(P, identity))
    // Need: edwards_add(P, identity) = P (when canonical), but P might not be canonical.
    // Instead, use reveal_with_fuel to unfold the definition.
    reveal_with_fuel(edwards_scalar_mul, 3);
}

/// Doubling distributes over addition (from scalar_mul distributivity):
/// edwards_double(A+B) = edwards_add(edwards_double(A), edwards_double(B))
pub proof fn lemma_double_distributes(a: (nat, nat), b: (nat, nat))
    ensures
        ({
            let ab = edwards_add(a.0, a.1, b.0, b.1);
            edwards_double(ab.0, ab.1)
        }) == ({
            let da = edwards_double(a.0, a.1);
            let db = edwards_double(b.0, b.1);
            edwards_add(da.0, da.1, db.0, db.1)
        }),
{
    let ab = edwards_add(a.0, a.1, b.0, b.1);
    lemma_double_is_scalar_mul_2(ab);
    lemma_double_is_scalar_mul_2(a);
    lemma_double_is_scalar_mul_2(b);
    axiom_edwards_scalar_mul_distributive(a, b, 2);
}

/// Doubling the identity is identity.
pub proof fn lemma_double_identity()
    ensures
        edwards_double(0nat, 1nat) == math_edwards_identity(),
{
    lemma_double_is_scalar_mul_2(math_edwards_identity());
    lemma_edwards_scalar_mul_identity(2);
}

/// Single-point VT Horner: straus_vt_partial(seq![P], seq![naf], i) == [reconstruct_naf_from(naf, i)]*P
pub proof fn lemma_straus_vt_single(P: (nat, nat), naf: Seq<i8>, i: int)
    requires
        naf.len() == 256,
        P.0 < p(),
        P.1 < p(),
        0 <= i <= 256,
    ensures
        straus_vt_partial(seq![(P)], seq![(naf)], i) == edwards_scalar_mul_signed(
            P,
            reconstruct_naf_from(naf, i),
        ),
    decreases 256 - i,
{
    if i >= 256 {
        lemma_straus_vt_base(seq![(P)], seq![(naf)]);
        reveal(edwards_scalar_mul_signed);
        reveal_with_fuel(edwards_scalar_mul, 1);
    } else {
        lemma_straus_vt_step(seq![(P)], seq![(naf)], i);

        // IH at i+1
        lemma_straus_vt_single(P, naf, i + 1);
        let r_next = reconstruct_naf_from(naf, i + 1);

        // double([r_next]*P) = [2]*([r_next]*P) = [2*r_next]*P
        let prev_result = edwards_scalar_mul_signed(P, r_next);
        lemma_double_is_scalar_mul_2(prev_result);
        lemma_edwards_scalar_mul_signed_composition(P, r_next, 2);

        // column_sum(seq![P], seq![naf], i, 1) = [naf[i]]*P
        lemma_column_sum_single(P, naf, i);

        // [2*r_next]*P + [naf[i]]*P = [2*r_next + naf[i]]*P
        axiom_edwards_scalar_mul_signed_additive(P, 2 * r_next, naf[i] as int);

        // 2*r_next + naf[i] == reconstruct_naf_from(naf, i) by definition
        assert(naf[i] as int + 2 * r_next == reconstruct_naf_from(naf, i));
    }
}

/// VT partial peel-last: splitting off the last point
pub proof fn lemma_straus_vt_partial_peel_last(pts: Seq<(nat, nat)>, nafs: Seq<Seq<i8>>, i: int)
    requires
        pts.len() >= 1,
        nafs.len() == pts.len(),
        0 <= i <= 256,
        forall|k: int| 0 <= k < nafs.len() ==> (#[trigger] nafs[k]).len() == 256,
        forall|k: int| 0 <= k < pts.len() ==> (#[trigger] pts[k]).0 < p() && pts[k].1 < p(),
    ensures
        straus_vt_partial(pts, nafs, i) == ({
            let prefix_result = straus_vt_partial(pts.drop_last(), nafs.drop_last(), i);
            let single_result = straus_vt_partial(seq![(pts.last())], seq![(nafs.last())], i);
            edwards_add(prefix_result.0, prefix_result.1, single_result.0, single_result.1)
        }),
    decreases 256 - i,
{
    let n = pts.len() as int;
    let pts_prefix = pts.drop_last();
    let nafs_prefix = nafs.drop_last();
    let pts_single = seq![(pts.last())];
    let nafs_single = seq![(nafs.last())];

    if i >= 256 {
        lemma_straus_vt_base(pts, nafs);
        lemma_straus_vt_base(pts_prefix, nafs_prefix);
        lemma_straus_vt_base(pts_single, nafs_single);
        p_gt_2();
        lemma_edwards_add_identity_right_canonical(math_edwards_identity());
    } else {
        lemma_straus_vt_step(pts, nafs, i);
        lemma_straus_vt_step(pts_prefix, nafs_prefix, i);
        lemma_straus_vt_step(pts_single, nafs_single, i);

        // IH at i+1
        lemma_straus_vt_partial_peel_last(pts, nafs, i + 1);

        let prev_full = straus_vt_partial(pts, nafs, i + 1);
        let prev_prefix = straus_vt_partial(pts_prefix, nafs_prefix, i + 1);
        let prev_single = straus_vt_partial(pts_single, nafs_single, i + 1);

        // By IH: prev_full == edwards_add(prev_prefix, prev_single)
        // double(prev_full) == double(edwards_add(prev_prefix, prev_single))
        //                   == edwards_add(double(prev_prefix), double(prev_single))
        lemma_double_distributes(prev_prefix, prev_single);

        let doubled_prefix = edwards_double(prev_prefix.0, prev_prefix.1);
        let doubled_single = edwards_double(prev_single.0, prev_single.1);

        // Column sum splitting (same as CT)
        let col_prefix = straus_column_sum(pts_prefix, nafs_prefix, i, (n - 1));
        let col_single = straus_column_sum(pts_single, nafs_single, i, 1);

        lemma_column_sum_prefix_eq(pts, nafs, pts_prefix, nafs_prefix, i, n - 1);
        lemma_column_sum_single(pts.last(), nafs.last(), i);

        // Four-way reassociation: (A+B) + (C+D) = (A+C) + (B+D)
        let a = doubled_prefix;
        let b = doubled_single;
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

/// Helper: straus_vt_partial with 0 points is always identity
pub proof fn lemma_straus_vt_zero_points_from(pts: Seq<(nat, nat)>, nafs: Seq<Seq<i8>>, i: int)
    requires
        pts.len() == 0,
        nafs.len() == 0,
        0 <= i <= 256,
    ensures
        straus_vt_partial(pts, nafs, i) == math_edwards_identity(),
    decreases 256 - i,
{
    if i >= 256 {
        lemma_straus_vt_base(pts, nafs);
    } else {
        lemma_straus_vt_step(pts, nafs, i);
        lemma_straus_vt_zero_points_from(pts, nafs, i + 1);
        // double(identity) = identity
        lemma_double_identity();
        let id = math_edwards_identity();
        p_gt_2();
        lemma_edwards_add_identity_right_canonical(id);
    }
}

/// reconstruct_naf_from(naf, 0) == reconstruct(naf) for len-256
pub proof fn lemma_reconstruct_naf_from_equals_reconstruct(naf: Seq<i8>)
    requires
        naf.len() == 256,
    ensures
        reconstruct_naf_from(naf, 0) == reconstruct(naf),
{
    lemma_reconstruct_naf_from_eq_helper(naf, 0);
    assert(naf.subrange(0, 256int) =~= naf);
}

proof fn lemma_reconstruct_naf_from_eq_helper(naf: Seq<i8>, k: int)
    requires
        naf.len() == 256,
        0 <= k <= 256,
    ensures
        reconstruct_naf_from(naf, k) == reconstruct(naf.subrange(k, 256int)),
    decreases 256 - k,
{
    let sub = naf.subrange(k, 256int);
    if k >= 256 {
        assert(sub.len() == 0);
    } else {
        lemma_reconstruct_naf_from_eq_helper(naf, k + 1);
        let sub_next = naf.subrange(k + 1, 256int);
        assert(sub[0] == naf[k]);
        assert(sub.len() == (256 - k));
        assert forall|j: int| 0 <= j < sub.skip(1).len() implies sub.skip(1)[j] == sub_next[j] by {
            assert(sub.skip(1)[j] == sub[j + 1]);
            assert(sub[j + 1] == naf[k + 1 + j]);
            assert(sub_next[j] == naf[k + 1 + j]);
        }
        assert(sub.skip(1) =~= sub_next);
    }
}

/// Main VT correctness theorem
pub proof fn lemma_straus_vt_correct(
    scalars: Seq<Scalar>,
    points_ep: Seq<EdwardsPoint>,
    points_affine: Seq<(nat, nat)>,
    nafs: Seq<Seq<i8>>,
)
    requires
        scalars.len() == points_ep.len(),
        points_affine.len() == scalars.len(),
        nafs.len() == scalars.len(),
        forall|k: int|
            0 <= k < points_affine.len() ==> #[trigger] points_affine[k] == edwards_point_as_affine(
                points_ep[k],
            ),
        forall|k: int|
            0 <= k < nafs.len() ==> {
                &&& (#[trigger] nafs[k]).len() == 256
                &&& is_valid_naf(nafs[k], 5)
                &&& reconstruct(nafs[k]) == scalar_as_nat(&scalars[k]) as int
            },
    ensures
        straus_vt_partial(points_affine, nafs, 0) == sum_of_scalar_muls(scalars, points_ep),
    decreases scalars.len(),
{
    let n = scalars.len();

    if n == 0 {
        lemma_straus_vt_zero_points_from(points_affine, nafs, 0);
    } else {
        let last = (n - 1) as int;
        let pts_prefix = points_affine.drop_last();
        let nafs_prefix = nafs.drop_last();
        let scalars_prefix = scalars.subrange(0, last);
        let points_prefix = points_ep.subrange(0, last);

        // Preconditions for prefix
        assert forall|k: int| 0 <= k < pts_prefix.len() implies #[trigger] pts_prefix[k]
            == edwards_point_as_affine(points_prefix[k]) by {
            assert(pts_prefix[k] == points_affine[k]);
            assert(points_prefix[k] == points_ep[k]);
        }
        assert forall|k: int| 0 <= k < nafs_prefix.len() implies {
            &&& (#[trigger] nafs_prefix[k]).len() == 256
            &&& is_valid_naf(nafs_prefix[k], 5)
            &&& reconstruct(nafs_prefix[k]) == scalar_as_nat(&scalars_prefix[k]) as int
        } by {
            assert(nafs_prefix[k] == nafs[k]);
            assert(scalars_prefix[k] == scalars[k]);
        }

        // IH
        lemma_straus_vt_correct(scalars_prefix, points_prefix, pts_prefix, nafs_prefix);

        // Points are canonical
        assert forall|k: int| 0 <= k < points_affine.len() implies (#[trigger] points_affine[k]).0
            < p() && points_affine[k].1 < p() by {
            lemma_edwards_point_as_affine_canonical(points_ep[k]);
        }

        // Split
        lemma_straus_vt_partial_peel_last(points_affine, nafs, 0);

        // Single point Horner = scalar_mul
        let P_last = points_affine.last();
        let naf_last = nafs.last();
        lemma_straus_vt_single(P_last, naf_last, 0);
        lemma_reconstruct_naf_from_equals_reconstruct(naf_last);

        let scalar_nat = scalar_as_nat(&scalars[last]);
        assert(reconstruct(naf_last) == scalar_nat as int);
        reveal(edwards_scalar_mul_signed);
    }
}

} // verus!
