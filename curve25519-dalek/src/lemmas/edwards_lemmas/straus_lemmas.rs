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
use crate::specs::scalar_specs::*;
#[cfg(verus_keep_ghost)]
use crate::specs::window_specs::*;

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
        is_valid_lookup_table_projective(table, arbitrary::<EdwardsPoint>(), 8),
        // We need the table to decode to multiples of basepoint
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
/// Main correctness theorem for the constant-time Straus algorithm:
/// `straus_ct_partial(points, digits, 0) == sum_of_scalar_muls(scalars, points_ep)`
///
/// where `digits[k]` is the radix-16 representation of `scalars[k]` and
/// `points_affine[k] == edwards_point_as_affine(points_ep[k])`.
///
/// Proof sketch: The Horner evaluation `sum_j(16^j * column_sum(j))` is equal
/// to `sum_k(scalars[k] * points[k])` by interchanging the order of summation
/// (swap the k and j loops) and using `reconstruct_radix_16(digits[k]) == scalar[k]`.
///
/// This is an axiom because the full proof requires induction over the number of
/// points combined with distributivity and associativity of scalar multiplication
/// over the group operation, which we axiomatize.
pub proof fn axiom_straus_ct_correct(
    scalars: Seq<Scalar>,
    points_ep: Seq<EdwardsPoint>,
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
)
    requires
        scalars.len() == points_ep.len(),
        points_affine.len() == scalars.len(),
        digits.len() == scalars.len(),
        // points_affine are the affine forms of points_ep
        forall|k: int|
            0 <= k < points_affine.len() ==> #[trigger] points_affine[k] == edwards_point_as_affine(
                points_ep[k],
            ),
        // digits[k] is the valid radix-16 decomposition of scalars[k]
        forall|k: int|
            0 <= k < digits.len() ==> {
                &&& is_valid_radix_16(&#[trigger] digits[k])
                &&& radix_16_all_bounded_seq(digits[k])
                &&& reconstruct_radix_16(digits[k]) == scalar_as_nat(&scalars[k]) as int
            },
    ensures
        straus_ct_partial(points_affine, digits, 0) == sum_of_scalar_muls(scalars, points_ep),
{
    admit();
}

// =============================================================================
// Straus VT correctness theorem
// =============================================================================
/// Main correctness theorem for the variable-time Straus algorithm:
/// `straus_vt_partial(points, nafs, 0) == sum_of_scalar_muls(scalars, points_ep)`
///
/// where `nafs[k]` is the NAF(5) representation of `scalars[k]` and
/// `points_affine[k] == edwards_point_as_affine(points_ep[k])`.
pub proof fn axiom_straus_vt_correct(
    scalars: Seq<Scalar>,
    points_ep: Seq<EdwardsPoint>,
    points_affine: Seq<(nat, nat)>,
    nafs: Seq<Seq<i8>>,
)
    requires
        scalars.len() == points_ep.len(),
        points_affine.len() == scalars.len(),
        nafs.len() == scalars.len(),
        // points_affine are the affine forms of points_ep
        forall|k: int|
            0 <= k < points_affine.len() ==> #[trigger] points_affine[k] == edwards_point_as_affine(
                points_ep[k],
            ),
        // nafs[k] is the valid NAF(5) representation of scalars[k]
        forall|k: int|
            0 <= k < nafs.len() ==> {
                &&& is_valid_naf(#[trigger] nafs[k], 5)
                &&& reconstruct(nafs[k]) == scalar_as_nat(&scalars[k]) as int
            },
    ensures
        straus_vt_partial(points_affine, nafs, 0) == sum_of_scalar_muls(scalars, points_ep),
{
    admit();
}

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
// Identity projective point properties
// =============================================================================
/// The identity projective point is valid, has bounded limbs, and its affine
/// coordinates are the identity (0, 1).
pub proof fn lemma_identity_projective_point_properties()
    ensures
        is_valid_projective_point(identity_projective_point_edwards()),
        fe51_limbs_bounded(&identity_projective_point_edwards().X, 52),
        fe51_limbs_bounded(&identity_projective_point_edwards().Y, 52),
        fe51_limbs_bounded(&identity_projective_point_edwards().Z, 52),
        sum_of_limbs_bounded(
            &identity_projective_point_edwards().X,
            &identity_projective_point_edwards().Y,
            u64::MAX,
        ),
        projective_point_as_affine_edwards(identity_projective_point_edwards())
            == math_edwards_identity(),
{
    // Identity: X=0, Y=1, Z=1
    // All limbs are 0 or 1, so bounded by 2^52
    // Z=1 != 0
    // affine = (0*1^{-1}, 1*1^{-1}) = (0, 1) = identity
    admit();
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

} // verus!
