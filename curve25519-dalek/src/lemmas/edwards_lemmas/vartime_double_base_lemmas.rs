//! Lemmas for vartime_double_base scalar multiplication: aA + bB.
//!
//! Proves correctness of `vartime_double_base::mul` which computes aA + bB
//! where B is the Ed25519 basepoint, using Straus variable-time evaluation
//! with NAF(5) for A and NAF(8) for B (precomputed-tables) or NAF(5) for both.
//!
//! ## Bundled validity predicate:
//! - `vt_double_base_input_valid`: groups table bounds, NAF validity, and point coordinates
//!
//! ## Select lemmas (precomputed-tables):
//! - `lemma_naf_select_is_signed_scalar_mul_affine8`: NafLookupTable8 select -> \[d\] B
//! - `lemma_naf_digit_positive_select_preconditions_8`: bit-vector preconditions for positive NAF(8) digit
//! - `lemma_naf_digit_negative_select_preconditions_8`: bit-vector preconditions for negative NAF(8) digit
//!
//! ## Column sum helpers:
//! - `lemma_vt_double_base_col_a`: column sum after processing digit a
//! - `lemma_vt_double_base_col_ab`: column sum after processing digits a and b
//!
//! ## Axioms:
//! - `axiom_affine_odd_multiples_entries_valid`: each entry of a valid NAF(8) table is a valid AffineNielsPoint
#![allow(non_snake_case)]

#[cfg(feature = "precomputed-tables")]
use crate::backend::serial::curve_models::AffineNielsPoint;
use crate::backend::serial::curve_models::ProjectiveNielsPoint;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::straus_lemmas::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::window_specs::*;

use vstd::prelude::*;

verus! {

// ============================================================================
// Select lemmas (precomputed-tables)
// ============================================================================
/// For precomputed tables: select from 64-entry AffineNiels table
#[cfg(feature = "precomputed-tables")]
pub proof fn lemma_naf_select_is_signed_scalar_mul_affine8(
    table: [AffineNielsPoint; 64],
    digit: i8,
    result: AffineNielsPoint,
    basepoint: (nat, nat),
)
    requires
        0 < digit < 128,
        (digit as int) % 2 != 0,
        forall|j: int|
            0 <= j < 64 ==> affine_niels_point_as_affine_edwards(#[trigger] table[j])
                == edwards_scalar_mul(basepoint, (2 * j + 1) as nat),
        result == table[((digit as int) / 2) as int],
    ensures
        affine_niels_point_as_affine_edwards(result) == edwards_scalar_mul_signed(
            basepoint,
            digit as int,
        ),
{
    reveal(edwards_scalar_mul_signed);
    let j = ((digit as int) / 2) as int;
    assert(0 <= j < 64);
    assert(affine_niels_point_as_affine_edwards(table[j]) == edwards_scalar_mul(
        basepoint,
        (2 * j + 1) as nat,
    ));
    assert((2 * j + 1) as nat == digit as nat);
}

/// For a NAF digit d > 0 from a valid NAF(8), d is odd and d < 128.
#[cfg(feature = "precomputed-tables")]
pub proof fn lemma_naf_digit_positive_select_preconditions_8(digit: i8)
    requires
        digit > 0,
        (digit as int) % 2 != 0,
        digit < 128,
    ensures
        (digit as usize) & 1usize == 1usize,
        (digit as usize) < 128,
{
    assert((digit as usize) & 1usize == 1usize) by (bit_vector)
        requires
            digit > 0i8,
            digit <= 127i8,
            (digit as int) % 2 != 0,
    ;
}

/// For a NAF digit d < 0 from a valid NAF(8), -d is odd and -d < 128.
#[cfg(feature = "precomputed-tables")]
pub proof fn lemma_naf_digit_negative_select_preconditions_8(digit: i8)
    requires
        digit < 0,
        (digit as int) % 2 != 0,
        digit > -128,
    ensures
        ((-digit) as usize) & 1usize == 1usize,
        ((-digit) as usize) < 128,
{
    assert(((-digit) as usize) & 1usize == 1usize) by (bit_vector)
        requires
            digit < 0i8,
            digit > -128i8,
            (digit as int) % 2 != 0,
    ;
}

// ============================================================================
// Axioms
// ============================================================================
/// Axiom: each entry in a valid NAF lookup table (width 8) is a valid AffineNielsPoint.
#[cfg(feature = "precomputed-tables")]
pub proof fn axiom_affine_odd_multiples_entries_valid(
    table: [AffineNielsPoint; 64],
    basepoint: (nat, nat),
    idx: int,
)
    requires
        0 <= idx < 64,
        naf_lookup_table8_affine_limbs_bounded(table),
        is_valid_naf_lookup_table8_affine_coords(table, basepoint),
    ensures
        is_valid_affine_niels_point(table[idx]),
{
    admit();
}

// ============================================================================
// Bundled predicates
// ============================================================================
#[cfg(feature = "precomputed-tables")]
pub open spec fn vt_double_base_input_valid(
    a_naf: Seq<i8>,
    b_naf: Seq<i8>,
    table_A: [ProjectiveNielsPoint; 8],
    table_B: [AffineNielsPoint; 64],
    A_affine: (nat, nat),
    B_affine: (nat, nat),
    pts_affine: Seq<(nat, nat)>,
    nafs: Seq<Seq<i8>>,
) -> bool {
    &&& pts_affine == seq![A_affine, B_affine]
    &&& nafs == seq![a_naf, b_naf]
    &&& pts_affine.len() == 2
    &&& nafs.len() == 2
    &&& A_affine.0 < p()
    &&& A_affine.1 < p()
    &&& B_affine.0 < p()
    &&& B_affine.1 < p()
    &&& a_naf.len() == 256
    &&& b_naf.len() == 256
    &&& is_valid_naf(a_naf, 5)
    &&& is_valid_naf(b_naf, 8)
    &&& naf_lookup_table5_projective_limbs_bounded(table_A)
    &&& forall|j: int| 0 <= j < 8 ==> is_valid_projective_niels_point(#[trigger] table_A[j])
    &&& forall|j: int|
        0 <= j < 8 ==> projective_niels_point_as_affine_edwards(#[trigger] table_A[j])
            == edwards_scalar_mul(A_affine, (2 * j + 1) as nat)
    &&& naf_lookup_table8_affine_limbs_bounded(table_B)
    &&& is_valid_naf_lookup_table8_affine_coords(table_B, B_affine)
}

#[cfg(not(feature = "precomputed-tables"))]
pub open spec fn vt_double_base_input_valid(
    a_naf: Seq<i8>,
    b_naf: Seq<i8>,
    table_A: [ProjectiveNielsPoint; 8],
    table_B: [ProjectiveNielsPoint; 8],
    A_affine: (nat, nat),
    B_affine: (nat, nat),
    pts_affine: Seq<(nat, nat)>,
    nafs: Seq<Seq<i8>>,
) -> bool {
    &&& pts_affine == seq![A_affine, B_affine]
    &&& nafs == seq![a_naf, b_naf]
    &&& pts_affine.len() == 2
    &&& nafs.len() == 2
    &&& A_affine.0 < p()
    &&& A_affine.1 < p()
    &&& B_affine.0 < p()
    &&& B_affine.1 < p()
    &&& a_naf.len() == 256
    &&& b_naf.len() == 256
    &&& is_valid_naf(a_naf, 5)
    &&& is_valid_naf(b_naf, 5)
    &&& naf_lookup_table5_projective_limbs_bounded(table_A)
    &&& forall|j: int| 0 <= j < 8 ==> is_valid_projective_niels_point(#[trigger] table_A[j])
    &&& forall|j: int|
        0 <= j < 8 ==> projective_niels_point_as_affine_edwards(#[trigger] table_A[j])
            == edwards_scalar_mul(A_affine, (2 * j + 1) as nat)
    &&& naf_lookup_table5_projective_limbs_bounded(table_B)
    &&& forall|j: int| 0 <= j < 8 ==> is_valid_projective_niels_point(#[trigger] table_B[j])
    &&& forall|j: int|
        0 <= j < 8 ==> projective_niels_point_as_affine_edwards(#[trigger] table_B[j])
            == edwards_scalar_mul(B_affine, (2 * j + 1) as nat)
}

// ============================================================================
// Column sum helpers
// ============================================================================
pub proof fn lemma_vt_double_base_col_a(
    A_affine: (nat, nat),
    B_affine: (nat, nat),
    a_naf: Seq<i8>,
    b_naf: Seq<i8>,
    pts_affine: Seq<(nat, nat)>,
    nafs: Seq<Seq<i8>>,
    i: int,
)
    requires
        pts_affine == seq![A_affine, B_affine],
        nafs == seq![a_naf, b_naf],
        A_affine.0 < p(),
        A_affine.1 < p(),
        a_naf.len() == 256,
        0 <= i < 256,
    ensures
        straus_column_sum(pts_affine, nafs, i, 1) == edwards_scalar_mul_signed(
            A_affine,
            a_naf[i] as int,
        ),
{
    lemma_column_sum_single(A_affine, a_naf, i);
    lemma_column_sum_prefix_eq(seq![A_affine], seq![a_naf], pts_affine, nafs, i, 1);
}

pub proof fn lemma_vt_double_base_col_ab(
    A_affine: (nat, nat),
    B_affine: (nat, nat),
    a_naf: Seq<i8>,
    b_naf: Seq<i8>,
    pts_affine: Seq<(nat, nat)>,
    nafs: Seq<Seq<i8>>,
    i: int,
)
    requires
        pts_affine == seq![A_affine, B_affine],
        nafs == seq![a_naf, b_naf],
        b_naf.len() == 256,
        0 <= i < 256,
    ensures
        straus_column_sum(pts_affine, nafs, i, 2) == edwards_add(
            straus_column_sum(pts_affine, nafs, i, 1).0,
            straus_column_sum(pts_affine, nafs, i, 1).1,
            edwards_scalar_mul_signed(B_affine, b_naf[i] as int).0,
            edwards_scalar_mul_signed(B_affine, b_naf[i] as int).1,
        ),
{
    reveal(straus_column_sum);
    assert(pts_affine[1] == B_affine);
    assert(nafs[1] == b_naf);
}

} // verus!
