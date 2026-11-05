//! Lemmas specific to `backend::serial::scalar_mul::vartime_double_base`.
#![allow(non_snake_case)]

use crate::backend::serial::curve_models::ProjectiveNielsPoint;
use crate::edwards::EdwardsPoint;

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
use crate::specs::window_specs::*;

use vstd::prelude::*;

verus! {

/// Both input points are on the curve.
///
/// Opaque so that loop contexts do not unfold the curve equation.
#[verifier::opaque]
pub open spec fn vartime_double_base_points_on_curve(
    A_affine: (nat, nat),
    B_affine: (nat, nat),
) -> bool {
    is_on_edwards_curve(A_affine.0, A_affine.1) && is_on_edwards_curve(B_affine.0, B_affine.1)
}

pub open spec fn vartime_double_base_shared_input_valid(
    A_affine: (nat, nat),
    B_affine: (nat, nat),
    pts_affine: Seq<(nat, nat)>,
    a_naf: Seq<i8>,
    b_naf: Seq<i8>,
    nafs: Seq<Seq<i8>>,
    table_A: [ProjectiveNielsPoint; 8],
    A: EdwardsPoint,
    bp: EdwardsPoint,
) -> bool {
    &&& A_affine.0 < p()
    &&& A_affine.1 < p()
    &&& B_affine.0 < p()
    &&& B_affine.1 < p()
    &&& vartime_double_base_points_on_curve(A_affine, B_affine)
    &&& A_affine == edwards_point_as_affine(A)
    &&& B_affine == edwards_point_as_affine(bp)
    &&& a_naf.len() == 256
    &&& b_naf.len() == 256
    &&& pts_affine.len() == 2
    &&& pts_affine[0] == A_affine
    &&& pts_affine[1] == B_affine
    &&& nafs.len() == 2
    &&& nafs[0] == a_naf
    &&& nafs[1] == b_naf
    &&& is_valid_naf(a_naf, 5)
    &&& {
        #[cfg(feature = "precomputed-tables")]
        { is_valid_naf(b_naf, 8) }
        #[cfg(not(feature = "precomputed-tables"))]
        { is_valid_naf(b_naf, 5) }
    }
    &&& naf_lookup_table5_projective_limbs_bounded(table_A)
    &&& is_valid_naf_lookup_table5_projective(table_A, A)
    &&& forall|j: int| 0 <= j < 8 ==> is_valid_projective_niels_point(#[trigger] table_A[j])
}

/// Both input points are on the curve, as a sequence.
pub proof fn lemma_vartime_double_base_pts_on_curve(
    pts_affine: Seq<(nat, nat)>,
    A_affine: (nat, nat),
    B_affine: (nat, nat),
)
    requires
        pts_affine.len() == 2,
        pts_affine[0] == A_affine,
        pts_affine[1] == B_affine,
        vartime_double_base_points_on_curve(A_affine, B_affine),
    ensures
        all_on_edwards_curve(pts_affine),
{
    reveal(vartime_double_base_points_on_curve);
    assert forall|k: int| 0 <= k < pts_affine.len() implies is_on_edwards_curve(
        (#[trigger] pts_affine[k]).0,
        pts_affine[k].1,
    ) by {
        if k == 0 {
        } else {
            assert(k == 1);
        }
    }
}

/// The points and the terms of one column step are on the curve.
pub proof fn lemma_vartime_double_base_terms_on_curve(
    pts_affine: Seq<(nat, nat)>,
    nafs: Seq<Seq<i8>>,
    A_affine: (nat, nat),
    B_affine: (nat, nat),
    i: int,
    digit: int,
)
    requires
        0 <= i < 256,
        pts_affine.len() == 2,
        pts_affine[0] == A_affine,
        pts_affine[1] == B_affine,
        vartime_double_base_points_on_curve(A_affine, B_affine),
    ensures
        all_on_edwards_curve(pts_affine),
        ({
            let prev = straus_vt_partial(pts_affine, nafs, i + 1);
            let doubled = edwards_double(prev.0, prev.1);
            is_on_edwards_curve(doubled.0, doubled.1)
        }),
        is_on_edwards_curve(
            straus_column_sum(pts_affine, nafs, i, 1).0,
            straus_column_sum(pts_affine, nafs, i, 1).1,
        ),
        is_on_edwards_curve(
            edwards_scalar_mul_signed(B_affine, digit).0,
            edwards_scalar_mul_signed(B_affine, digit).1,
        ),
{
    lemma_vartime_double_base_pts_on_curve(pts_affine, A_affine, B_affine);
    reveal(vartime_double_base_points_on_curve);
    lemma_straus_vt_partial_on_curve(pts_affine, nafs, i + 1);
    let prev = straus_vt_partial(pts_affine, nafs, i + 1);
    axiom_edwards_add_complete(prev.0, prev.1, prev.0, prev.1);
    lemma_column_sum_on_curve(pts_affine, nafs, i, 1);
    lemma_edwards_scalar_mul_signed_on_curve(B_affine, digit);
}

/// Associativity for one column step: (2H + col_a) + [d]B = 2H + (col_a + [d]B).
pub proof fn lemma_vartime_double_base_assoc(
    pts_affine: Seq<(nat, nat)>,
    nafs: Seq<Seq<i8>>,
    A_affine: (nat, nat),
    B_affine: (nat, nat),
    i: int,
    digit: int,
)
    requires
        0 <= i < 256,
        pts_affine.len() == 2,
        pts_affine[0] == A_affine,
        pts_affine[1] == B_affine,
        vartime_double_base_points_on_curve(A_affine, B_affine),
    ensures
        ({
            let prev = straus_vt_partial(pts_affine, nafs, i + 1);
            let doubled = edwards_double(prev.0, prev.1);
            let col_a = straus_column_sum(pts_affine, nafs, i, 1);
            let term_b = edwards_scalar_mul_signed(B_affine, digit);
            let left = edwards_add(doubled.0, doubled.1, col_a.0, col_a.1);
            let right = edwards_add(col_a.0, col_a.1, term_b.0, term_b.1);
            edwards_add(left.0, left.1, term_b.0, term_b.1) == edwards_add(
                doubled.0,
                doubled.1,
                right.0,
                right.1,
            )
        }),
{
    lemma_vartime_double_base_terms_on_curve(pts_affine, nafs, A_affine, B_affine, i, digit);
    let prev = straus_vt_partial(pts_affine, nafs, i + 1);
    let doubled = edwards_double(prev.0, prev.1);
    let col_a = straus_column_sum(pts_affine, nafs, i, 1);
    let term_b = edwards_scalar_mul_signed(B_affine, digit);
    axiom_edwards_add_associative(doubled.0, doubled.1, col_a.0, col_a.1, term_b.0, term_b.1);
}

pub proof fn lemma_vartime_double_base_col_a(
    pts_affine: Seq<(nat, nat)>,
    nafs: Seq<Seq<i8>>,
    A_affine: (nat, nat),
    a_naf: Seq<i8>,
    i: int,
)
    requires
        0 <= i < 256,
        a_naf.len() == 256,
        pts_affine.len() >= 1,
        nafs.len() >= 1,
        pts_affine[0] == A_affine,
        nafs[0] == a_naf,
        A_affine.0 < p(),
        A_affine.1 < p(),
    ensures
        straus_column_sum(pts_affine, nafs, i, 1) == edwards_scalar_mul_signed(
            A_affine,
            a_naf[i] as int,
        ),
{
    lemma_column_sum_single(A_affine, a_naf, i);
    lemma_column_sum_prefix_eq(seq![A_affine], seq![a_naf], pts_affine, nafs, i, 1);
}

pub proof fn lemma_vartime_double_base_col_ab(
    pts_affine: Seq<(nat, nat)>,
    nafs: Seq<Seq<i8>>,
    B_affine: (nat, nat),
    b_naf: Seq<i8>,
    i: int,
)
    requires
        0 <= i < 256,
        b_naf.len() == 256,
        pts_affine.len() >= 2,
        nafs.len() >= 2,
        pts_affine[1] == B_affine,
        nafs[1] == b_naf,
    ensures
        straus_column_sum(pts_affine, nafs, i, 2) == edwards_add(
            straus_column_sum(pts_affine, nafs, i, 1).0,
            straus_column_sum(pts_affine, nafs, i, 1).1,
            edwards_scalar_mul_signed(B_affine, b_naf[i] as int).0,
            edwards_scalar_mul_signed(B_affine, b_naf[i] as int).1,
        ),
{
    reveal(straus_column_sum);
}

} // verus!
