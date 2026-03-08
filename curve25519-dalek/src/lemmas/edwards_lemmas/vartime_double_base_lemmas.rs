//! Lemmas specific to `backend::serial::scalar_mul::vartime_double_base`.
#![allow(non_snake_case)]

#[cfg(verus_keep_ghost)]
use crate::lemmas::edwards_lemmas::straus_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::*;
#[cfg(verus_keep_ghost)]
use crate::specs::field_specs::*;
#[cfg(verus_keep_ghost)]
use crate::specs::field_specs_u64::*;

use vstd::prelude::*;

verus! {

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
        straus_column_sum(pts_affine, nafs, i, 1)
            == edwards_scalar_mul_signed(A_affine, a_naf[i] as int),
{
    lemma_column_sum_single(A_affine, a_naf, i);
    lemma_column_sum_prefix_eq(
        seq![A_affine],
        seq![a_naf],
        pts_affine,
        nafs,
        i,
        1,
    );
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
