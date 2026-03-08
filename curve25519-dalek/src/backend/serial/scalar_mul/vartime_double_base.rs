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
#![allow(non_snake_case)]

use core::cmp::Ordering;

#[cfg(feature = "precomputed-tables")]
use crate::backend::serial::curve_models::AffineNielsPoint;
use crate::backend::serial::curve_models::{ProjectiveNielsPoint, ProjectivePoint};
use crate::constants;
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::Identity;
use crate::window::NafLookupTable5;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::straus_lemmas::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::vartime_double_base_lemmas::*;
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

use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

#[verifier::rlimit(50)]
/// Compute \\(aA + bB\\) in variable time, where \\(B\\) is the Ed25519 basepoint.
pub fn mul(a: &Scalar, A: &EdwardsPoint, b: &Scalar) -> (out: EdwardsPoint)
    requires
        is_well_formed_edwards_point(*A),
        scalar_as_nat(a) < pow2(255),
        scalar_as_nat(b) < pow2(255),
    ensures
        is_well_formed_edwards_point(out),
        edwards_point_as_affine(out) == {
            let aA = edwards_scalar_mul(edwards_point_as_affine(*A), scalar_as_nat(a));
            let bB = edwards_scalar_mul(spec_ed25519_basepoint(), scalar_as_nat(b));
            edwards_add(aA.0, aA.1, bB.0, bB.1)
        },
{
    let a_naf = a.non_adjacent_form(5);

    #[cfg(feature = "precomputed-tables")]
    let b_naf = b.non_adjacent_form(8);
    #[cfg(not(feature = "precomputed-tables"))]
    let b_naf = b.non_adjacent_form(5);

    let table_A = NafLookupTable5::<ProjectiveNielsPoint>::from(A);
    #[cfg(feature = "precomputed-tables")]
    let table_B = &constants::AFFINE_ODD_MULTIPLES_OF_BASEPOINT;
    #[cfg(not(feature = "precomputed-tables"))]
    let table_B = &NafLookupTable5::<ProjectiveNielsPoint>::from(
        &constants::ED25519_BASEPOINT_POINT,
    );

    let ghost A_affine = edwards_point_as_affine(*A);
    let ghost B_affine = spec_ed25519_basepoint();
    let ghost pts_affine = seq![A_affine, B_affine];
    let ghost nafs = seq![a_naf@, b_naf@];
    let bp_for_proof = constants::ED25519_BASEPOINT_POINT;

    let mut r = ProjectivePoint::identity();
    /* <ORIGINAL CODE>
    // Find starting index
    let mut i: usize = 255;
    for j in (0..256).rev() {
        i = j;
        if a_naf[i] != 0 || b_naf[i] != 0 {
            break;
        }
    }
    // ... loop from i down to 0 using loop { ... if i == 0 { break; } i -= 1; } ...
    </ORIGINAL CODE> */
    // VERIFICATION NOTE: Restructured to while loop from 256 down to 1 (processing index i-1).
    // Dropping the find-starting-index optimization doesn't affect correctness.
    let mut i: usize = 256;

    proof {
        lemma_identity_projective_point_properties();
        lemma_edwards_point_as_affine_canonical(*A);
        lemma_edwards_point_as_affine_canonical(bp_for_proof);
        assert(edwards_point_as_affine(bp_for_proof) == B_affine);
        assert forall|j: int| 0 <= j < 8 implies is_valid_projective_niels_point(
            #[trigger] table_A.0[j],
        ) by {}
        assert forall|j: int| 0 <= j < 8 implies projective_niels_point_as_affine_edwards(
            #[trigger] table_A.0[j],
        ) == edwards_scalar_mul(A_affine, (2 * j + 1) as nat) by {}
        #[cfg(feature = "precomputed-tables")]
        {
            axiom_affine_odd_multiples_of_basepoint_valid();
        }
        #[cfg(not(feature = "precomputed-tables"))]
        {
            assert(naf_lookup_table5_projective_limbs_bounded(table_B.0));
            assert forall|j: int| 0 <= j < 8 implies is_valid_projective_niels_point(
                #[trigger] table_B.0[j],
            ) by {}
            assert forall|j: int| 0 <= j < 8 implies projective_niels_point_as_affine_edwards(
                #[trigger] table_B.0[j],
            ) == edwards_scalar_mul(B_affine, (2 * j + 1) as nat) by {}
        }
        assert(vt_double_base_input_valid(
            a_naf@,
            b_naf@,
            table_A.0,
            table_B.0,
            A_affine,
            B_affine,
            pts_affine,
            nafs,
        ));
        lemma_straus_vt_base(pts_affine, nafs);
        assert(projective_point_as_affine_edwards(r) == edwards_identity());
    }

    while i > 0
        invariant
            0 <= i <= 256,
            is_valid_projective_point(r),
            fe51_limbs_bounded(&r.X, 52),
            fe51_limbs_bounded(&r.Y, 52),
            fe51_limbs_bounded(&r.Z, 52),
            sum_of_limbs_bounded(&r.X, &r.Y, u64::MAX),
            vt_double_base_input_valid(
                a_naf@,
                b_naf@,
                table_A.0,
                table_B.0,
                A_affine,
                B_affine,
                pts_affine,
                nafs,
            ),
            projective_point_as_affine_edwards(r) == straus_vt_partial(pts_affine, nafs, i as int),
        decreases i,
    {
        i = i - 1;
        let mut t = r.double();
        let ghost doubled_affine = completed_point_as_affine_edwards(t);
        let ghost col_a = straus_column_sum(pts_affine, nafs, i as int, 1);

        proof {
            assert(p() > 2) by {
                p_gt_2();
            }
            assert(edwards_add(
                doubled_affine.0,
                doubled_affine.1,
                edwards_identity().0,
                edwards_identity().1,
            ) == doubled_affine) by {
                lemma_edwards_add_identity_right_canonical(doubled_affine);
            }
        }

        // Process a_naf[i]
        match a_naf[i].cmp(&0) {
            Ordering::Greater => {
                proof {
                    let digit = a_naf@[i as int];
                    assert(1 <= digit && digit <= 15 && (digit as int) % 2 != 0) by {
                        assert(is_valid_naf(a_naf@, 5));
                        assert(pow2(4) == 16) by {
                            lemma2_to64();
                        }
                    }
                    lemma_naf_digit_positive_select_preconditions(digit);
                }
                let selected_A = table_A.select(a_naf[i] as usize);
                t = &t.as_extended() + &selected_A;
                proof {
                    let ghost digit = a_naf@[i as int];
                    let term_a = edwards_scalar_mul_signed(A_affine, digit as int);
                    assert(projective_niels_point_as_affine_edwards(selected_A) == term_a) by {
                        lemma_naf_select_is_signed_scalar_mul_projective(
                            table_A.0,
                            digit,
                            selected_A,
                            A_affine,
                            true,
                        );
                    }
                    assert(col_a == term_a) by {
                        lemma_vt_double_base_col_a(
                            A_affine,
                            B_affine,
                            a_naf@,
                            b_naf@,
                            pts_affine,
                            nafs,
                            i as int,
                        );
                    }
                }
            },
            Ordering::Less => {
                proof {
                    let digit = a_naf@[i as int];
                    assert(-15 <= digit && digit <= -1 && (digit as int) % 2 != 0) by {
                        assert(is_valid_naf(a_naf@, 5));
                        assert(pow2(4) == 16) by {
                            lemma2_to64();
                        }
                    }
                    lemma_naf_digit_negative_select_preconditions(digit);
                }
                let selected_A = table_A.select((-a_naf[i]) as usize);
                t = &t.as_extended() - &selected_A;
                proof {
                    let ghost digit = a_naf@[i as int];
                    let ghost abs_digit = (-digit) as i8;
                    let term_a = edwards_scalar_mul_signed(A_affine, digit as int);
                    assert(projective_niels_point_as_affine_edwards(selected_A)
                        == edwards_scalar_mul_signed(A_affine, abs_digit as int)) by {
                        lemma_naf_select_is_signed_scalar_mul_projective(
                            table_A.0,
                            abs_digit,
                            selected_A,
                            A_affine,
                            true,
                        );
                    }
                    assert(term_a == edwards_neg(
                        projective_niels_point_as_affine_edwards(selected_A),
                    )) by {
                        lemma_neg_of_signed_scalar_mul(A_affine, abs_digit as int);
                        assert(digit as int == -(abs_digit as int));
                    }
                    assert(col_a == term_a) by {
                        lemma_vt_double_base_col_a(
                            A_affine,
                            B_affine,
                            a_naf@,
                            b_naf@,
                            pts_affine,
                            nafs,
                            i as int,
                        );
                    }
                }
            },
            Ordering::Equal => {
                proof {
                    assert(col_a == edwards_identity()) by {
                        lemma_column_sum_canonical(pts_affine, nafs, i as int, 0);
                        lemma_column_sum_step_zero_digit(pts_affine, nafs, i as int, 0);
                    }
                }
            },
        }

        let ghost col_ab = straus_column_sum(pts_affine, nafs, i as int, 2);

        // Process b_naf[i] — precomputed-tables variant (AffineNielsPoint)
        #[cfg(feature = "precomputed-tables")]
        match b_naf[i].cmp(&0) {
            Ordering::Greater => {
                proof {
                    let digit = b_naf@[i as int];
                    assert(1 <= digit && digit < 128 && (digit as int) % 2 != 0) by {
                        assert(is_valid_naf(b_naf@, 8));
                        assert(pow2(7) == 128) by {
                            lemma2_to64();
                        }
                    }
                    lemma_naf_digit_positive_select_preconditions_8(digit);
                }
                let b_digit = b_naf[i] as usize;
                let selected_B = table_B.select(b_digit);
                let ext_b = t.as_extended();
                proof {
                    let sel_idx = (b_digit as int) / 2;
                    assert(is_valid_affine_niels_point(selected_B)) by {
                        axiom_affine_odd_multiples_entries_valid(table_B.0, B_affine, sel_idx);
                    }
                    assert(edwards_z_sum_bounded(ext_b)) by {
                        lemma_unfold_edwards(ext_b);
                        crate::lemmas::field_lemmas::add_lemmas::lemma_sum_of_limbs_bounded_from_fe51_bounded(
                        &ext_b.Z, &ext_b.Z, 52);
                    }
                }
                t = &ext_b + &selected_B;
                proof {
                    let ghost digit = b_naf@[i as int];
                    let term_b = edwards_scalar_mul_signed(B_affine, digit as int);
                    assert(affine_niels_point_as_affine_edwards(selected_B) == term_b) by {
                        lemma_naf_select_is_signed_scalar_mul_affine8(
                            table_B.0,
                            digit,
                            selected_B,
                            B_affine,
                        );
                    }
                    assert(col_ab == edwards_add(col_a.0, col_a.1, term_b.0, term_b.1)) by {
                        lemma_vt_double_base_col_ab(
                            A_affine,
                            B_affine,
                            a_naf@,
                            b_naf@,
                            pts_affine,
                            nafs,
                            i as int,
                        );
                    }
                    assert(completed_point_as_affine_edwards(t) == edwards_add(
                        doubled_affine.0,
                        doubled_affine.1,
                        col_ab.0,
                        col_ab.1,
                    )) by {
                        axiom_edwards_add_associative(
                            doubled_affine.0,
                            doubled_affine.1,
                            col_a.0,
                            col_a.1,
                            term_b.0,
                            term_b.1,
                        );
                    }
                }
            },
            Ordering::Less => {
                proof {
                    let digit = b_naf@[i as int];
                    assert(-128 < digit && digit <= -1 && (digit as int) % 2 != 0) by {
                        assert(is_valid_naf(b_naf@, 8));
                        assert(pow2(7) == 128) by {
                            lemma2_to64();
                        }
                    }
                    lemma_naf_digit_negative_select_preconditions_8(digit);
                }
                let abs_b_digit = (-b_naf[i]) as usize;
                let selected_B = table_B.select(abs_b_digit);
                let ext_b = t.as_extended();
                proof {
                    let sel_idx = (abs_b_digit as int) / 2;
                    assert(is_valid_affine_niels_point(selected_B)) by {
                        axiom_affine_odd_multiples_entries_valid(table_B.0, B_affine, sel_idx);
                    }
                    assert(edwards_z_sum_bounded(ext_b)) by {
                        lemma_unfold_edwards(ext_b);
                        crate::lemmas::field_lemmas::add_lemmas::lemma_sum_of_limbs_bounded_from_fe51_bounded(
                        &ext_b.Z, &ext_b.Z, 52);
                    }
                }
                t = &ext_b - &selected_B;
                proof {
                    let ghost digit = b_naf@[i as int];
                    let ghost abs_digit = (-digit) as i8;
                    let term_b = edwards_scalar_mul_signed(B_affine, digit as int);
                    assert(affine_niels_point_as_affine_edwards(selected_B)
                        == edwards_scalar_mul_signed(B_affine, abs_digit as int)) by {
                        lemma_naf_select_is_signed_scalar_mul_affine8(
                            table_B.0,
                            abs_digit,
                            selected_B,
                            B_affine,
                        );
                    }
                    assert(term_b == edwards_neg(affine_niels_point_as_affine_edwards(selected_B)))
                        by {
                        lemma_neg_of_signed_scalar_mul(B_affine, abs_digit as int);
                        assert(digit as int == -(abs_digit as int));
                    }
                    assert(col_ab == edwards_add(col_a.0, col_a.1, term_b.0, term_b.1)) by {
                        lemma_vt_double_base_col_ab(
                            A_affine,
                            B_affine,
                            a_naf@,
                            b_naf@,
                            pts_affine,
                            nafs,
                            i as int,
                        );
                    }
                    assert(completed_point_as_affine_edwards(t) == edwards_add(
                        doubled_affine.0,
                        doubled_affine.1,
                        col_ab.0,
                        col_ab.1,
                    )) by {
                        axiom_edwards_add_associative(
                            doubled_affine.0,
                            doubled_affine.1,
                            col_a.0,
                            col_a.1,
                            term_b.0,
                            term_b.1,
                        );
                    }
                }
            },
            Ordering::Equal => {
                proof {
                    assert(col_ab == col_a) by {
                        lemma_column_sum_canonical(pts_affine, nafs, i as int, 1);
                        lemma_column_sum_step_zero_digit(pts_affine, nafs, i as int, 1);
                    }
                    assert(completed_point_as_affine_edwards(t) == edwards_add(
                        doubled_affine.0,
                        doubled_affine.1,
                        col_ab.0,
                        col_ab.1,
                    ));
                }
            },
        }

        // Process b_naf[i] — non-precomputed variant (ProjectiveNielsPoint)
        #[cfg(not(feature = "precomputed-tables"))]
        match b_naf[i].cmp(&0) {
            Ordering::Greater => {
                proof {
                    let digit = b_naf@[i as int];
                    assert(1 <= digit && digit <= 15 && (digit as int) % 2 != 0) by {
                        assert(is_valid_naf(b_naf@, 5));
                        assert(pow2(4) == 16) by {
                            lemma2_to64();
                        }
                    }
                    lemma_naf_digit_positive_select_preconditions(digit);
                }
                let selected_B = table_B.select(b_naf[i] as usize);
                t = &t.as_extended() + &selected_B;
                proof {
                    let ghost digit = b_naf@[i as int];
                    let term_b = edwards_scalar_mul_signed(B_affine, digit as int);
                    assert(projective_niels_point_as_affine_edwards(selected_B) == term_b) by {
                        lemma_naf_select_is_signed_scalar_mul_projective(
                            table_B.0,
                            digit,
                            selected_B,
                            B_affine,
                            true,
                        );
                    }
                    assert(col_ab == edwards_add(col_a.0, col_a.1, term_b.0, term_b.1)) by {
                        lemma_vt_double_base_col_ab(
                            A_affine,
                            B_affine,
                            a_naf@,
                            b_naf@,
                            pts_affine,
                            nafs,
                            i as int,
                        );
                    }
                    assert(completed_point_as_affine_edwards(t) == edwards_add(
                        doubled_affine.0,
                        doubled_affine.1,
                        col_ab.0,
                        col_ab.1,
                    )) by {
                        axiom_edwards_add_associative(
                            doubled_affine.0,
                            doubled_affine.1,
                            col_a.0,
                            col_a.1,
                            term_b.0,
                            term_b.1,
                        );
                    }
                }
            },
            Ordering::Less => {
                proof {
                    let digit = b_naf@[i as int];
                    assert(-15 <= digit && digit <= -1 && (digit as int) % 2 != 0) by {
                        assert(is_valid_naf(b_naf@, 5));
                        assert(pow2(4) == 16) by {
                            lemma2_to64();
                        }
                    }
                    lemma_naf_digit_negative_select_preconditions(digit);
                }
                let selected_B = table_B.select((-b_naf[i]) as usize);
                t = &t.as_extended() - &selected_B;
                proof {
                    let ghost digit = b_naf@[i as int];
                    let ghost abs_digit = (-digit) as i8;
                    let term_b = edwards_scalar_mul_signed(B_affine, digit as int);
                    assert(projective_niels_point_as_affine_edwards(selected_B)
                        == edwards_scalar_mul_signed(B_affine, abs_digit as int)) by {
                        lemma_naf_select_is_signed_scalar_mul_projective(
                            table_B.0,
                            abs_digit,
                            selected_B,
                            B_affine,
                            true,
                        );
                    }
                    assert(term_b == edwards_neg(
                        projective_niels_point_as_affine_edwards(selected_B),
                    )) by {
                        lemma_neg_of_signed_scalar_mul(B_affine, abs_digit as int);
                        assert(digit as int == -(abs_digit as int));
                    }
                    assert(col_ab == edwards_add(col_a.0, col_a.1, term_b.0, term_b.1)) by {
                        lemma_vt_double_base_col_ab(
                            A_affine,
                            B_affine,
                            a_naf@,
                            b_naf@,
                            pts_affine,
                            nafs,
                            i as int,
                        );
                    }
                    assert(completed_point_as_affine_edwards(t) == edwards_add(
                        doubled_affine.0,
                        doubled_affine.1,
                        col_ab.0,
                        col_ab.1,
                    )) by {
                        axiom_edwards_add_associative(
                            doubled_affine.0,
                            doubled_affine.1,
                            col_a.0,
                            col_a.1,
                            term_b.0,
                            term_b.1,
                        );
                    }
                }
            },
            Ordering::Equal => {
                proof {
                    assert(col_ab == col_a) by {
                        lemma_column_sum_canonical(pts_affine, nafs, i as int, 1);
                        lemma_column_sum_step_zero_digit(pts_affine, nafs, i as int, 1);
                    }
                    assert(completed_point_as_affine_edwards(t) == edwards_add(
                        doubled_affine.0,
                        doubled_affine.1,
                        col_ab.0,
                        col_ab.1,
                    ));
                }
            },
        }

        r = t.as_projective();

        proof {
            lemma_straus_vt_step(pts_affine, nafs, i as int);
        }
    }

    proof {
        crate::lemmas::field_lemmas::add_lemmas::lemma_fe51_limbs_bounded_weaken(&r.X, 52, 54);
        crate::lemmas::field_lemmas::add_lemmas::lemma_fe51_limbs_bounded_weaken(&r.Y, 52, 54);
        crate::lemmas::field_lemmas::add_lemmas::lemma_fe51_limbs_bounded_weaken(&r.Z, 52, 54);
    }
    let result = r.as_extended();

    proof {
        assert(reconstruct(a_naf@) == scalar_as_nat(a) as int);
        assert(reconstruct(b_naf@) == scalar_as_nat(b) as int);

        // Help Z3 with seq operations
        assert(pts_affine.drop_last() == seq![A_affine]);
        assert(nafs.drop_last() == seq![a_naf@]);
        assert(pts_affine.last() == B_affine);
        assert(nafs.last() == b_naf@);

        lemma_straus_vt_partial_peel_last(pts_affine, nafs, 0);

        // A-part
        lemma_straus_vt_single(A_affine, a_naf@, 0);
        lemma_reconstruct_naf_from_equals_reconstruct(a_naf@);
        assert(straus_vt_partial(seq![A_affine], seq![a_naf@], 0) == edwards_scalar_mul_signed(
            A_affine,
            scalar_as_nat(a) as int,
        ));

        // B-part
        lemma_straus_vt_single(B_affine, b_naf@, 0);
        lemma_reconstruct_naf_from_equals_reconstruct(b_naf@);
        assert(straus_vt_partial(seq![B_affine], seq![b_naf@], 0) == edwards_scalar_mul_signed(
            B_affine,
            scalar_as_nat(b) as int,
        ));

        // signed -> unsigned since scalars are non-negative
        assert(edwards_scalar_mul_signed(A_affine, scalar_as_nat(a) as int) == edwards_scalar_mul(
            A_affine,
            scalar_as_nat(a),
        )) by {
            reveal(edwards_scalar_mul_signed);
        }
        assert(edwards_scalar_mul_signed(B_affine, scalar_as_nat(b) as int) == edwards_scalar_mul(
            B_affine,
            scalar_as_nat(b),
        )) by {
            reveal(edwards_scalar_mul_signed);
        }

        assert(edwards_point_as_affine(result) == projective_point_as_affine_edwards(r));
        assert(is_well_formed_edwards_point(result));
    }
    result
}

} // verus!
