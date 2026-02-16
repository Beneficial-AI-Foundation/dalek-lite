//! Lemmas for Edwards point addition producing CompletedPoint results.
//!
//! These lemmas prove that the extended addition formulas used in
//! `EdwardsPoint + ProjectiveNielsPoint` and `EdwardsPoint + AffineNielsPoint`
//! correctly compute the Edwards addition in P¹ × P¹ representation.
#[allow(unused_imports)]
use crate::backend::serial::u64::constants::EDWARDS_D;
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::add_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// Bridge lemmas: prove that exec-level EdwardsPoint + Niels operations
// produce valid CompletedPoints matching spec-level edwards_add/sub.
// Sub variants follow from add via edwards_sub = edwards_add ∘ neg.
/// Exec bridge: EdwardsPoint + ProjectiveNielsPoint -> valid CompletedPoint.
pub proof fn lemma_add_projective_niels_completed_valid(
    self_point: crate::edwards::EdwardsPoint,
    other: crate::backend::serial::curve_models::ProjectiveNielsPoint,
    result: crate::backend::serial::curve_models::CompletedPoint,
    pp_val: nat,
    mm_val: nat,
    tt2d_val: nat,
    zz_val: nat,
)
    requires
        is_well_formed_edwards_point(self_point),
        is_valid_edwards_point(self_point),
        is_valid_projective_niels_point(other),
        pp_val == field_mul(
            field_add(fe51_as_canonical_nat(&self_point.Y), fe51_as_canonical_nat(&self_point.X)),
            fe51_as_canonical_nat(&other.Y_plus_X),
        ),
        mm_val == field_mul(
            field_sub(fe51_as_canonical_nat(&self_point.Y), fe51_as_canonical_nat(&self_point.X)),
            fe51_as_canonical_nat(&other.Y_minus_X),
        ),
        tt2d_val == field_mul(
            fe51_as_canonical_nat(&self_point.T),
            fe51_as_canonical_nat(&other.T2d),
        ),
        zz_val == field_mul(fe51_as_canonical_nat(&self_point.Z), fe51_as_canonical_nat(&other.Z)),
        fe51_as_canonical_nat(&result.X) == field_sub(pp_val, mm_val),
        fe51_as_canonical_nat(&result.Y) == field_add(pp_val, mm_val),
        fe51_as_canonical_nat(&result.Z) == field_add(field_add(zz_val, zz_val), tt2d_val),
        fe51_as_canonical_nat(&result.T) == field_sub(field_add(zz_val, zz_val), tt2d_val),
    ensures
        is_valid_completed_point(result),
        completed_point_as_affine_edwards(result) == spec_edwards_add_projective_niels(
            self_point,
            other,
        ),
{
    let sX = fe51_as_canonical_nat(&self_point.X);
    let sY = fe51_as_canonical_nat(&self_point.Y);
    let sZ = fe51_as_canonical_nat(&self_point.Z);
    let sT = fe51_as_canonical_nat(&self_point.T);
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    p_gt_2();

    assert(sZ != 0);
    assert(sZ % p() != 0) by {
        lemma_field_element_reduced(sZ);
    };

    // Extract witness from is_valid_projective_niels_point
    let ep = choose|ep: crate::edwards::EdwardsPoint|
        is_valid_edwards_point(ep) && #[trigger] projective_niels_corresponds_to_edwards(other, ep);
    let X2 = fe51_as_canonical_nat(&ep.X);
    let Y2 = fe51_as_canonical_nat(&ep.Y);
    let Z2 = fe51_as_canonical_nat(&ep.Z);
    let T2 = fe51_as_canonical_nat(&ep.T);

    assert(Z2 != 0);  // from is_valid_edwards_point(ep)
    assert(Z2 % p() != 0) by {
        lemma_field_element_reduced(Z2);
    };

    assert(field_mul(sX, sY) == field_mul(sZ, sT));
    assert(field_mul(X2, Y2) == field_mul(Z2, T2));

    // Niels correspondence
    assert(fe51_as_canonical_nat(&other.Y_plus_X) == field_add(Y2, X2)) by {
        reveal(projective_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.Y_minus_X) == field_sub(Y2, X2)) by {
        reveal(projective_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.Z) == Z2) by {
        reveal(projective_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.T2d) == field_mul(field_mul(2, d), T2)) by {
        reveal(projective_niels_corresponds_to_edwards);
    };

    // Affine coordinates
    let x1 = field_mul(sX, field_inv(sZ));
    let y1 = field_mul(sY, field_inv(sZ));
    let x2 = field_mul(X2, field_inv(Z2));
    let y2 = field_mul(Y2, field_inv(Z2));

    assert(math_on_edwards_curve(x1, y1)) by {
        axiom_valid_extended_point_affine_on_curve(sX, sY, sZ, sT);
    };
    assert(math_on_edwards_curve(x2, y2)) by {
        axiom_valid_extended_point_affine_on_curve(X2, Y2, Z2, T2);
    };

    // STEP 1: FOIL on PP and MM
    let result_x = field_sub(pp_val, mm_val);
    let result_y = field_add(pp_val, mm_val);
    assert(result_x == field_mul(2, field_add(field_mul(sY, X2), field_mul(sX, Y2)))) by {
        lemma_pp_minus_mm(sY, sX, Y2, X2);
    };
    assert(result_y == field_mul(2, field_add(field_mul(sY, Y2), field_mul(sX, X2)))) by {
        lemma_pp_plus_mm(sY, sX, Y2, X2);
    };

    // STEP 2: Factor z1z2 = mul(sZ, Z2) from projective products
    let z1z2 = field_mul(sZ, Z2);

    assert(field_mul(sY, X2) == field_mul(field_mul(y1, x2), z1z2)) by {
        lemma_four_factor_rearrange(y1, sZ, x2, Z2);
        lemma_div_mul_cancel(sY, sZ);
        lemma_div_mul_cancel(X2, Z2);
        lemma_field_element_reduced(sY);
        lemma_field_element_reduced(X2);
    };

    assert(field_mul(sX, Y2) == field_mul(field_mul(x1, y2), z1z2)) by {
        lemma_four_factor_rearrange(x1, sZ, y2, Z2);
        lemma_div_mul_cancel(sX, sZ);
        lemma_div_mul_cancel(Y2, Z2);
        lemma_field_element_reduced(sX);
        lemma_field_element_reduced(Y2);
    };

    assert(field_mul(sY, Y2) == field_mul(field_mul(y1, y2), z1z2)) by {
        lemma_four_factor_rearrange(y1, sZ, y2, Z2);
        lemma_div_mul_cancel(sY, sZ);
        lemma_div_mul_cancel(Y2, Z2);
        lemma_field_element_reduced(sY);
        lemma_field_element_reduced(Y2);
    };

    assert(field_mul(sX, X2) == field_mul(field_mul(x1, x2), z1z2)) by {
        lemma_four_factor_rearrange(x1, sZ, x2, Z2);
        lemma_div_mul_cancel(sX, sZ);
        lemma_div_mul_cancel(X2, Z2);
        lemma_field_element_reduced(sX);
        lemma_field_element_reduced(X2);
    };

    let y1x2 = field_mul(y1, x2);
    let x1y2 = field_mul(x1, y2);
    let y1y2 = field_mul(y1, y2);
    let x1x2 = field_mul(x1, x2);

    assert(field_add(field_mul(sY, X2), field_mul(sX, Y2)) == field_mul(
        z1z2,
        field_add(y1x2, x1y2),
    )) by {
        lemma_reverse_distribute_add(y1x2, x1y2, z1z2);
        lemma_field_mul_comm(field_add(y1x2, x1y2), z1z2);
    };

    assert(field_add(field_mul(sY, Y2), field_mul(sX, X2)) == field_mul(
        z1z2,
        field_add(y1y2, x1x2),
    )) by {
        lemma_reverse_distribute_add(y1y2, x1x2, z1z2);
        lemma_field_mul_comm(field_add(y1y2, x1x2), z1z2);
    };

    let num_x = field_add(y1x2, x1y2);
    let num_y = field_add(y1y2, x1x2);

    // STEP 3: TT2d expansion via Segre invariant (sZ·sT = sX·sY)
    let x1y1 = field_mul(x1, y1);
    let x2y2 = field_mul(x2, y2);

    assert(field_mul(sX, sY) == field_mul(x1y1, field_mul(sZ, sZ))) by {
        lemma_four_factor_rearrange(x1, sZ, y1, sZ);
        lemma_div_mul_cancel(sX, sZ);
        lemma_div_mul_cancel(sY, sZ);
        lemma_field_element_reduced(sX);
        lemma_field_element_reduced(sY);
    };

    assert(sT == field_mul(x1y1, sZ) % p()) by {
        lemma_field_mul_assoc(x1y1, sZ, sZ);
        lemma_field_mul_comm(field_mul(x1y1, sZ), sZ);
        lemma_field_mul_left_cancel(sZ, sT, field_mul(x1y1, sZ));
        lemma_field_element_reduced(sT);
    };
    assert(field_mul(X2, Y2) == field_mul(x2y2, field_mul(Z2, Z2))) by {
        lemma_four_factor_rearrange(x2, Z2, y2, Z2);
        lemma_div_mul_cancel(X2, Z2);
        lemma_div_mul_cancel(Y2, Z2);
        lemma_field_element_reduced(X2);
        lemma_field_element_reduced(Y2);
    };

    assert(T2 == field_mul(x2y2, Z2) % p()) by {
        lemma_field_mul_assoc(x2y2, Z2, Z2);
        lemma_field_mul_comm(field_mul(x2y2, Z2), Z2);
        lemma_field_mul_left_cancel(Z2, T2, field_mul(x2y2, Z2));
        lemma_field_element_reduced(T2);
    };

    assert(field_mul(sT, T2) == field_mul(field_mul(x1y1, x2y2), z1z2)) by {
        lemma_field_element_reduced(sT);
        lemma_field_element_reduced(T2);
        lemma_mul_mod_noop_right(sT as int, T2 as int, p() as int);
        lemma_mul_mod_noop_left(sT as int, T2 as int, p() as int);
        lemma_mul_mod_noop_left((field_mul(x1y1, sZ)) as int, T2 as int, p() as int);
        lemma_mul_mod_noop_right(
            (field_mul(x1y1, sZ)) as int,
            (field_mul(x2y2, Z2)) as int,
            p() as int,
        );
        lemma_four_factor_rearrange(x1y1, sZ, x2y2, Z2);
    };

    let t = field_mul(d, field_mul(x1x2, y1y2));

    assert(field_mul(x1y1, x2y2) == field_mul(x1x2, y1y2)) by {
        lemma_four_factor_rearrange(x1, y1, x2, y2);
    };

    assert(tt2d_val == field_mul(field_mul(sT, T2), field_mul(2, d))) by {
        lemma_field_mul_comm(field_mul(2, d), T2);
        lemma_field_mul_assoc(sT, T2, field_mul(2, d));
    };

    let x1x2y1y2 = field_mul(x1x2, y1y2);
    assert(field_mul(field_mul(x1x2y1y2, z1z2), field_mul(2, d)) == field_mul(
        z1z2,
        field_mul(x1x2y1y2, field_mul(2, d)),
    )) by {
        lemma_field_mul_comm(x1x2y1y2, z1z2);
        lemma_field_mul_assoc(z1z2, x1x2y1y2, field_mul(2, d));
    };

    assert(field_mul(x1x2y1y2, field_mul(2, d)) == field_mul(2, t)) by {
        lemma_field_mul_comm(x1x2y1y2, field_mul(2, d));
        lemma_field_mul_assoc(2, d, x1x2y1y2);
    };

    assert(tt2d_val == field_mul(z1z2, field_mul(2, t)));

    // STEP 4: Denominator factoring
    let zz2 = field_add(zz_val, zz_val);
    assert(zz2 == field_mul(2, z1z2)) by {
        lemma_add_self_eq_double(zz_val);
    };

    let result_z = field_add(zz2, tt2d_val);
    let result_t = field_sub(zz2, tt2d_val);

    assert(field_mul(2, z1z2) == field_mul(z1z2, 2)) by {
        lemma_field_mul_comm(2nat, z1z2);
    };

    assert(result_z == field_mul(z1z2, field_add(2, field_mul(2, t)))) by {
        lemma_reverse_distribute_add(2nat, field_mul(2, t), z1z2);
        lemma_field_mul_comm(field_add(2, field_mul(2, t)), z1z2);
    };

    assert(field_add(2nat, field_mul(2, t)) == field_mul(2, field_add(1, t))) by {
        lemma_field_mul_distributes_over_add(2, 1, t);
        lemma_field_mul_one_right(2nat);
        lemma_small_mod(2nat, p());
    };
    assert(result_z == field_mul(z1z2, field_mul(2, field_add(1, t))));

    assert(result_t == field_mul(z1z2, field_sub(2nat, field_mul(2, t)))) by {
        lemma_reverse_distribute_sub(2nat, field_mul(2, t), z1z2);
        lemma_field_mul_comm(field_sub(2nat, field_mul(2, t)), z1z2);
    };

    assert(field_sub(2nat, field_mul(2, t)) == field_mul(2, field_sub(1, t))) by {
        lemma_field_mul_comm(2nat, field_sub(1, t));
        lemma_field_mul_distributes_over_sub_right(1, t, 2);
        lemma_field_mul_one_left(2nat);
        lemma_small_mod(2nat, p());
        lemma_field_mul_comm(t, 2nat);
    };
    assert(result_t == field_mul(z1z2, field_mul(2, field_sub(1, t))));

    assert(result_x == field_mul(z1z2, field_mul(2, num_x))) by {
        lemma_field_mul_assoc(2, z1z2, num_x);
        lemma_field_mul_comm(2nat, z1z2);
        lemma_field_mul_assoc(z1z2, 2, num_x);
    };

    assert(result_y == field_mul(z1z2, field_mul(2, num_y))) by {
        lemma_field_mul_assoc(2, z1z2, num_y);
        lemma_field_mul_comm(2nat, z1z2);
        lemma_field_mul_assoc(z1z2, 2, num_y);
    };

    // STEP 5: Factor cancellation to get affine ratios
    let aff_rx = field_mul(2, field_add(x1y2, y1x2));
    let aff_ry = field_mul(2, field_add(y1y2, x1x2));
    let aff_rz = field_mul(2, field_add(1, t));
    let aff_rt = field_mul(2, field_sub(1, t));

    assert(num_x == field_add(x1y2, y1x2)) by {
        let pp = p();
        lemma_add_mod_noop(y1x2 as int, x1y2 as int, pp as int);
        lemma_add_mod_noop(x1y2 as int, y1x2 as int, pp as int);
    };

    assert(result_x == field_mul(z1z2, aff_rx));
    assert(result_y == field_mul(z1z2, aff_ry));
    assert(result_z == field_mul(z1z2, aff_rz));
    assert(result_t == field_mul(z1z2, aff_rt));

    lemma_completed_point_ratios(x1, y1, x2, y2, aff_rx, aff_ry, aff_rz, aff_rt);

    assert(z1z2 != 0) by {
        lemma_field_element_reduced(sZ);
        lemma_field_element_reduced(Z2);
        lemma_nonzero_product(sZ, Z2);
    };
    assert(z1z2 % p() != 0) by {
        lemma_mod_bound((sZ * Z2) as int, p() as int);
        lemma_field_element_reduced(z1z2);
    };

    // Cancel z1z2 from X/Z ratio
    assert(aff_rz % p() != 0) by {
        lemma_field_element_reduced(aff_rz);
    };
    lemma_cancel_common_factor(aff_rx, aff_rz, z1z2);
    lemma_field_mul_comm(z1z2, aff_rx);
    lemma_field_mul_comm(z1z2, aff_rz);

    // Cancel z1z2 from Y/T ratio
    assert(aff_rt % p() != 0) by {
        lemma_field_element_reduced(aff_rt);
    };
    lemma_cancel_common_factor(aff_ry, aff_rt, z1z2);
    lemma_field_mul_comm(z1z2, aff_ry);
    lemma_field_mul_comm(z1z2, aff_rt);

    assert(result_z != 0) by {
        lemma_nonzero_product(aff_rz, z1z2);
    };
    assert(result_t != 0) by {
        lemma_nonzero_product(aff_rt, z1z2);
    };

    // STEP 6: Connect to spec_edwards_add_projective_niels
    lemma_projective_niels_affine_equals_edwards_affine(other, ep);
}

/// Exec bridge: EdwardsPoint - ProjectiveNielsPoint -> valid CompletedPoint.
/// Derivable from add variant: subtraction swaps Y_plus_X/Y_minus_X (negating x2)
/// and swaps Z/T (reflecting sign change in 1 +/- d*x1*x2*y1*y2).
pub proof fn lemma_sub_projective_niels_completed_valid(
    self_point: crate::edwards::EdwardsPoint,
    other: crate::backend::serial::curve_models::ProjectiveNielsPoint,
    result: crate::backend::serial::curve_models::CompletedPoint,
    pm_val: nat,
    mp_val: nat,
    tt2d_val: nat,
    zz_val: nat,
)
    requires
        is_well_formed_edwards_point(self_point),
        is_valid_edwards_point(self_point),
        is_valid_projective_niels_point(other),
        pm_val == field_mul(
            field_add(fe51_as_canonical_nat(&self_point.Y), fe51_as_canonical_nat(&self_point.X)),
            fe51_as_canonical_nat(&other.Y_minus_X),
        ),
        mp_val == field_mul(
            field_sub(fe51_as_canonical_nat(&self_point.Y), fe51_as_canonical_nat(&self_point.X)),
            fe51_as_canonical_nat(&other.Y_plus_X),
        ),
        tt2d_val == field_mul(
            fe51_as_canonical_nat(&self_point.T),
            fe51_as_canonical_nat(&other.T2d),
        ),
        zz_val == field_mul(fe51_as_canonical_nat(&self_point.Z), fe51_as_canonical_nat(&other.Z)),
        fe51_as_canonical_nat(&result.X) == field_sub(pm_val, mp_val),
        fe51_as_canonical_nat(&result.Y) == field_add(pm_val, mp_val),
        fe51_as_canonical_nat(&result.Z) == field_sub(field_add(zz_val, zz_val), tt2d_val),
        fe51_as_canonical_nat(&result.T) == field_add(field_add(zz_val, zz_val), tt2d_val),
    ensures
        is_valid_completed_point(result),
        completed_point_as_affine_edwards(result) == spec_edwards_sub_projective_niels(
            self_point,
            other,
        ),
{
    let sX = fe51_as_canonical_nat(&self_point.X);
    let sY = fe51_as_canonical_nat(&self_point.Y);
    let sZ = fe51_as_canonical_nat(&self_point.Z);
    let sT = fe51_as_canonical_nat(&self_point.T);
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    p_gt_2();

    assert(sZ != 0);
    assert(sZ % p() != 0) by {
        lemma_field_element_reduced(sZ);
    };

    // Extract witness from is_valid_projective_niels_point
    let ep = choose|ep: crate::edwards::EdwardsPoint|
        is_valid_edwards_point(ep) && #[trigger] projective_niels_corresponds_to_edwards(other, ep);
    let X2 = fe51_as_canonical_nat(&ep.X);
    let Y2 = fe51_as_canonical_nat(&ep.Y);
    let Z2 = fe51_as_canonical_nat(&ep.Z);
    let T2 = fe51_as_canonical_nat(&ep.T);

    assert(Z2 != 0);
    assert(Z2 % p() != 0) by {
        lemma_field_element_reduced(Z2);
    };

    assert(field_mul(sX, sY) == field_mul(sZ, sT));
    assert(field_mul(X2, Y2) == field_mul(Z2, T2));

    // Niels correspondence
    assert(fe51_as_canonical_nat(&other.Y_plus_X) == field_add(Y2, X2)) by {
        reveal(projective_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.Y_minus_X) == field_sub(Y2, X2)) by {
        reveal(projective_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.Z) == Z2) by {
        reveal(projective_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.T2d) == field_mul(field_mul(2, d), T2)) by {
        reveal(projective_niels_corresponds_to_edwards);
    };

    // Affine coordinates
    let x1 = field_mul(sX, field_inv(sZ));
    let y1 = field_mul(sY, field_inv(sZ));
    let x2 = field_mul(X2, field_inv(Z2));
    let y2 = field_mul(Y2, field_inv(Z2));

    assert(math_on_edwards_curve(x1, y1)) by {
        axiom_valid_extended_point_affine_on_curve(sX, sY, sZ, sT);
    };
    assert(math_on_edwards_curve(x2, y2)) by {
        axiom_valid_extended_point_affine_on_curve(X2, Y2, Z2, T2);
    };

    // STEP 1: Mixed FOIL on PM and MP
    let result_x = field_sub(pm_val, mp_val);
    let result_y = field_add(pm_val, mp_val);

    assert(result_x == field_mul(2, field_sub(field_mul(sX, Y2), field_mul(sY, X2)))) by {
        lemma_pm_minus_mp(sY, sX, Y2, X2);
    };
    assert(result_y == field_mul(2, field_sub(field_mul(sY, Y2), field_mul(sX, X2)))) by {
        lemma_pm_plus_mp(sY, sX, Y2, X2);
    };

    // STEP 2: Factor z1z2 = mul(sZ, Z2) from projective products
    let z1z2 = field_mul(sZ, Z2);

    assert(field_mul(sY, X2) == field_mul(field_mul(y1, x2), z1z2)) by {
        lemma_four_factor_rearrange(y1, sZ, x2, Z2);
        lemma_div_mul_cancel(sY, sZ);
        lemma_div_mul_cancel(X2, Z2);
        lemma_field_element_reduced(sY);
        lemma_field_element_reduced(X2);
    };

    assert(field_mul(sX, Y2) == field_mul(field_mul(x1, y2), z1z2)) by {
        lemma_four_factor_rearrange(x1, sZ, y2, Z2);
        lemma_div_mul_cancel(sX, sZ);
        lemma_div_mul_cancel(Y2, Z2);
        lemma_field_element_reduced(sX);
        lemma_field_element_reduced(Y2);
    };

    assert(field_mul(sY, Y2) == field_mul(field_mul(y1, y2), z1z2)) by {
        lemma_four_factor_rearrange(y1, sZ, y2, Z2);
        lemma_div_mul_cancel(sY, sZ);
        lemma_div_mul_cancel(Y2, Z2);
        lemma_field_element_reduced(sY);
        lemma_field_element_reduced(Y2);
    };

    assert(field_mul(sX, X2) == field_mul(field_mul(x1, x2), z1z2)) by {
        lemma_four_factor_rearrange(x1, sZ, x2, Z2);
        lemma_div_mul_cancel(sX, sZ);
        lemma_div_mul_cancel(X2, Z2);
        lemma_field_element_reduced(sX);
        lemma_field_element_reduced(X2);
    };

    let y1x2 = field_mul(y1, x2);
    let x1y2 = field_mul(x1, y2);
    let y1y2 = field_mul(y1, y2);
    let x1x2 = field_mul(x1, x2);

    assert(field_sub(field_mul(sX, Y2), field_mul(sY, X2)) == field_mul(
        z1z2,
        field_sub(x1y2, y1x2),
    )) by {
        lemma_reverse_distribute_sub(x1y2, y1x2, z1z2);
        lemma_field_mul_comm(field_sub(x1y2, y1x2), z1z2);
    };

    assert(field_sub(field_mul(sY, Y2), field_mul(sX, X2)) == field_mul(
        z1z2,
        field_sub(y1y2, x1x2),
    )) by {
        lemma_reverse_distribute_sub(y1y2, x1x2, z1z2);
        lemma_field_mul_comm(field_sub(y1y2, x1x2), z1z2);
    };

    let num_x = field_sub(x1y2, y1x2);
    let num_y = field_sub(y1y2, x1x2);

    // STEP 3: TT2d expansion via Segre invariant
    let x1y1 = field_mul(x1, y1);
    let x2y2 = field_mul(x2, y2);

    assert(field_mul(sX, sY) == field_mul(x1y1, field_mul(sZ, sZ))) by {
        lemma_four_factor_rearrange(x1, sZ, y1, sZ);
        lemma_div_mul_cancel(sX, sZ);
        lemma_div_mul_cancel(sY, sZ);
        lemma_field_element_reduced(sX);
        lemma_field_element_reduced(sY);
    };

    assert(sT == field_mul(x1y1, sZ) % p()) by {
        lemma_field_mul_assoc(x1y1, sZ, sZ);
        lemma_field_mul_comm(field_mul(x1y1, sZ), sZ);
        lemma_field_mul_left_cancel(sZ, sT, field_mul(x1y1, sZ));
        lemma_field_element_reduced(sT);
    };

    assert(field_mul(X2, Y2) == field_mul(x2y2, field_mul(Z2, Z2))) by {
        lemma_four_factor_rearrange(x2, Z2, y2, Z2);
        lemma_div_mul_cancel(X2, Z2);
        lemma_div_mul_cancel(Y2, Z2);
        lemma_field_element_reduced(X2);
        lemma_field_element_reduced(Y2);
    };

    assert(T2 == field_mul(x2y2, Z2) % p()) by {
        lemma_field_mul_assoc(x2y2, Z2, Z2);
        lemma_field_mul_comm(field_mul(x2y2, Z2), Z2);
        lemma_field_mul_left_cancel(Z2, T2, field_mul(x2y2, Z2));
        lemma_field_element_reduced(T2);
    };

    assert(field_mul(sT, T2) == field_mul(field_mul(x1y1, x2y2), z1z2)) by {
        lemma_field_element_reduced(sT);
        lemma_field_element_reduced(T2);
        lemma_mul_mod_noop_right(sT as int, T2 as int, p() as int);
        lemma_mul_mod_noop_left(sT as int, T2 as int, p() as int);
        lemma_mul_mod_noop_left((field_mul(x1y1, sZ)) as int, T2 as int, p() as int);
        lemma_mul_mod_noop_right(
            (field_mul(x1y1, sZ)) as int,
            (field_mul(x2y2, Z2)) as int,
            p() as int,
        );
        lemma_four_factor_rearrange(x1y1, sZ, x2y2, Z2);
    };

    let t = field_mul(d, field_mul(x1x2, y1y2));

    assert(field_mul(x1y1, x2y2) == field_mul(x1x2, y1y2)) by {
        lemma_four_factor_rearrange(x1, y1, x2, y2);
    };

    assert(tt2d_val == field_mul(field_mul(sT, T2), field_mul(2, d))) by {
        lemma_field_mul_comm(field_mul(2, d), T2);
        lemma_field_mul_assoc(sT, T2, field_mul(2, d));
    };

    let x1x2y1y2 = field_mul(x1x2, y1y2);
    assert(field_mul(field_mul(x1x2y1y2, z1z2), field_mul(2, d)) == field_mul(
        z1z2,
        field_mul(x1x2y1y2, field_mul(2, d)),
    )) by {
        lemma_field_mul_comm(x1x2y1y2, z1z2);
        lemma_field_mul_assoc(z1z2, x1x2y1y2, field_mul(2, d));
    };

    assert(field_mul(x1x2y1y2, field_mul(2, d)) == field_mul(2, t)) by {
        lemma_field_mul_comm(x1x2y1y2, field_mul(2, d));
        lemma_field_mul_assoc(2, d, x1x2y1y2);
    };

    assert(tt2d_val == field_mul(z1z2, field_mul(2, t)));

    // STEP 4: Denominator factoring (Z/T swapped from add)
    let zz2 = field_add(zz_val, zz_val);
    assert(zz2 == field_mul(2, z1z2)) by {
        lemma_add_self_eq_double(zz_val);
    };

    let result_z = field_sub(zz2, tt2d_val);
    let result_t = field_add(zz2, tt2d_val);

    assert(field_mul(2, z1z2) == field_mul(z1z2, 2)) by {
        lemma_field_mul_comm(2nat, z1z2);
    };

    assert(result_z == field_mul(z1z2, field_sub(2nat, field_mul(2, t)))) by {
        lemma_reverse_distribute_sub(2nat, field_mul(2, t), z1z2);
        lemma_field_mul_comm(field_sub(2nat, field_mul(2, t)), z1z2);
    };

    assert(field_sub(2nat, field_mul(2, t)) == field_mul(2, field_sub(1, t))) by {
        lemma_field_mul_comm(2nat, field_sub(1, t));
        lemma_field_mul_distributes_over_sub_right(1, t, 2);
        lemma_field_mul_one_left(2nat);
        lemma_small_mod(2nat, p());
        lemma_field_mul_comm(t, 2nat);
    };
    assert(result_z == field_mul(z1z2, field_mul(2, field_sub(1, t))));

    assert(result_t == field_mul(z1z2, field_add(2nat, field_mul(2, t)))) by {
        lemma_reverse_distribute_add(2nat, field_mul(2, t), z1z2);
        lemma_field_mul_comm(field_add(2nat, field_mul(2, t)), z1z2);
    };

    assert(field_add(2nat, field_mul(2, t)) == field_mul(2, field_add(1, t))) by {
        lemma_field_mul_distributes_over_add(2, 1, t);
        lemma_field_mul_one_right(2nat);
        lemma_small_mod(2nat, p());
    };
    assert(result_t == field_mul(z1z2, field_mul(2, field_add(1, t))));

    assert(result_x == field_mul(z1z2, field_mul(2, num_x))) by {
        lemma_field_mul_assoc(2, z1z2, num_x);
        lemma_field_mul_comm(2nat, z1z2);
        lemma_field_mul_assoc(z1z2, 2, num_x);
    };

    assert(result_y == field_mul(z1z2, field_mul(2, num_y))) by {
        lemma_field_mul_assoc(2, z1z2, num_y);
        lemma_field_mul_comm(2nat, z1z2);
        lemma_field_mul_assoc(z1z2, 2, num_y);
    };

    // STEP 5: Connect to edwards_sub via neg(x2)
    let neg_x2 = field_neg(x2);
    lemma_negation_preserves_curve(x2, y2);

    // sub(x1y2, y1x2) = add(x1y2, neg(y1x2)) = add(x1y2, y1*neg(x2))
    lemma_field_mul_neg(y1, x2);
    lemma_field_sub_eq_add_neg(x1y2, y1x2);

    // sub(y1y2, x1x2) = add(y1y2, neg(x1x2)) = add(y1y2, x1*neg(x2))
    lemma_field_mul_neg(x1, x2);
    lemma_field_sub_eq_add_neg(y1y2, x1x2);

    // t' = mul(d, mul(x1*neg(x2), y1*y2)) = neg(t)
    lemma_field_mul_comm(field_neg(x1x2), y1y2);
    lemma_field_mul_neg(y1y2, x1x2);
    lemma_field_mul_comm(y1y2, x1x2);
    lemma_field_mul_neg(d, field_mul(x1x2, y1y2));

    let t_prime = field_mul(d, field_mul(field_mul(x1, neg_x2), field_mul(y1, y2)));
    assert(t_prime == field_neg(t));

    // sub(1, t) = add(1, t'), sub(1, t') = add(1, t)
    lemma_field_sub_eq_add_neg(1nat, t);
    lemma_field_sub_eq_add_neg(1nat, t_prime);
    lemma_neg_neg(t);
    assert(field_sub(1nat, t_prime) == field_add(1nat, t)) by {
        let p = p();
        lemma_add_mod_noop(1nat as int, (t % p) as int, p as int);
        lemma_add_mod_noop(1nat as int, t as int, p as int);
        lemma_mod_twice(t as int, p as int);
    };

    let aff_rx = field_mul(2, field_add(field_mul(x1, y2), field_mul(y1, neg_x2)));
    let aff_ry = field_mul(2, field_add(field_mul(y1, y2), field_mul(x1, neg_x2)));
    let aff_rz = field_mul(2, field_add(1, t_prime));
    let aff_rt = field_mul(2, field_sub(1, t_prime));

    assert(aff_rx == field_mul(2, num_x));
    assert(aff_ry == field_mul(2, num_y));
    assert(aff_rz == field_mul(2, field_sub(1, t)));
    assert(aff_rt == field_mul(2, field_add(1, t)));

    assert(result_x == field_mul(z1z2, aff_rx));
    assert(result_y == field_mul(z1z2, aff_ry));
    assert(result_z == field_mul(z1z2, aff_rz));
    assert(result_t == field_mul(z1z2, aff_rt));

    lemma_completed_point_ratios(x1, y1, neg_x2, y2, aff_rx, aff_ry, aff_rz, aff_rt);

    // STEP 6: Factor cancellation
    assert(z1z2 != 0) by {
        lemma_field_element_reduced(sZ);
        lemma_field_element_reduced(Z2);
        lemma_nonzero_product(sZ, Z2);
    };
    assert(z1z2 % p() != 0) by {
        lemma_mod_bound((sZ * Z2) as int, p() as int);
        lemma_field_element_reduced(z1z2);
    };

    // Cancel z1z2 from X/Z ratio
    assert(aff_rz % p() != 0) by {
        lemma_field_element_reduced(aff_rz);
    };
    lemma_cancel_common_factor(aff_rx, aff_rz, z1z2);
    lemma_field_mul_comm(z1z2, aff_rx);
    lemma_field_mul_comm(z1z2, aff_rz);

    // Cancel z1z2 from Y/T ratio
    assert(aff_rt % p() != 0) by {
        lemma_field_element_reduced(aff_rt);
    };
    lemma_cancel_common_factor(aff_ry, aff_rt, z1z2);
    lemma_field_mul_comm(z1z2, aff_ry);
    lemma_field_mul_comm(z1z2, aff_rt);

    assert(result_z != 0) by {
        lemma_nonzero_product(aff_rz, z1z2);
    };
    assert(result_t != 0) by {
        lemma_nonzero_product(aff_rt, z1z2);
    };

    // STEP 7: Connect to spec_edwards_sub_projective_niels
    lemma_projective_niels_affine_equals_edwards_affine(other, ep);
}

/// Exec bridge: EdwardsPoint + AffineNielsPoint -> valid CompletedPoint.
/// Same structure as ProjectiveNiels but uses Z2 = 2*Z1 (affine Niels has Z=1).
pub proof fn lemma_add_affine_niels_completed_valid(
    self_point: crate::edwards::EdwardsPoint,
    other: crate::backend::serial::curve_models::AffineNielsPoint,
    result: crate::backend::serial::curve_models::CompletedPoint,
    pp_val: nat,
    mm_val: nat,
    txy2d_val: nat,
    z2_val: nat,
)
    requires
        is_well_formed_edwards_point(self_point),
        is_valid_edwards_point(self_point),
        is_valid_affine_niels_point(other),
        pp_val == field_mul(
            field_add(fe51_as_canonical_nat(&self_point.Y), fe51_as_canonical_nat(&self_point.X)),
            fe51_as_canonical_nat(&other.y_plus_x),
        ),
        mm_val == field_mul(
            field_sub(fe51_as_canonical_nat(&self_point.Y), fe51_as_canonical_nat(&self_point.X)),
            fe51_as_canonical_nat(&other.y_minus_x),
        ),
        txy2d_val == field_mul(
            fe51_as_canonical_nat(&self_point.T),
            fe51_as_canonical_nat(&other.xy2d),
        ),
        z2_val == field_add(
            fe51_as_canonical_nat(&self_point.Z),
            fe51_as_canonical_nat(&self_point.Z),
        ),
        fe51_as_canonical_nat(&result.X) == field_sub(pp_val, mm_val),
        fe51_as_canonical_nat(&result.Y) == field_add(pp_val, mm_val),
        fe51_as_canonical_nat(&result.Z) == field_add(z2_val, txy2d_val),
        fe51_as_canonical_nat(&result.T) == field_sub(z2_val, txy2d_val),
    ensures
        is_valid_completed_point(result),
        completed_point_as_affine_edwards(result) == spec_edwards_add_affine_niels(
            self_point,
            other,
        ),
{
    let sX = fe51_as_canonical_nat(&self_point.X);
    let sY = fe51_as_canonical_nat(&self_point.Y);
    let sZ = fe51_as_canonical_nat(&self_point.Z);
    let sT = fe51_as_canonical_nat(&self_point.T);
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    p_gt_2();

    assert(sZ != 0);
    assert(sZ % p() != 0) by {
        lemma_field_element_reduced(sZ);
    };

    // Extract witness from is_valid_affine_niels_point
    let ep = choose|ep: crate::edwards::EdwardsPoint|
        is_valid_edwards_point(ep) && #[trigger] affine_niels_corresponds_to_edwards(other, ep);
    let X2 = fe51_as_canonical_nat(&ep.X);
    let Y2 = fe51_as_canonical_nat(&ep.Y);
    let Z2 = fe51_as_canonical_nat(&ep.Z);

    let z2_inv = field_inv(Z2);
    let x2 = field_mul(X2, z2_inv);
    let y2 = field_mul(Y2, z2_inv);

    let x1 = field_mul(sX, field_inv(sZ));
    let y1 = field_mul(sY, field_inv(sZ));

    assert(math_on_edwards_curve(x1, y1)) by {
        axiom_valid_extended_point_affine_on_curve(sX, sY, sZ, sT);
    };
    assert(math_on_edwards_curve(x2, y2)) by {
        axiom_valid_extended_point_affine_on_curve(X2, Y2, Z2, fe51_as_canonical_nat(&ep.T));
    };

    // Niels correspondence
    assert(fe51_as_canonical_nat(&other.y_plus_x) == field_add(y2, x2)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.y_minus_x) == field_sub(y2, x2)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.xy2d) == field_mul(field_mul(field_mul(x2, y2), 2), d)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };

    // STEP 1: FOIL on PP and MM
    let result_x = field_sub(pp_val, mm_val);
    let result_y = field_add(pp_val, mm_val);

    assert(result_x == field_mul(2, field_add(field_mul(sY, x2), field_mul(sX, y2)))) by {
        lemma_pp_minus_mm(sY, sX, y2, x2);
    };
    assert(result_y == field_mul(2, field_add(field_mul(sY, y2), field_mul(sX, x2)))) by {
        lemma_pp_plus_mm(sY, sX, y2, x2);
    };

    // STEP 2: Factor sZ from projective*affine products
    assert(field_mul(sY, x2) == field_mul(field_mul(y1, x2), sZ)) by {
        lemma_div_mul_cancel(sY, sZ);
        lemma_field_element_reduced(sY);
        lemma_field_mul_assoc(y1, sZ, x2);
        lemma_field_mul_comm(sZ, x2);
        lemma_field_mul_assoc(y1, x2, sZ);
    };

    assert(field_mul(sX, y2) == field_mul(field_mul(x1, y2), sZ)) by {
        lemma_div_mul_cancel(sX, sZ);
        lemma_field_element_reduced(sX);
        lemma_field_mul_assoc(x1, sZ, y2);
        lemma_field_mul_comm(sZ, y2);
        lemma_field_mul_assoc(x1, y2, sZ);
    };

    assert(field_mul(sY, y2) == field_mul(field_mul(y1, y2), sZ)) by {
        lemma_div_mul_cancel(sY, sZ);
        lemma_field_element_reduced(sY);
        lemma_field_mul_assoc(y1, sZ, y2);
        lemma_field_mul_comm(sZ, y2);
        lemma_field_mul_assoc(y1, y2, sZ);
    };

    assert(field_mul(sX, x2) == field_mul(field_mul(x1, x2), sZ)) by {
        lemma_div_mul_cancel(sX, sZ);
        lemma_field_element_reduced(sX);
        lemma_field_mul_assoc(x1, sZ, x2);
        lemma_field_mul_comm(sZ, x2);
        lemma_field_mul_assoc(x1, x2, sZ);
    };

    let y1x2 = field_mul(y1, x2);
    let x1y2 = field_mul(x1, y2);
    let y1y2 = field_mul(y1, y2);
    let x1x2 = field_mul(x1, x2);

    assert(field_add(field_mul(sY, x2), field_mul(sX, y2)) == field_mul(sZ, field_add(y1x2, x1y2)))
        by {
        lemma_reverse_distribute_add(y1x2, x1y2, sZ);
        lemma_field_mul_comm(field_add(y1x2, x1y2), sZ);
    };

    assert(field_add(field_mul(sY, y2), field_mul(sX, x2)) == field_mul(sZ, field_add(y1y2, x1x2)))
        by {
        lemma_reverse_distribute_add(y1y2, x1x2, sZ);
        lemma_field_mul_comm(field_add(y1y2, x1x2), sZ);
    };

    let num_x = field_add(y1x2, x1y2);
    let num_y = field_add(y1y2, x1x2);

    assert(result_x == field_mul(sZ, field_mul(2, num_x))) by {
        lemma_field_mul_assoc(2, sZ, num_x);
        lemma_field_mul_comm(2nat, sZ);
        lemma_field_mul_assoc(sZ, 2, num_x);
    };

    assert(result_y == field_mul(sZ, field_mul(2, num_y))) by {
        lemma_field_mul_assoc(2, sZ, num_y);
        lemma_field_mul_comm(2nat, sZ);
        lemma_field_mul_assoc(sZ, 2, num_y);
    };

    // STEP 3: Txy2d expansion via Segre invariant
    let x1y1 = field_mul(x1, y1);
    let x2y2 = field_mul(x2, y2);

    assert(field_mul(sX, sY) == field_mul(x1y1, field_mul(sZ, sZ))) by {
        lemma_four_factor_rearrange(x1, sZ, y1, sZ);
        lemma_div_mul_cancel(sX, sZ);
        lemma_div_mul_cancel(sY, sZ);
        lemma_field_element_reduced(sX);
        lemma_field_element_reduced(sY);
    };

    assert(sT == field_mul(x1y1, sZ) % p()) by {
        lemma_field_mul_assoc(x1y1, sZ, sZ);
        lemma_field_mul_comm(field_mul(x1y1, sZ), sZ);
        lemma_field_mul_left_cancel(sZ, sT, field_mul(x1y1, sZ));
        lemma_field_element_reduced(sT);
    };

    let xy2d_spec = field_mul(field_mul(x2y2, 2), d);

    assert(field_mul(sT, xy2d_spec) == field_mul(field_mul(x1y1, sZ), xy2d_spec)) by {
        lemma_field_element_reduced(sT);
        lemma_mul_mod_noop_left(sT as int, xy2d_spec as int, p() as int);
        lemma_mul_mod_noop_left((field_mul(x1y1, sZ)) as int, xy2d_spec as int, p() as int);
    };

    assert(xy2d_spec == field_mul(x2y2, field_mul(2, d))) by {
        lemma_field_mul_assoc(x2y2, 2, d);
    };

    assert(field_mul(field_mul(x1y1, sZ), field_mul(x2y2, field_mul(2, d))) == field_mul(
        field_mul(x1y1, x2y2),
        field_mul(sZ, field_mul(2, d)),
    )) by {
        lemma_four_factor_rearrange(x1y1, sZ, x2y2, field_mul(2, d));
    };

    assert(field_mul(x1y1, x2y2) == field_mul(x1x2, y1y2)) by {
        lemma_four_factor_rearrange(x1, y1, x2, y2);
    };

    let t = field_mul(d, field_mul(x1x2, y1y2));
    let x1x2y1y2 = field_mul(x1x2, y1y2);

    assert(field_mul(x1x2y1y2, field_mul(sZ, field_mul(2, d))) == field_mul(
        sZ,
        field_mul(x1x2y1y2, field_mul(2, d)),
    )) by {
        lemma_field_mul_assoc(x1x2y1y2, sZ, field_mul(2, d));
        lemma_field_mul_comm(x1x2y1y2, sZ);
        lemma_field_mul_assoc(sZ, x1x2y1y2, field_mul(2, d));
    };

    assert(field_mul(x1x2y1y2, field_mul(2, d)) == field_mul(2, t)) by {
        lemma_field_mul_comm(x1x2y1y2, field_mul(2, d));
        lemma_field_mul_assoc(2, d, x1x2y1y2);
    };

    assert(txy2d_val == field_mul(sZ, field_mul(2, t)));

    // STEP 4: Denominator factoring
    assert(z2_val == field_mul(2, sZ)) by {
        lemma_add_self_eq_double(sZ);
    };

    let result_z = field_add(z2_val, txy2d_val);
    let result_t = field_sub(z2_val, txy2d_val);

    assert(field_mul(2, sZ) == field_mul(sZ, 2)) by {
        lemma_field_mul_comm(2nat, sZ);
    };

    assert(result_z == field_mul(sZ, field_add(2nat, field_mul(2, t)))) by {
        lemma_reverse_distribute_add(2nat, field_mul(2, t), sZ);
        lemma_field_mul_comm(field_add(2nat, field_mul(2, t)), sZ);
    };

    assert(field_add(2nat, field_mul(2, t)) == field_mul(2, field_add(1, t))) by {
        lemma_field_mul_distributes_over_add(2, 1, t);
        lemma_field_mul_one_right(2nat);
        lemma_small_mod(2nat, p());
    };
    assert(result_z == field_mul(sZ, field_mul(2, field_add(1, t))));

    assert(result_t == field_mul(sZ, field_sub(2nat, field_mul(2, t)))) by {
        lemma_reverse_distribute_sub(2nat, field_mul(2, t), sZ);
        lemma_field_mul_comm(field_sub(2nat, field_mul(2, t)), sZ);
    };

    assert(field_sub(2nat, field_mul(2, t)) == field_mul(2, field_sub(1, t))) by {
        lemma_field_mul_comm(2nat, field_sub(1, t));
        lemma_field_mul_distributes_over_sub_right(1, t, 2);
        lemma_field_mul_one_left(2nat);
        lemma_small_mod(2nat, p());
        lemma_field_mul_comm(t, 2nat);
    };
    assert(result_t == field_mul(sZ, field_mul(2, field_sub(1, t))));

    // STEP 5: Factor cancellation
    let aff_rx = field_mul(2, field_add(x1y2, y1x2));
    let aff_ry = field_mul(2, field_add(y1y2, x1x2));
    let aff_rz = field_mul(2, field_add(1, t));
    let aff_rt = field_mul(2, field_sub(1, t));

    assert(num_x == field_add(x1y2, y1x2)) by {
        let pp = p();
        lemma_add_mod_noop(y1x2 as int, x1y2 as int, pp as int);
        lemma_add_mod_noop(x1y2 as int, y1x2 as int, pp as int);
    };

    assert(result_x == field_mul(sZ, aff_rx));
    assert(result_y == field_mul(sZ, aff_ry));
    assert(result_z == field_mul(sZ, aff_rz));
    assert(result_t == field_mul(sZ, aff_rt));

    lemma_completed_point_ratios(x1, y1, x2, y2, aff_rx, aff_ry, aff_rz, aff_rt);

    // Cancel sZ from X/Z ratio
    assert(aff_rz % p() != 0) by {
        lemma_field_element_reduced(aff_rz);
    };
    lemma_cancel_common_factor(aff_rx, aff_rz, sZ);
    lemma_field_mul_comm(sZ, aff_rx);
    lemma_field_mul_comm(sZ, aff_rz);

    // Cancel sZ from Y/T ratio
    assert(aff_rt % p() != 0) by {
        lemma_field_element_reduced(aff_rt);
    };
    lemma_cancel_common_factor(aff_ry, aff_rt, sZ);
    lemma_field_mul_comm(sZ, aff_ry);
    lemma_field_mul_comm(sZ, aff_rt);

    assert(result_z != 0) by {
        lemma_nonzero_product(aff_rz, sZ);
    };
    assert(result_t != 0) by {
        lemma_nonzero_product(aff_rt, sZ);
    };

    // STEP 6: Connect to spec_edwards_add_affine_niels
    lemma_affine_niels_affine_equals_edwards_affine(other, ep);
}

/// Exec bridge: EdwardsPoint - AffineNielsPoint -> valid CompletedPoint.
/// Derivable from add variant via edwards_sub = edwards_add with negated point.
pub proof fn lemma_sub_affine_niels_completed_valid(
    self_point: crate::edwards::EdwardsPoint,
    other: crate::backend::serial::curve_models::AffineNielsPoint,
    result: crate::backend::serial::curve_models::CompletedPoint,
    pm_val: nat,
    mp_val: nat,
    txy2d_val: nat,
    z2_val: nat,
)
    requires
        is_well_formed_edwards_point(self_point),
        is_valid_edwards_point(self_point),
        is_valid_affine_niels_point(other),
        pm_val == field_mul(
            field_add(fe51_as_canonical_nat(&self_point.Y), fe51_as_canonical_nat(&self_point.X)),
            fe51_as_canonical_nat(&other.y_minus_x),
        ),
        mp_val == field_mul(
            field_sub(fe51_as_canonical_nat(&self_point.Y), fe51_as_canonical_nat(&self_point.X)),
            fe51_as_canonical_nat(&other.y_plus_x),
        ),
        txy2d_val == field_mul(
            fe51_as_canonical_nat(&self_point.T),
            fe51_as_canonical_nat(&other.xy2d),
        ),
        z2_val == field_add(
            fe51_as_canonical_nat(&self_point.Z),
            fe51_as_canonical_nat(&self_point.Z),
        ),
        fe51_as_canonical_nat(&result.X) == field_sub(pm_val, mp_val),
        fe51_as_canonical_nat(&result.Y) == field_add(pm_val, mp_val),
        fe51_as_canonical_nat(&result.Z) == field_sub(z2_val, txy2d_val),
        fe51_as_canonical_nat(&result.T) == field_add(z2_val, txy2d_val),
    ensures
        is_valid_completed_point(result),
        completed_point_as_affine_edwards(result) == spec_edwards_sub_affine_niels(
            self_point,
            other,
        ),
{
    let sX = fe51_as_canonical_nat(&self_point.X);
    let sY = fe51_as_canonical_nat(&self_point.Y);
    let sZ = fe51_as_canonical_nat(&self_point.Z);
    let sT = fe51_as_canonical_nat(&self_point.T);
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    p_gt_2();

    assert(sZ != 0);
    assert(sZ % p() != 0) by {
        lemma_field_element_reduced(sZ);
    };

    let ep = choose|ep: crate::edwards::EdwardsPoint|
        is_valid_edwards_point(ep) && #[trigger] affine_niels_corresponds_to_edwards(other, ep);
    let X2 = fe51_as_canonical_nat(&ep.X);
    let Y2 = fe51_as_canonical_nat(&ep.Y);
    let Z2 = fe51_as_canonical_nat(&ep.Z);

    let z2_inv = field_inv(Z2);
    let x2 = field_mul(X2, z2_inv);
    let y2 = field_mul(Y2, z2_inv);

    let x1 = field_mul(sX, field_inv(sZ));
    let y1 = field_mul(sY, field_inv(sZ));

    assert(math_on_edwards_curve(x1, y1)) by {
        axiom_valid_extended_point_affine_on_curve(sX, sY, sZ, sT);
    };
    assert(math_on_edwards_curve(x2, y2)) by {
        axiom_valid_extended_point_affine_on_curve(X2, Y2, Z2, fe51_as_canonical_nat(&ep.T));
    };

    // Niels correspondence
    assert(fe51_as_canonical_nat(&other.y_plus_x) == field_add(y2, x2)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.y_minus_x) == field_sub(y2, x2)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.xy2d) == field_mul(field_mul(field_mul(x2, y2), 2), d)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };

    // STEP 1: Mixed FOIL
    let result_x = field_sub(pm_val, mp_val);
    let result_y = field_add(pm_val, mp_val);

    assert(result_x == field_mul(2, field_sub(field_mul(sX, y2), field_mul(sY, x2)))) by {
        lemma_pm_minus_mp(sY, sX, y2, x2);
    };
    assert(result_y == field_mul(2, field_sub(field_mul(sY, y2), field_mul(sX, x2)))) by {
        lemma_pm_plus_mp(sY, sX, y2, x2);
    };

    // STEP 2: Factor sZ
    assert(field_mul(sY, x2) == field_mul(field_mul(y1, x2), sZ)) by {
        lemma_div_mul_cancel(sY, sZ);
        lemma_field_element_reduced(sY);
        lemma_field_mul_assoc(y1, sZ, x2);
        lemma_field_mul_comm(sZ, x2);
        lemma_field_mul_assoc(y1, x2, sZ);
    };

    assert(field_mul(sX, y2) == field_mul(field_mul(x1, y2), sZ)) by {
        lemma_div_mul_cancel(sX, sZ);
        lemma_field_element_reduced(sX);
        lemma_field_mul_assoc(x1, sZ, y2);
        lemma_field_mul_comm(sZ, y2);
        lemma_field_mul_assoc(x1, y2, sZ);
    };

    assert(field_mul(sY, y2) == field_mul(field_mul(y1, y2), sZ)) by {
        lemma_div_mul_cancel(sY, sZ);
        lemma_field_element_reduced(sY);
        lemma_field_mul_assoc(y1, sZ, y2);
        lemma_field_mul_comm(sZ, y2);
        lemma_field_mul_assoc(y1, y2, sZ);
    };

    assert(field_mul(sX, x2) == field_mul(field_mul(x1, x2), sZ)) by {
        lemma_div_mul_cancel(sX, sZ);
        lemma_field_element_reduced(sX);
        lemma_field_mul_assoc(x1, sZ, x2);
        lemma_field_mul_comm(sZ, x2);
        lemma_field_mul_assoc(x1, x2, sZ);
    };

    let y1x2 = field_mul(y1, x2);
    let x1y2 = field_mul(x1, y2);
    let y1y2 = field_mul(y1, y2);
    let x1x2 = field_mul(x1, x2);

    assert(field_sub(field_mul(sX, y2), field_mul(sY, x2)) == field_mul(sZ, field_sub(x1y2, y1x2)))
        by {
        lemma_reverse_distribute_sub(x1y2, y1x2, sZ);
        lemma_field_mul_comm(field_sub(x1y2, y1x2), sZ);
    };

    assert(field_sub(field_mul(sY, y2), field_mul(sX, x2)) == field_mul(sZ, field_sub(y1y2, x1x2)))
        by {
        lemma_reverse_distribute_sub(y1y2, x1x2, sZ);
        lemma_field_mul_comm(field_sub(y1y2, x1x2), sZ);
    };

    let num_x = field_sub(x1y2, y1x2);
    let num_y = field_sub(y1y2, x1x2);

    assert(result_x == field_mul(sZ, field_mul(2, num_x))) by {
        lemma_field_mul_assoc(2, sZ, num_x);
        lemma_field_mul_comm(2nat, sZ);
        lemma_field_mul_assoc(sZ, 2, num_x);
    };

    assert(result_y == field_mul(sZ, field_mul(2, num_y))) by {
        lemma_field_mul_assoc(2, sZ, num_y);
        lemma_field_mul_comm(2nat, sZ);
        lemma_field_mul_assoc(sZ, 2, num_y);
    };

    // STEP 3: Txy2d expansion via Segre invariant
    let x1y1 = field_mul(x1, y1);
    let x2y2 = field_mul(x2, y2);

    assert(field_mul(sX, sY) == field_mul(x1y1, field_mul(sZ, sZ))) by {
        lemma_four_factor_rearrange(x1, sZ, y1, sZ);
        lemma_div_mul_cancel(sX, sZ);
        lemma_div_mul_cancel(sY, sZ);
        lemma_field_element_reduced(sX);
        lemma_field_element_reduced(sY);
    };

    assert(sT == field_mul(x1y1, sZ) % p()) by {
        lemma_field_mul_assoc(x1y1, sZ, sZ);
        lemma_field_mul_comm(field_mul(x1y1, sZ), sZ);
        lemma_field_mul_left_cancel(sZ, sT, field_mul(x1y1, sZ));
        lemma_field_element_reduced(sT);
    };

    let xy2d_spec = field_mul(field_mul(x2y2, 2), d);

    assert(field_mul(sT, xy2d_spec) == field_mul(field_mul(x1y1, sZ), xy2d_spec)) by {
        lemma_field_element_reduced(sT);
        lemma_mul_mod_noop_left(sT as int, xy2d_spec as int, p() as int);
        lemma_mul_mod_noop_left((field_mul(x1y1, sZ)) as int, xy2d_spec as int, p() as int);
    };

    assert(xy2d_spec == field_mul(x2y2, field_mul(2, d))) by {
        lemma_field_mul_assoc(x2y2, 2, d);
    };

    assert(field_mul(field_mul(x1y1, sZ), field_mul(x2y2, field_mul(2, d))) == field_mul(
        field_mul(x1y1, x2y2),
        field_mul(sZ, field_mul(2, d)),
    )) by {
        lemma_four_factor_rearrange(x1y1, sZ, x2y2, field_mul(2, d));
    };

    assert(field_mul(x1y1, x2y2) == field_mul(x1x2, y1y2)) by {
        lemma_four_factor_rearrange(x1, y1, x2, y2);
    };

    let t = field_mul(d, field_mul(x1x2, y1y2));
    let x1x2y1y2 = field_mul(x1x2, y1y2);

    assert(field_mul(x1x2y1y2, field_mul(sZ, field_mul(2, d))) == field_mul(
        sZ,
        field_mul(x1x2y1y2, field_mul(2, d)),
    )) by {
        lemma_field_mul_assoc(x1x2y1y2, sZ, field_mul(2, d));
        lemma_field_mul_comm(x1x2y1y2, sZ);
        lemma_field_mul_assoc(sZ, x1x2y1y2, field_mul(2, d));
    };

    assert(field_mul(x1x2y1y2, field_mul(2, d)) == field_mul(2, t)) by {
        lemma_field_mul_comm(x1x2y1y2, field_mul(2, d));
        lemma_field_mul_assoc(2, d, x1x2y1y2);
    };

    assert(txy2d_val == field_mul(sZ, field_mul(2, t)));

    // STEP 4: Denominator factoring (Z/T swapped from add)
    assert(z2_val == field_mul(2, sZ)) by {
        lemma_add_self_eq_double(sZ);
    };

    let result_z = field_sub(z2_val, txy2d_val);
    let result_t = field_add(z2_val, txy2d_val);

    assert(field_mul(2, sZ) == field_mul(sZ, 2)) by {
        lemma_field_mul_comm(2nat, sZ);
    };

    assert(result_z == field_mul(sZ, field_sub(2nat, field_mul(2, t)))) by {
        lemma_reverse_distribute_sub(2nat, field_mul(2, t), sZ);
        lemma_field_mul_comm(field_sub(2nat, field_mul(2, t)), sZ);
    };

    assert(field_sub(2nat, field_mul(2, t)) == field_mul(2, field_sub(1, t))) by {
        lemma_field_mul_comm(2nat, field_sub(1, t));
        lemma_field_mul_distributes_over_sub_right(1, t, 2);
        lemma_field_mul_one_left(2nat);
        lemma_small_mod(2nat, p());
        lemma_field_mul_comm(t, 2nat);
    };
    assert(result_z == field_mul(sZ, field_mul(2, field_sub(1, t))));

    assert(result_t == field_mul(sZ, field_add(2nat, field_mul(2, t)))) by {
        lemma_reverse_distribute_add(2nat, field_mul(2, t), sZ);
        lemma_field_mul_comm(field_add(2nat, field_mul(2, t)), sZ);
    };

    assert(field_add(2nat, field_mul(2, t)) == field_mul(2, field_add(1, t))) by {
        lemma_field_mul_distributes_over_add(2, 1, t);
        lemma_field_mul_one_right(2nat);
        lemma_small_mod(2nat, p());
    };
    assert(result_t == field_mul(sZ, field_mul(2, field_add(1, t))));

    // STEP 5: Connect to edwards_sub via neg(x2)
    let neg_x2 = field_neg(x2);
    lemma_negation_preserves_curve(x2, y2);

    // sub(x1y2, y1x2) = add(x1y2, neg(y1x2)) = add(x1y2, y1*neg(x2))
    lemma_field_mul_neg(y1, x2);
    lemma_field_sub_eq_add_neg(x1y2, y1x2);

    // sub(y1y2, x1x2) = add(y1y2, neg(x1x2)) = add(y1y2, x1*neg(x2))
    lemma_field_mul_neg(x1, x2);
    lemma_field_sub_eq_add_neg(y1y2, x1x2);

    // t' = mul(d, mul(x1*neg(x2), y1*y2)) = neg(t)
    lemma_field_mul_comm(field_neg(x1x2), y1y2);
    lemma_field_mul_neg(y1y2, x1x2);
    lemma_field_mul_comm(y1y2, x1x2);
    lemma_field_mul_neg(d, field_mul(x1x2, y1y2));

    let t_prime = field_mul(d, field_mul(field_mul(x1, neg_x2), field_mul(y1, y2)));
    assert(t_prime == field_neg(t));

    // sub(1, t) = add(1, t'), sub(1, t') = add(1, t)
    lemma_field_sub_eq_add_neg(1nat, t);
    lemma_field_sub_eq_add_neg(1nat, t_prime);
    lemma_neg_neg(t);
    assert(field_sub(1nat, t_prime) == field_add(1nat, t)) by {
        let p = p();
        lemma_add_mod_noop(1nat as int, (t % p) as int, p as int);
        lemma_add_mod_noop(1nat as int, t as int, p as int);
        lemma_mod_twice(t as int, p as int);
    };

    let aff_rx = field_mul(2, field_add(field_mul(x1, y2), field_mul(y1, neg_x2)));
    let aff_ry = field_mul(2, field_add(field_mul(y1, y2), field_mul(x1, neg_x2)));
    let aff_rz = field_mul(2, field_add(1, t_prime));
    let aff_rt = field_mul(2, field_sub(1, t_prime));

    assert(aff_rx == field_mul(2, num_x));
    assert(aff_ry == field_mul(2, num_y));
    assert(aff_rz == field_mul(2, field_sub(1, t)));
    assert(aff_rt == field_mul(2, field_add(1, t)));

    assert(result_x == field_mul(sZ, aff_rx));
    assert(result_y == field_mul(sZ, aff_ry));
    assert(result_z == field_mul(sZ, aff_rz));
    assert(result_t == field_mul(sZ, aff_rt));

    lemma_completed_point_ratios(x1, y1, neg_x2, y2, aff_rx, aff_ry, aff_rz, aff_rt);

    // STEP 6: Factor cancellation
    assert(aff_rz % p() != 0) by {
        lemma_field_element_reduced(aff_rz);
    };
    lemma_cancel_common_factor(aff_rx, aff_rz, sZ);
    lemma_field_mul_comm(sZ, aff_rx);
    lemma_field_mul_comm(sZ, aff_rz);

    assert(aff_rt % p() != 0) by {
        lemma_field_element_reduced(aff_rt);
    };
    lemma_cancel_common_factor(aff_ry, aff_rt, sZ);
    lemma_field_mul_comm(sZ, aff_ry);
    lemma_field_mul_comm(sZ, aff_rt);

    assert(result_z != 0) by {
        lemma_nonzero_product(aff_rz, sZ);
    };
    assert(result_t != 0) by {
        lemma_nonzero_product(aff_rt, sZ);
    };

    // STEP 7: Connect to spec_edwards_sub_affine_niels
    lemma_affine_niels_affine_equals_edwards_affine(other, ep);
}

} // verus!
