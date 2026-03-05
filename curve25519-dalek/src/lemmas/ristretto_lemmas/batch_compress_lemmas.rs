#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::axioms::axiom_invsqrt_a_minus_d;
#[allow(unused_imports)]
use crate::backend::serial::u64::constants as u64_constants;
#[allow(unused_imports)]
use crate::constants;
#[allow(unused_imports)]
use crate::edwards::EdwardsPoint;
#[allow(unused_imports)]
use crate::field::FieldElement;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::number_theory_lemmas::{lemma_euclid_prime, lemma_p_is_odd};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::lemma_projective_implies_affine_on_curve;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::niels_addition_correctness::lemma_projective_product_factor;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::constants_lemmas::{
    lemma_d_plus_one_nonzero, lemma_sqrt_ad_minus_one_nonzero,
};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::lemma_field_mul_zero_left;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::lemma_field_mul_zero_right;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::lemma_nonzero_product;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::{
    lemma_a_times_inv_ab_is_inv_b, lemma_add_self_eq_double, lemma_cancel_common_factor,
    lemma_div_mul_cancel, lemma_factor_result_component_add, lemma_factor_result_component_sub,
    lemma_field_add_add_recover_double, lemma_field_add_assoc, lemma_field_add_comm,
    lemma_field_add_sub_cancel, lemma_field_add_sub_recover_double, lemma_field_diff_of_squares,
    lemma_field_element_reduced, lemma_field_mul_assoc, lemma_field_mul_comm,
    lemma_field_mul_distributes_over_add, lemma_field_mul_distributes_over_sub_right,
    lemma_field_mul_exchange, lemma_field_mul_left_cancel, lemma_field_mul_neg,
    lemma_field_mul_one_left, lemma_field_mul_one_right, lemma_field_neg_mul_left,
    lemma_field_neg_neg, lemma_field_neg_nonzero, lemma_field_sub_add_cancel,
    lemma_field_sub_antisymmetric, lemma_field_sub_eq_add_neg, lemma_field_sub_self,
    lemma_four_factor_rearrange, lemma_inv_mul_cancel, lemma_inv_of_product,
    lemma_neg_a_times_inv_ab, lemma_neg_one_times_is_neg, lemma_neg_square_eq,
    lemma_product_of_squares_eq_square_of_product, lemma_quotient_of_squares,
    lemma_reassociate_2_z_num, lemma_reverse_distribute_sub, lemma_sub_neg_eq_add,
    lemma_swap_sub_negates_mul,
};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::sqrt_m1_lemmas::axiom_sqrt_m1_squared;
#[allow(unused_imports)]
use crate::specs::core_specs::*;
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::primality_specs::{axiom_p_is_prime, is_prime};
#[allow(unused_imports)]
use crate::specs::ristretto_specs::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::{
    lemma_mod_bound, lemma_mul_mod_noop_left, lemma_mul_mod_noop_right, lemma_small_mod,
};
use vstd::prelude::*;

verus! {

/// Helper: z % p() != 0 implies field_square(z) % p() != 0.
pub proof fn lemma_field_square_nonzero(z: nat)
    requires
        z < p(),
        z % p() != 0,
    ensures
        field_square(z) % p() != 0,
{
    assert(z != 0) by {
        lemma_field_element_reduced(z);
    };
    assert(field_square(z) != 0) by {
        p_gt_2();
        lemma_nonzero_product(z, z);
    };
    assert(field_square(z) % p() == field_square(z)) by {
        lemma_field_element_reduced(field_square(z));
    };
}

/// Helper: from the Segre relation Z·T = X·Y and Z ≠ 0,
/// derive T = ab·Z where a = X/Z, b = Y/Z, ab = a·b.
pub proof fn lemma_segre_derives_t(x: nat, y: nat, z: nat, t: nat)
    requires
        x < p(),
        y < p(),
        z < p(),
        t < p(),
        z % p() != 0,
        field_mul(z, t) == field_mul(x, y),
    ensures
        ({
            let inv_z = field_inv(z);
            let ab = field_mul(field_mul(x, inv_z), field_mul(y, inv_z));
            t == field_mul(ab, z)
        }),
{
    let inv_z = field_inv(z);
    let a = field_mul(x, inv_z);
    let b = field_mul(y, inv_z);
    let ab = field_mul(a, b);
    let z2 = field_square(z);

    assert(field_mul(x, y) == field_mul(ab, z2)) by {
        lemma_projective_product_factor(x, z, y, z);
    };
    assert(field_mul(ab, z2) == field_mul(field_mul(ab, z), z)) by {
        lemma_field_mul_assoc(ab, z, z);
    };
    assert(field_mul(field_mul(ab, z), z) == field_mul(z, field_mul(ab, z))) by {
        lemma_field_mul_comm(field_mul(ab, z), z);
    };
    assert(t % p() == field_mul(ab, z) % p()) by {
        lemma_field_mul_left_cancel(z, t, field_mul(ab, z));
    };
    assert(t == field_mul(ab, z)) by {
        lemma_field_element_reduced(t);
        lemma_field_element_reduced(field_mul(ab, z));
    };
}

/// Helper: given T = ab·Z, factor d·T² through Z² as d·(a²·b²)·Z².
pub proof fn lemma_dt_squared_factor(d: nat, a: nat, b: nat, z: nat, t: nat)
    requires
        t == field_mul(field_mul(a, b), z),
    ensures
        ({
            let z2 = field_square(z);
            let t_dab2 = field_mul(d, field_mul(field_square(a), field_square(b)));
            field_mul(d, field_square(t)) == field_mul(t_dab2, z2)
        }),
{
    let ab = field_mul(a, b);
    let z2 = field_square(z);
    let t_dab2 = field_mul(d, field_mul(field_square(a), field_square(b)));

    assert(field_square(t) == field_mul(field_square(ab), z2)) by {
        lemma_four_factor_rearrange(ab, z, ab, z);
    };
    assert(field_square(ab) == field_mul(field_square(a), field_square(b))) by {
        lemma_four_factor_rearrange(a, b, a, b);
    };
    assert(field_mul(d, field_square(t)) == field_mul(t_dab2, z2)) by {
        lemma_field_mul_assoc(d, field_mul(field_square(a), field_square(b)), z2);
    };
}

/// Lemma: the doubled affine point equals the batch state quotients (e/f, g/h).
///
/// Given an extended Edwards point (X:Y:Z:T) with Segre relation Z·T = X·Y and Z ≠ 0,
/// and batch state fields e = 2XY, f = Z²+dT², g = Y²+X², h = Z²−dT²,
/// the doubled affine point equals (e/f, g/h).
///
/// Proof outline (mirrors lemma_double_projective_completed_valid):
///   1. Factor e, g through Z² using lemma_projective_product_factor
///   2. Derive T = ab·Z from Segre, factor f, h through Z²
///   3. Cancel Z² from e/f and g/h using lemma_cancel_common_factor
///   4. Match to edwards_add(a, b, a, b) where a = X/Z, b = Y/Z
pub proof fn lemma_doubled_affine_from_batch_state(
    x: nat,
    y: nat,
    z: nat,
    t: nat,
    e: nat,
    f: nat,
    g: nat,
    h: nat,
)
    requires
        x < p(),
        y < p(),
        z < p(),
        t < p(),
        z % p() != 0,
        field_mul(z, t) == field_mul(x, y),
        ({
            let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
            e == field_mul(2, field_mul(x, y)) && f == field_add(
                field_square(z),
                field_mul(d, field_square(t)),
            ) && g == field_add(field_square(y), field_square(x)) && h == field_sub(
                field_square(z),
                field_mul(d, field_square(t)),
            )
        }),
    ensures
        edwards_double(field_mul(x, field_inv(z)), field_mul(y, field_inv(z))) == (
            field_mul(e, field_inv(f)),
            field_mul(g, field_inv(h)),
        ),
{
    let p = p();
    assert(p > 2) by {
        p_gt_2();
    };

    let inv_z = field_inv(z);
    let a = field_mul(x, inv_z);
    let b = field_mul(y, inv_z);
    let ab = field_mul(a, b);
    let a2 = field_square(a);
    let b2 = field_square(b);
    let z2 = field_square(z);
    let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
    let t_dab2 = field_mul(d, field_mul(a2, b2));

    assert(z2 % p != 0) by {
        lemma_field_square_nonzero(z);
    };

    assert(field_mul(x, y) == field_mul(ab, z2)) by {
        lemma_projective_product_factor(x, z, y, z);
    };
    assert(field_mul(1nat, z2) == z2) by {
        lemma_field_mul_one_left(z2);
        lemma_field_element_reduced(z2);
    };

    // Factor e through Z²: e = Z²·(2·ab)
    assert(e == field_mul(z2, field_mul(2, ab))) by {
        lemma_reassociate_2_z_num(z2, ab);
    };

    // Factor g through Z²: g = Z²·(b²+a²)
    assert(g == field_mul(z2, field_add(b2, a2))) by {
        assert(field_square(x) == field_mul(a2, z2)) by {
            lemma_projective_product_factor(x, z, x, z);
        };
        assert(field_square(y) == field_mul(b2, z2)) by {
            lemma_projective_product_factor(y, z, y, z);
        };
        lemma_factor_result_component_add(b2, a2, z2);
    };

    // Derive T = ab·Z from Segre relation
    assert(t == field_mul(ab, z)) by {
        lemma_segre_derives_t(x, y, z, t);
    };

    // Factor d·T² through Z²: d·T² = t_dab2·Z²
    assert(field_mul(d, field_square(t)) == field_mul(t_dab2, z2)) by {
        lemma_dt_squared_factor(d, a, b, z, t);
    };

    // f = Z² + d·T² = Z²·(1 + d·a²b²)
    assert(f == field_mul(z2, field_add(1nat, t_dab2))) by {
        lemma_factor_result_component_add(1nat, t_dab2, z2);
    };

    // h = Z² − d·T² = Z²·(1 − d·a²b²)
    assert(h == field_mul(z2, field_sub(1nat, t_dab2))) by {
        lemma_factor_result_component_sub(1nat, t_dab2, z2);
    };

    // Cancel Z² from e/f and g/h
    if field_add(1nat, t_dab2) % p != 0 {
        assert(field_mul(e, field_inv(f)) == field_mul(
            field_mul(2, ab),
            field_inv(field_add(1nat, t_dab2)),
        )) by {
            lemma_cancel_common_factor(field_mul(2, ab), field_add(1nat, t_dab2), z2);
        };
    } else {
        assert(field_mul(e, field_inv(f)) == 0) by {
            assert(f == 0) by {
                assert(field_add(1nat, t_dab2) == 0) by {
                    lemma_field_element_reduced(field_add(1nat, t_dab2));
                };
                lemma_field_mul_zero_right(z2, field_add(1nat, t_dab2));
            };
            assert(field_inv(f) == 0) by {
                field_inv_zero();
            };
            lemma_field_mul_zero_right(e, field_inv(f));
        };
        assert(field_mul(field_mul(2, ab), field_inv(field_add(1nat, t_dab2))) == 0) by {
            assert(field_inv(field_add(1nat, t_dab2)) == 0) by {
                field_inv_zero();
            };
            lemma_field_mul_zero_right(field_mul(2, ab), field_inv(field_add(1nat, t_dab2)));
        };
    }
    // g/h = Z²·(b²+a²) / Z²·(1−t_dab2) = (b²+a²)/(1−t_dab2)   [or both 0]
    assert(g == field_mul(field_add(b2, a2), z2)) by {
        lemma_field_mul_comm(z2, field_add(b2, a2));
    };
    assert(h == field_mul(field_sub(1nat, t_dab2), z2)) by {
        lemma_field_mul_comm(z2, field_sub(1nat, t_dab2));
    };
    if field_sub(1nat, t_dab2) % p != 0 {
        assert(field_mul(g, field_inv(h)) == field_mul(
            field_add(b2, a2),
            field_inv(field_sub(1nat, t_dab2)),
        )) by {
            lemma_cancel_common_factor(field_add(b2, a2), field_sub(1nat, t_dab2), z2);
        };
    } else {
        assert(field_mul(g, field_inv(h)) == 0) by {
            assert(h == 0) by {
                assert(field_sub(1nat, t_dab2) == 0) by {
                    lemma_field_element_reduced(field_sub(1nat, t_dab2));
                };
                lemma_field_mul_zero_right(z2, field_sub(1nat, t_dab2));
            };
            assert(field_inv(h) == 0) by {
                field_inv_zero();
            };
            lemma_field_mul_zero_right(g, field_inv(h));
        };
        assert(field_mul(field_add(b2, a2), field_inv(field_sub(1nat, t_dab2))) == 0) by {
            assert(field_inv(field_sub(1nat, t_dab2)) == 0) by {
                field_inv_zero();
            };
            lemma_field_mul_zero_right(field_add(b2, a2), field_inv(field_sub(1nat, t_dab2)));
        };
    }

    // STEP 5: Match (e/f, g/h) to edwards_add(a, b, a, b) = edwards_double(a, b)
    assert(field_mul(b, a) == ab) by {
        lemma_field_mul_comm(b, a);
    };
    assert(field_add(ab, ab) == field_mul(2, ab)) by {
        lemma_add_self_eq_double(ab);
    };
}

/// Lemma: the batch identity h² − g² = −e²(1+d) holds for projective intermediates.
///
/// Given (X:Y:Z:T) on the Edwards curve with Segre relation Z·T = X·Y,
/// and projective intermediates e = 2XY, g = Y²+X², h = Z²−dT²:
///
///     h² − g² = −e² · (1 + d)
///
/// Proof: derives affine intermediates (a=X/Z, b=Y/Z), calls
/// `lemma_curve_eq_batch_identity(a, b)` for the affine identity,
/// then scales by Z⁴ using factoring through Z².
pub proof fn lemma_batch_identity_projective(x: nat, y: nat, z: nat, t: nat, e: nat, g: nat, h: nat)
    requires
        x < p(),
        y < p(),
        z < p(),
        t < p(),
        z % p() != 0,
        field_mul(z, t) == field_mul(x, y),
        is_on_edwards_curve_projective(x, y, z),
        ({
            let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
            e == field_mul(2, field_mul(x, y)) && g == field_add(field_square(y), field_square(x))
                && h == field_sub(field_square(z), field_mul(d, field_square(t)))
        }),
    ensures
        ({
            let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
            field_sub(field_square(h), field_square(g)) == field_neg(
                field_mul(field_square(e), field_add(d, 1)),
            )
        }),
{
    let pn = p();
    assert(pn > 2) by {
        p_gt_2();
    };
    let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
    let inv_z = field_inv(z);
    let a = field_mul(x, inv_z);
    let b = field_mul(y, inv_z);
    let z2 = field_square(z);
    let ab = field_mul(a, b);

    assert(is_on_edwards_curve(a, b)) by {
        lemma_projective_implies_affine_on_curve(x, y, z);
    };

    // Affine intermediates
    let e_aff = field_mul(2, ab);
    let g_aff = field_add(field_square(b), field_square(a));
    let h_aff = field_sub(1nat, field_mul(d, field_mul(field_square(a), field_square(b))));

    // Affine identity: h_aff² − g_aff² = −e_aff²·(1+d)
    assert(field_sub(field_square(h_aff), field_square(g_aff)) == field_neg(
        field_mul(field_square(e_aff), field_add(d, 1)),
    )) by {
        lemma_curve_eq_batch_identity(a, b);
    };

    // Z² ≠ 0
    assert(z2 % pn != 0) by {
        lemma_field_square_nonzero(z);
    };

    // e = Z² · e_aff
    assert(e == field_mul(z2, e_aff)) by {
        assert(field_mul(x, y) == field_mul(ab, z2)) by {
            lemma_projective_product_factor(x, z, y, z);
        };
        assert(field_mul(z2, e_aff) == field_mul(z2, field_mul(2, ab)));
        lemma_reassociate_2_z_num(z2, ab);
    };

    // g = Z² · g_aff
    assert(g == field_mul(z2, g_aff)) by {
        assert(field_square(x) == field_mul(field_square(a), z2)) by {
            lemma_projective_product_factor(x, z, x, z);
            lemma_four_factor_rearrange(a, z, a, z);
        };
        assert(field_square(y) == field_mul(field_square(b), z2)) by {
            lemma_projective_product_factor(y, z, y, z);
            lemma_four_factor_rearrange(b, z, b, z);
        };
        lemma_factor_result_component_add(field_square(b), field_square(a), z2);
    };

    // Derive T = ab·Z from Segre
    assert(t == field_mul(ab, z)) by {
        lemma_segre_derives_t(x, y, z, t);
    };

    // Factor d·T² through Z²
    let t_dab2 = field_mul(d, field_mul(field_square(a), field_square(b)));
    assert(field_mul(d, field_square(t)) == field_mul(t_dab2, z2)) by {
        lemma_dt_squared_factor(d, a, b, z, t);
    };

    // h = Z² · h_aff
    assert(h == field_mul(z2, h_aff)) by {
        lemma_field_mul_one_left(z2);
        lemma_field_element_reduced(z2);
        lemma_factor_result_component_sub(1nat, t_dab2, z2);
    };

    // Now scale the affine identity by Z⁴:
    // h² = (Z² · h_aff)² = Z⁴ · h_aff²
    // g² = (Z² · g_aff)² = Z⁴ · g_aff²
    let z4 = field_square(z2);
    assert(field_square(h) == field_mul(z4, field_square(h_aff))) by {
        lemma_four_factor_rearrange(z2, h_aff, z2, h_aff);
    };
    assert(field_square(g) == field_mul(z4, field_square(g_aff))) by {
        lemma_four_factor_rearrange(z2, g_aff, z2, g_aff);
    };

    // h² - g² = Z⁴·h_aff² - Z⁴·g_aff² = Z⁴·(h_aff² - g_aff²)
    assert(field_sub(field_square(h), field_square(g)) == field_mul(
        z4,
        field_sub(field_square(h_aff), field_square(g_aff)),
    )) by {
        lemma_field_mul_comm(z4, field_square(h_aff));
        lemma_field_mul_comm(z4, field_square(g_aff));
        lemma_factor_result_component_sub(field_square(h_aff), field_square(g_aff), z4);
    };

    // Substitute affine identity: h_aff² - g_aff² = -e_aff²·(1+d)
    // So h² - g² = Z⁴ · (-e_aff²·(1+d)) = -(Z⁴·e_aff²)·(1+d)
    assert(field_mul(z4, field_neg(field_mul(field_square(e_aff), field_add(d, 1)))) == field_neg(
        field_mul(field_mul(z4, field_square(e_aff)), field_add(d, 1)),
    )) by {
        lemma_field_mul_neg(z4, field_mul(field_square(e_aff), field_add(d, 1)));
        lemma_field_mul_assoc(z4, field_square(e_aff), field_add(d, 1));
    };

    // Z⁴ · e_aff² = (Z² · e_aff)² = e²
    assert(field_mul(z4, field_square(e_aff)) == field_square(e)) by {
        lemma_four_factor_rearrange(z2, e_aff, z2, e_aff);
    };
}

/// Lemma: when inv = 0, batch_compress_body produces the all-zeros encoding.
///
/// This handles the degenerate case (identity/torsion points where eg·fh = 0).
/// When batch_invert returns inv = 0, all products involving inv vanish,
/// so zinv = tinv = 0, both negchecks are false (is_negative(0) = false),
/// and the final s = 0 yields u8_32_from_nat(0).
pub proof fn lemma_batch_compress_body_inv_zero(e: nat, f: nat, g: nat, h: nat, eg: nat, fh: nat)
    ensures
        batch_compress_body(e, f, g, h, eg, fh, 0) == u8_32_from_nat(0),
{
    let invsqrt_a_minus_d = fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D);
    assert(p() > 2) by {
        p_gt_2();
    };

    // All field_mul(x, 0) == 0 since 0 % p == 0
    assert(field_mul(eg, 0) == 0) by {
        lemma_field_mul_zero_right(eg, 0);
    };
    assert(field_mul(fh, 0) == 0) by {
        lemma_field_mul_zero_right(fh, 0);
    };
    assert(!is_negative(0));
    assert(field_mul(field_mul(h, e), 0) == 0) by {
        lemma_field_mul_zero_right(field_mul(h, e), 0);
    };
    assert(field_mul(g, 0) == 0) by {
        lemma_field_mul_zero_right(g, 0);
    };
    assert(field_mul(invsqrt_a_minus_d, 0) == 0) by {
        lemma_field_mul_zero_right(invsqrt_a_minus_d, 0);
    };
    assert(field_mul(field_sub(h, g), 0) == 0) by {
        lemma_field_mul_zero_right(field_sub(h, g), 0);
    };
}

/// Lemma: ristretto_compress_affine(x, y) == u8_32_from_nat(0) when x·y ≡ 0 (mod p).
///
/// When at least one affine coordinate is zero mod p, u2 = x·y = 0 in
/// ristretto_compress_extended, so invsqrt(u1·u2²) = invsqrt(0) = 0.
/// All downstream products vanish, giving s = 0 and the zero encoding.
pub proof fn lemma_ristretto_compress_affine_zero_xy(x: nat, y: nat)
    requires
        field_mul(x, y) % p() == 0,
    ensures
        ristretto_compress_affine(x, y) == u8_32_from_nat(0),
{
    let pn = p();
    assert(pn > 2) by {
        p_gt_2();
    };

    // ristretto_compress_affine(x, y) = ristretto_compress_extended(x, y, 1, t)
    // where t = field_mul(x, y).  We trace the spec with t = 0.
    let t = field_mul(x, y);
    assert(t == 0) by {
        lemma_mod_bound((x * y) as int, pn as int);
        if t != 0 {
            lemma_small_mod(t, pn);
        }
    };

    // u2 = field_mul(x, y) = 0, so u2² = 0, so invsqrt argument u1·u2² = 0
    let z: nat = 1;
    let u1 = field_mul(field_add(z, y), field_sub(z, y));
    let u2 = field_square(t);
    assert(field_mul(u1, u2) == 0) by {
        assert(u2 == 0) by {
            lemma_small_mod(0nat, pn);
        };
        lemma_field_mul_zero_right(u1, u2);
    };

    // nat_invsqrt(0) = 0, so isq = 0, making i1 = i2 = z_inv = den_inv = 0
    let isq = nat_invsqrt(field_mul(u1, u2));
    assert(isq == 0) by {
        lemma_small_mod(0nat, pn);
    };

    assert(field_mul(isq, u1) == 0) by {
        lemma_field_mul_zero_left(isq, u1);
    };
    assert(field_mul(isq, t) == 0) by {
        lemma_field_mul_zero_left(isq, t);
    };

    let i1 = field_mul(isq, u1);
    let i2 = field_mul(isq, t);

    // z_inv = i1 · (i2 · t) = 0
    assert(field_mul(i2, t) == 0) by {
        lemma_field_mul_zero_left(i2, t);
    };
    assert(field_mul(i1, field_mul(i2, t)) == 0) by {
        lemma_field_mul_zero_left(i1, field_mul(i2, t));
    };
    let z_inv = field_mul(i1, field_mul(i2, t));

    // enchanted_denominator = i1 · INVSQRT_A_MINUS_D = 0
    let invsqrt_a_minus_d = fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D);
    assert(field_mul(i1, invsqrt_a_minus_d) == 0) by {
        lemma_field_mul_zero_left(i1, invsqrt_a_minus_d);
    };

    // rotate = is_negative(t · z_inv) = is_negative(0) = false
    assert(!is_negative(field_mul(t, z_inv))) by {
        assert(field_mul(t, z_inv) == 0) by {
            lemma_field_mul_zero_left(t, z_inv);
        };
    };

    // ¬rotate ⟹ den_inv_rot = i2 = 0, and x_rot = x
    // is_negative(x · z_inv) = is_negative(0) = false ⟹ y_final = y
    assert(!is_negative(field_mul(x, z_inv))) by {
        assert(field_mul(x, z_inv) == 0) by {
            lemma_field_mul_zero_right(x, z_inv);
        };
    };

    // s = den_inv_rot · (z − y_final) = 0 · (...) = 0
    assert(field_mul(i2, field_sub(z, y)) == 0) by {
        lemma_field_mul_zero_left(i2, field_sub(z, y));
    };
    // is_negative(0) = false ⟹ s_final = 0 ⟹ result = u8_32_from_nat(0)
}

/// Lemma: when eg·fh = 0 for a valid on-curve point, the doubled affine
/// point's Ristretto encoding is the zero encoding.
///
/// Proof: Use lemma_doubled_affine_from_batch_state to get doubled = (e/f, g/h).
/// Since eg·fh = 0, by Euclid's lemma at least one of {e, g, f, h} is zero.
/// In each case, one coordinate of the doubled point is zero (either the
/// numerator is zero, or field_inv(0) = 0 makes the denominator kill it).
/// Therefore field_mul(doubled.0, doubled.1) = 0, and by
/// lemma_ristretto_compress_affine_zero_xy the encoding is all zeros.
///
/// Reference: Curve25519 torsion structure; [RISTRETTO] §5.3
/// Runtime validation: `test_degenerate_double_compresses_to_zero`
pub proof fn lemma_degenerate_double_compresses_to_zero(
    x: nat,
    y: nat,
    z: nat,
    t: nat,
    e: nat,
    f: nat,
    g: nat,
    h: nat,
)
    requires
        x < p(),
        y < p(),
        z < p(),
        t < p(),
        z % p() != 0,
        field_mul(z, t) == field_mul(x, y),
        ({
            let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
            e == field_mul(2, field_mul(x, y)) && f == field_add(
                field_square(z),
                field_mul(d, field_square(t)),
            ) && g == field_add(field_square(y), field_square(x)) && h == field_sub(
                field_square(z),
                field_mul(d, field_square(t)),
            )
        }),
        field_mul(field_mul(e, g), field_mul(f, h)) % p() == 0,
    ensures
        ristretto_compress_affine(
            edwards_double(field_mul(x, field_inv(z)), field_mul(y, field_inv(z))).0,
            edwards_double(field_mul(x, field_inv(z)), field_mul(y, field_inv(z))).1,
        ) == u8_32_from_nat(0),
{
    let pn = p();
    assert(pn > 2) by {
        p_gt_2();
    };
    assert(is_prime(pn)) by {
        axiom_p_is_prime();
    };

    // doubled = (e/f, g/h)
    let doubled = edwards_double(field_mul(x, field_inv(z)), field_mul(y, field_inv(z)));
    let dx = field_mul(e, field_inv(f));
    let dy = field_mul(g, field_inv(h));
    assert(doubled == (dx, dy)) by {
        lemma_doubled_affine_from_batch_state(x, y, z, t, e, f, g, h);
    };

    let eg = field_mul(e, g);
    let fh = field_mul(f, h);

    // eg·fh = 0 ⟹ eg = 0 ∨ fh = 0, by Euclid's lemma
    assert(eg % pn == 0 || fh % pn == 0) by {
        assert((eg * fh) % pn == 0) by {
            let egfh = field_mul(eg, fh);
            lemma_mod_bound((eg * fh) as int, pn as int);
            if egfh != 0 {
                lemma_small_mod(egfh, pn);
            }
            lemma_small_mod(eg, pn);
            lemma_small_mod(fh, pn);
            lemma_mul_mod_noop_left(eg as int, fh as int, pn as int);
            lemma_mul_mod_noop_right((eg % pn) as int, fh as int, pn as int);
        };
        lemma_euclid_prime(eg, fh, pn);
    };

    // In each branch, show field_mul(dx, dy) == 0
    assert(field_mul(dx, dy) == 0) by {
        if eg % pn == 0 {
            assert(eg == 0) by {
                if eg != 0 {
                    lemma_small_mod(eg, pn);
                }
            };
            assert((e * g) % pn == 0) by {
                lemma_small_mod(e, pn);
                lemma_small_mod(g, pn);
                lemma_mul_mod_noop_left(e as int, g as int, pn as int);
                lemma_mul_mod_noop_right((e % pn) as int, g as int, pn as int);
            };
            lemma_euclid_prime(e, g, pn);

            if e % pn == 0 {
                // e = 0 ⟹ dx = 0·inv(f) = 0
                assert(e == 0) by {
                    if e != 0 {
                        lemma_small_mod(e, pn);
                    }
                };
                assert(dx == 0) by {
                    lemma_field_mul_zero_left(0nat, field_inv(f));
                };
                lemma_field_mul_zero_left(dx, dy);
            } else {
                // g = 0 ⟹ dy = 0·inv(h) = 0
                assert(g == 0) by {
                    if g != 0 {
                        lemma_small_mod(g, pn);
                    }
                };
                assert(dy == 0) by {
                    lemma_field_mul_zero_left(0nat, field_inv(h));
                };
                lemma_field_mul_zero_right(dx, dy);
            }
        } else {
            // fh = 0 ⟹ f = 0 ∨ h = 0
            assert(fh == 0) by {
                if fh != 0 {
                    lemma_small_mod(fh, pn);
                }
            };
            assert((f * h) % pn == 0) by {
                lemma_small_mod(f, pn);
                lemma_small_mod(h, pn);
                lemma_mul_mod_noop_left(f as int, h as int, pn as int);
                lemma_mul_mod_noop_right((f % pn) as int, h as int, pn as int);
            };
            lemma_euclid_prime(f, h, pn);

            if f % pn == 0 {
                // f = 0 ⟹ inv(f) = inv(0) = 0 ⟹ dx = e·0 = 0
                assert(f == 0) by {
                    if f != 0 {
                        lemma_small_mod(f, pn);
                    }
                };
                assert(field_inv(f) == 0) by {
                    field_inv_zero();
                };
                assert(dx == 0) by {
                    lemma_field_mul_zero_right(e, field_inv(f));
                };
                lemma_field_mul_zero_left(dx, dy);
            } else {
                // h = 0 ⟹ inv(h) = inv(0) = 0 ⟹ dy = g·0 = 0
                assert(h == 0) by {
                    if h != 0 {
                        lemma_small_mod(h, pn);
                    }
                };
                assert(field_inv(h) == 0) by {
                    field_inv_zero();
                };
                assert(dy == 0) by {
                    lemma_field_mul_zero_right(g, field_inv(h));
                };
                lemma_field_mul_zero_right(dx, dy);
            }
        }
    };

    // field_mul(dx, dy) = 0 ⟹ ristretto_compress_affine gives the zero encoding
    assert(ristretto_compress_affine(doubled.0, doubled.1) == u8_32_from_nat(0)) by {
        assert(field_mul(dx, dy) % pn == 0) by {
            lemma_small_mod(0nat, pn);
        };
        lemma_ristretto_compress_affine_zero_xy(dx, dy);
    };
}

/// Helper: field_mul(a, 1) == a for any field element a < p().
///
/// Combines `lemma_field_mul_one_right` and `lemma_field_element_reduced`
/// into a single call, eliminating a common two-line proof pattern.
proof fn lemma_mul_one_identity(a: nat)
    requires
        a < p(),
    ensures
        field_mul(a, 1nat) == a,
{
    assert(field_mul(a, 1nat) == a) by {
        lemma_field_mul_one_right(a);
        lemma_field_element_reduced(a);
    };
}

// =============================================================================
// Axiom: curve equation batch identity  h² − g² = −e² · (1 + d)
// =============================================================================
/// Helper: (x+y)² − (x−y)² = 4xy in GF(p).
///
/// Derived from diff-of-squares + the recover-double identities:
///   (s−d)(s+d) = s²−d²,  (x+y)−(x−y) = 2y,  (x+y)+(x−y) = 2x.
proof fn lemma_sum_sq_minus_diff_sq(x: nat, y: nat)
    ensures
        field_sub(field_square(field_add(x, y)), field_square(field_sub(x, y))) == field_mul(
            field_mul(2nat, 2nat),
            field_mul(x, y),
        ),
{
    assert(p() > 2) by {
        p_gt_2();
    };
    let s = field_add(x, y);
    let d = field_sub(x, y);

    // (s+d)(s-d) = s²-d², and (x+y)-(x-y)=2y, (x+y)+(x-y)=2x
    assert(field_sub(field_square(s), field_square(d)) == field_mul(
        field_mul(2nat, 2nat),
        field_mul(x, y),
    )) by {
        lemma_field_diff_of_squares(s, d);
        lemma_field_add_sub_recover_double(x, y);
        lemma_field_add_add_recover_double(x, y);
        lemma_field_mul_exchange(2nat, y, 2nat, x);
        lemma_field_mul_comm(y, x);
    };
}

/// Lemma: for a point (a, b) on the Edwards curve −a² + b² = 1 + d·a²·b²
/// with batch intermediates e = 2ab, g = a² + b², h = 1 − d·a²·b²:
///
///     h² − g² = −e² · (1 + d)
///
/// ## Proof outline
///
/// Use the identity (x+y)² − (x−y)² = 4xy twice:
///   1. With (b², a²): g² − (b²−a²)² = 4·a²b²
///   2. With (1, da²b²): (1+da²b²)² − h² = 4·da²b²
///
/// The curve equation gives b²−a² = 1+da²b², so steps 1 and 2 telescope:
///   g² − h² = 4·a²b² + 4·da²b² = 4·a²b²·(d+1) = e²·(d+1)
///
/// Therefore h² − g² = −e²·(d+1).
///
/// Reference: Consequence of the twisted Edwards curve equation; Hamburg (2015) Decaf §6
/// Runtime validation: `test_curve_eq_batch_identity`
pub proof fn lemma_curve_eq_batch_identity(a: nat, b: nat)
    requires
        a < p(),
        b < p(),
        is_on_edwards_curve(a, b),
    ensures
        ({
            let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
            let e = field_mul(2, field_mul(a, b));
            let g = field_add(field_square(a), field_square(b));
            let h = field_sub(1nat, field_mul(d, field_mul(field_square(a), field_square(b))));
            field_sub(field_square(h), field_square(g)) == field_neg(
                field_mul(field_square(e), field_add(d, 1)),
            )
        }),
{
    let dd = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
    assert(p() > 2) by {
        p_gt_2();
    };

    let a2 = field_square(a);
    let b2 = field_square(b);
    let ab = field_mul(a, b);
    let a2b2 = field_mul(a2, b2);
    let dab2 = field_mul(dd, a2b2);
    let e = field_mul(2, ab);
    let g = field_add(a2, b2);
    let h = field_sub(1nat, dab2);
    let d_plus_1 = field_add(dd, 1);
    let two_sq = field_mul(2nat, 2nat);

    let sq_g = field_square(g);
    let sq_h = field_square(h);

    // Curve equation: b² − a² = 1 + d·a²·b²
    let curve_rhs = field_add(1nat, dab2);
    assert(field_sub(b2, a2) == curve_rhs);
    let sq_crhs = field_square(curve_rhs);

    // === Part A: g² − h² = V + W (via telescoping) ===

    let V = field_mul(two_sq, a2b2);

    // A1+A2. g = b²+a², and (b²+a²)² − (b²−a²)² = 4·a²·b² = V
    assert(field_sub(sq_g, field_square(field_sub(b2, a2))) == V) by {
        lemma_field_add_comm(a2, b2);
        lemma_sum_sq_minus_diff_sq(b2, a2);
        lemma_field_mul_comm(b2, a2);
    };

    // A3. b²−a² = curve_rhs from the curve equation, so sq(b²−a²) = sq_crhs
    assert(field_sub(sq_g, sq_crhs) == V);

    let W = field_mul(two_sq, dab2);

    // A4. (1+dab2)² − (1−dab2)² = 4·dab2 = W
    assert(field_sub(sq_crhs, sq_h) == W) by {
        lemma_sum_sq_minus_diff_sq(1nat, dab2);
        lemma_field_mul_one_left(dab2);
        lemma_field_element_reduced(dab2);
    };

    // A5. Telescoping: sq_g − sq_h = V + W
    let VW = field_add(V, W);
    assert(field_sub(sq_g, sq_h) == VW) by {
        // sub(sq_g, sq_crhs) = V  ⟹  sq_g = V + sq_crhs
        assert(field_add(V, sq_crhs) == sq_g) by {
            lemma_field_add_sub_cancel(sq_g, sq_crhs);
        };
        // sub(sq_crhs, sq_h) = W  ⟹  sq_crhs = W + sq_h
        assert(field_add(W, sq_h) == sq_crhs) by {
            lemma_field_add_sub_cancel(sq_crhs, sq_h);
        };
        // sq_g = V + (W + sq_h) = (V+W) + sq_h
        assert(sq_g == field_add(VW, sq_h)) by {
            lemma_field_add_assoc(V, W, sq_h);
        };
        // Therefore sub(sq_g, sq_h) = VW
        lemma_field_sub_add_cancel(VW, sq_h);
    };

    // === Part B: e²·(d+1) = W + V ===

    // B1. e² = 4·a²b² = V
    assert(field_square(e) == V) by {
        lemma_field_mul_exchange(2nat, ab, 2nat, ab);
        lemma_field_mul_exchange(a, b, a, b);
    };

    // B2+B3. a²b²·(d+1) = d·a²b² + a²b² = dab2 + a2b2
    assert(field_mul(a2b2, d_plus_1) == field_add(dab2, a2b2)) by {
        lemma_field_mul_distributes_over_add(a2b2, dd, 1);
        lemma_field_mul_comm(a2b2, dd);
        lemma_field_mul_one_right(a2b2);
        lemma_field_element_reduced(a2b2);
    };

    // B4. e²·(d+1) = 4·(dab2 + a2b2) = W + V
    assert(field_mul(field_square(e), d_plus_1) == field_add(W, V)) by {
        lemma_field_mul_assoc(two_sq, a2b2, d_plus_1);
        lemma_field_mul_distributes_over_add(two_sq, dab2, a2b2);
    };

    // === Part C: Conclude ===
    // VW = V+W = W+V = e²·(d+1), so sub(sq_g, sq_h) = e²·(d+1)
    assert(field_sub(sq_g, sq_h) == field_mul(field_square(e), d_plus_1)) by {
        lemma_field_add_comm(V, W);
    };

    // sub(sq_h, sq_g) = −sub(sq_g, sq_h) = −(e²·(d+1))
    assert(field_sub(sq_h, sq_g) == field_neg(field_mul(field_square(e), d_plus_1))) by {
        lemma_field_sub_antisymmetric(sq_g, sq_h);
    };
}

/// Helper: u1·u2² = (−1−d)·B² where u1 = (1+y)(1−y), u2 = eg/(fh), B = e·eg/(h·fh).
///
/// Proof: u1 = 1−y² = (h²−g²)/h² (using y=g/h and diff of squares).
/// Then u1·u2² = (h²−g²)·(eg)² / (h·fh)². By the batch identity h²−g² = −e²(1+d),
/// this becomes (−1−d)·e²·(eg)² / (h·fh)² = (−1−d)·(e·eg / (h·fh))² = (−1−d)·B².
proof fn lemma_u1_u2_sq_factoring(e: nat, f: nat, g: nat, h: nat, eg: nat, fh: nat, d: nat)
    requires
        eg == field_mul(e, g),
        fh == field_mul(f, h),
        field_mul(eg, fh) != 0,
        h % p() != 0,
        field_sub(field_square(h), field_square(g)) == field_neg(
            field_mul(field_square(e), field_add(d, 1)),
        ),
    ensures
        ({
            let inv_f = field_inv(f);
            let inv_h = field_inv(h);
            let y_aff = field_mul(g, inv_h);
            let x_aff = field_mul(e, inv_f);
            let t_aff = field_mul(x_aff, y_aff);
            let inv_fh = field_inv(fh);
            let u1 = field_mul(field_add(1nat, y_aff), field_sub(1nat, y_aff));
            let u2 = t_aff;
            let neg_one_minus_d = field_sub(field_neg(1nat), d);
            let big_b = field_mul(field_mul(e, eg), field_inv(field_mul(h, fh)));
            field_mul(u1, field_square(u2)) == field_mul(neg_one_minus_d, field_square(big_b))
        }),
{
    assert(p() > 2) by {
        p_gt_2();
    };
    let inv_f = field_inv(f);
    let inv_h = field_inv(h);
    let y_aff = field_mul(g, inv_h);
    let x_aff = field_mul(e, inv_f);
    let t_aff = field_mul(x_aff, y_aff);
    let inv_fh = field_inv(fh);
    let u1 = field_mul(field_add(1nat, y_aff), field_sub(1nat, y_aff));
    let u2 = t_aff;
    let neg_one_minus_d = field_sub(field_neg(1nat), d);
    let big_b = field_mul(field_mul(e, eg), field_inv(field_mul(h, fh)));
    let sq_h3 = field_square(h);
    let sq_g3 = field_square(g);
    let sq_e3 = field_square(e);
    let inv_sq_h3 = field_inv(sq_h3);
    let d_plus_1 = field_add(d, 1);
    let h_fh = field_mul(h, fh);
    let e_eg = field_mul(e, eg);

    // Step 1: u1 = 1 − y² = (h²−g²)/h²
    assert(u1 == field_sub(1nat, field_square(y_aff))) by {
        lemma_field_mul_comm(field_add(1nat, y_aff), field_sub(1nat, y_aff));
        lemma_field_diff_of_squares(1nat, y_aff);
        assert(field_square(1nat) == 1nat) by {
            lemma_small_mod(1nat, p());
        };
    };

    assert(field_square(y_aff) == field_mul(sq_g3, inv_sq_h3)) by {
        lemma_quotient_of_squares(g, h);
    };

    assert(field_mul(sq_h3, inv_sq_h3) == 1nat) by {
        lemma_nonzero_product(h, h);
        lemma_field_element_reduced(field_square(h));
        lemma_inv_mul_cancel(sq_h3);
        lemma_field_mul_comm(field_inv(sq_h3), sq_h3);
    };

    assert(u1 == field_mul(field_sub(sq_h3, sq_g3), inv_sq_h3)) by {
        lemma_field_mul_distributes_over_sub_right(sq_h3, sq_g3, inv_sq_h3);
    };

    // Step 2: u2² = (eg)² / (fh)²
    assert(t_aff == field_mul(eg, inv_fh) && field_square(u2) == field_mul(
        field_square(eg),
        field_inv(field_square(fh)),
    )) by {
        lemma_four_factor_rearrange(e, inv_f, g, inv_h);
        lemma_inv_of_product(f, h);
        lemma_quotient_of_squares(eg, fh);
    };

    // Step 3: LHS = u1·u2² = (h²−g²)·(eg)² / (h²·(fh)²) = (h²−g²)·(eg)² / (h·fh)²
    assert(field_mul(u1, field_square(u2)) == field_mul(
        field_mul(field_sub(sq_h3, sq_g3), field_square(eg)),
        field_inv(field_square(h_fh)),
    )) by {
        lemma_field_mul_exchange(
            field_sub(sq_h3, sq_g3),
            inv_sq_h3,
            field_square(eg),
            field_inv(field_square(fh)),
        );
        lemma_inv_of_product(sq_h3, field_square(fh));
        lemma_product_of_squares_eq_square_of_product(h, fh);
    };

    // Step 4: RHS = (−1−d)·(e·eg)² / (h·fh)² = (−1−d)·e²·(eg)² / (h·fh)²
    assert(field_mul(neg_one_minus_d, field_square(big_b)) == field_mul(
        field_mul(neg_one_minus_d, field_mul(sq_e3, field_square(eg))),
        field_inv(field_square(h_fh)),
    )) by {
        lemma_quotient_of_squares(e_eg, h_fh);
        lemma_product_of_squares_eq_square_of_product(e, eg);
        lemma_field_mul_assoc(
            neg_one_minus_d,
            field_mul(sq_e3, field_square(eg)),
            field_inv(field_square(h_fh)),
        );
    };

    // Step 5: Equate numerators. Need (h²−g²)·(eg)² = (−1−d)·e²·(eg)²,
    // i.e. h²−g² = (−1−d)·e². Bridge from the batch identity h²−g² = −e²·(d+1)
    assert(field_sub(sq_h3, sq_g3) == field_mul(neg_one_minus_d, sq_e3)) by {
        // −e²·(d+1) = e²·(−(d+1)) = e²·(−1−d)
        lemma_field_mul_neg(sq_e3, d_plus_1);
        lemma_neg_one_times_is_neg(d_plus_1);
        lemma_field_mul_distributes_over_add(field_neg(1nat), d, 1);
        lemma_neg_one_times_is_neg(d);
        lemma_neg_one_times_is_neg(1nat);
        lemma_field_mul_one_right(field_neg(1nat));
        lemma_field_element_reduced(field_neg(1nat));
        lemma_field_add_comm(field_neg(d), field_neg(1nat));
        lemma_field_sub_eq_add_neg(field_neg(1nat), d);
        lemma_field_mul_comm(sq_e3, neg_one_minus_d);
    };

    // Conclude: numerators match, so LHS·(eg)² = RHS·(eg)², so u1·u2² = (−1−d)·B²
    assert(field_mul(neg_one_minus_d, field_mul(sq_e3, field_square(eg))) == field_mul(
        field_sub(sq_h3, sq_g3),
        field_square(eg),
    )) by {
        lemma_field_mul_assoc(neg_one_minus_d, sq_e3, field_square(eg));
    };
}

/// Helper: the full algebraic proof that batch_compress_body == ristretto_compress_affine.
///
/// The proof proceeds in phases:
///   Phase A: Establish inv correspondences (zinv = inv(fh), tinv = inv(eg))
///   Phase B: Invsqrt factoring via axiom_invsqrt_factors_over_square
///   Phase C: Show z_inv_std = 1 using axiom_c_iad_sq_identity
///   Phase D: Show both algorithms take the same branches and produce s values
///            that are equal up to sign, so field_abs equalizes them
proof fn lemma_batch_std_final_matching(e: nat, f: nat, g: nat, h: nat, eg: nat, fh: nat, inv: nat)
    requires
        eg == field_mul(e, g),
        fh == field_mul(f, h),
        field_mul(eg, fh) != 0,
        field_mul(inv, field_mul(eg, fh)) == 1,
        ({
            let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
            field_sub(field_square(h), field_square(g)) == field_neg(
                field_mul(field_square(e), field_add(d, 1)),
            )
        }),
        e % p() != 0,
        f % p() != 0,
        g % p() != 0,
        h % p() != 0,
        eg % p() != 0,
        fh % p() != 0,
    ensures
        batch_compress_body(e, f, g, h, eg, fh, inv) == ristretto_compress_affine(
            field_mul(e, field_inv(f)),
            field_mul(g, field_inv(h)),
        ),
{
    let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
    let c_iad = fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D);
    let inv_f = field_inv(f);
    let inv_h = field_inv(h);
    let inv_fh = field_inv(fh);
    let x_aff = field_mul(e, inv_f);
    let y_aff = field_mul(g, inv_h);
    let t_aff = field_mul(x_aff, y_aff);
    assert(p() > 2) by {
        p_gt_2();
    };

    // === Phase A: Inv correspondences ===
    // t_aff = eg/fh
    assert(t_aff == field_mul(eg, inv_fh)) by {
        lemma_four_factor_rearrange(e, inv_f, g, inv_h);
        lemma_inv_of_product(f, h);
    };
    // inv ≡ inv(egfh) (mod p) by uniqueness of inverses
    let egfh = field_mul(eg, fh);
    assert(egfh % p() != 0) by {
        lemma_field_element_reduced(egfh);
    };
    assert(inv % p() == field_inv(egfh) % p()) by {
        // field_mul(egfh, inv) == 1 (from precondition via commutativity)
        assert(field_mul(egfh, inv) == 1) by {
            lemma_field_mul_comm(inv, egfh);
        };
        // field_mul(egfh, field_inv(egfh)) == 1
        assert(field_mul(egfh, field_inv(egfh)) == 1nat) by {
            field_inv_property(egfh);
            lemma_mul_mod_noop_left(egfh as int, field_inv(egfh) as int, p() as int);
        };
        // inv ≡ inv(egfh) (mod p) by left cancellation
        lemma_field_mul_left_cancel(egfh, inv, field_inv(egfh));
    };
    // zinv = eg*inv = eg*inv(egfh) = inv(fh)
    assert(field_mul(eg, inv) == field_inv(fh)) by {
        lemma_mul_mod_noop_right(eg as int, inv as int, p() as int);
        lemma_mul_mod_noop_right(eg as int, field_inv(egfh) as int, p() as int);
        lemma_a_times_inv_ab_is_inv_b(eg, fh);
    };
    // tinv = fh*inv = fh*inv(egfh) = inv(eg)
    assert(field_mul(fh, inv) == field_inv(eg)) by {
        lemma_mul_mod_noop_right(fh as int, inv as int, p() as int);
        lemma_mul_mod_noop_right(fh as int, field_inv(egfh) as int, p() as int);
        lemma_field_mul_comm(eg, fh);
        lemma_a_times_inv_ab_is_inv_b(fh, eg);
    };

    // Delegate to the case dispatch sub-proof
    assert(batch_compress_body(e, f, g, h, eg, fh, inv) == ristretto_compress_affine(
        field_mul(e, field_inv(f)),
        field_mul(g, field_inv(h)),
    )) by {
        lemma_batch_std_case_dispatch(e, f, g, h, eg, fh, inv);
    };
}

/// field_abs(field_neg(a)) == field_abs(a) for field elements < p().
proof fn lemma_field_abs_neg(a: nat)
    requires
        a < p(),
    ensures
        field_abs(field_neg(a)) == field_abs(a),
{
    assert(p() > 2 && p() % 2 == 1) by {
        p_gt_2();
        lemma_p_is_odd();
    };
    if a == 0 {
        // field_neg(0) = field_canonical((p() - field_canonical(0))) = p() % p() = 0
        assert(field_canonical(0nat) == 0nat) by {
            lemma_small_mod(0nat, p());
        };
        assert(field_canonical(p()) == 0nat) by {
            assert(p() % p() == 0nat) by (nonlinear_arith)
                requires
                    p() > 0,
            ;
        };
    } else {
        let neg_a = field_neg(a);
        assert(field_canonical(a) == a) by {
            lemma_small_mod(a, p());
        };
        assert(neg_a == (p() - a) as nat) by {
            lemma_small_mod((p() - a) as nat, p());
        };
        assert(field_canonical(neg_a) == neg_a) by {
            lemma_small_mod(neg_a, p());
        };
        assert(a % 2 != neg_a % 2) by (nonlinear_arith)
            requires
                a as int + neg_a as int == p() as int,
                p() % 2 == 1,
        ;
        assert(field_neg(neg_a) == a) by {
            lemma_field_neg_neg(a);
            lemma_small_mod(a, p());
        };
        if is_negative(a) {
            assert(field_abs(a) == neg_a);
            assert(!is_negative(neg_a));
            assert(field_abs(neg_a) == neg_a);
        } else {
            assert(field_abs(a) == a);
            assert(is_negative(neg_a));
            assert(field_abs(neg_a) == field_neg(neg_a));
        }
    }
}

/// field_abs(a*x) == field_abs(b*x) when a == b or a == field_neg(b).
proof fn lemma_field_abs_mul_sign(a: nat, b: nat, x: nat)
    requires
        a == b || a == field_neg(b),
    ensures
        field_abs(field_mul(a, x)) == field_abs(field_mul(b, x)),
{
    assert(p() > 2) by {
        p_gt_2();
    };
    if a == b {
    } else {
        assert(field_mul(a, x) == field_neg(field_mul(b, x))) by {
            lemma_field_neg_mul_left(b, x);
        };
        assert(field_abs(field_mul(a, x)) == field_abs(field_mul(b, x))) by {
            lemma_mod_bound((b * x) as int, p() as int);
            lemma_field_abs_neg(field_mul(b, x));
        };
    }
}

/// Phase C helper: proves z_inv_std = 1.
///
/// Given invsqrt_std = field_abs(c_iad · inv(B)) and the algebraic identity
/// u1·t² = (-1-d)·B², proves that i1·(i2·t) = 1 where i1 = invsqrt·u1, i2 = invsqrt·t.
proof fn lemma_z_inv_std_is_one(
    invsqrt_std: nat,
    u1: nat,
    t_aff: nat,
    c_iad: nat,
    B: nat,
    neg_one_minus_d: nat,
)
    requires
        invsqrt_std == field_abs(field_mul(c_iad, field_inv(B))),
        field_mul(u1, field_square(t_aff)) == field_mul(neg_one_minus_d, field_square(B)),
        B % p() != 0,
        neg_one_minus_d % p() != 0,
        field_mul(field_square(c_iad), neg_one_minus_d) == 1,
    ensures
        ({
            let i1 = field_mul(invsqrt_std, u1);
            let i2 = field_mul(invsqrt_std, t_aff);
            field_mul(i1, field_mul(i2, t_aff)) == 1
        }),
{
    let R = field_mul(c_iad, field_inv(B));
    let i1_std = field_mul(invsqrt_std, u1);
    let i2_std = field_mul(invsqrt_std, t_aff);
    let z_inv_std = field_mul(i1_std, field_mul(i2_std, t_aff));
    assert(p() > 2) by {
        p_gt_2();
    };

    // z_inv_std = invsqrt² · u1 · t²
    let i1_i2 = field_mul(i1_std, i2_std);
    let sq_inv = field_square(invsqrt_std);
    assert(i1_i2 == field_mul(sq_inv, field_mul(u1, t_aff))) by {
        lemma_four_factor_rearrange(invsqrt_std, u1, invsqrt_std, t_aff);
    };

    assert(z_inv_std == field_mul(sq_inv, field_mul(u1, field_square(t_aff)))) by {
        assert(z_inv_std == field_mul(i1_i2, t_aff)) by {
            lemma_field_mul_assoc(i1_std, i2_std, t_aff);
        };
        assert(field_mul(field_mul(sq_inv, field_mul(u1, t_aff)), t_aff) == field_mul(
            sq_inv,
            field_mul(u1, field_square(t_aff)),
        )) by {
            lemma_field_mul_assoc(sq_inv, field_mul(u1, t_aff), t_aff);
            lemma_field_mul_assoc(u1, t_aff, t_aff);
        };
    };

    // Substitute u1·t² = (−1−d)·B²
    assert(z_inv_std == field_mul(sq_inv, field_mul(neg_one_minus_d, field_square(B))));

    // sq_inv = sq(R): squaring absorbs field_abs sign
    assert(sq_inv == field_square(R)) by {
        if is_negative(R) {
            lemma_neg_square_eq(R);
            lemma_field_element_reduced(R);
            lemma_small_mod(R, p());
        }
    };

    // sq(R) = sq(c_iad) · sq(inv(B))
    let sq_c = field_square(c_iad);
    let sq_inv_B = field_square(field_inv(B));
    assert(sq_inv == field_mul(sq_c, sq_inv_B)) by {
        lemma_product_of_squares_eq_square_of_product(c_iad, field_inv(B));
    };

    // z_inv_std = (c_iad²·(−1−d)) · (inv(B)²·B²)
    assert(z_inv_std == field_mul(
        field_mul(sq_c, neg_one_minus_d),
        field_mul(sq_inv_B, field_square(B)),
    )) by {
        lemma_four_factor_rearrange(sq_c, sq_inv_B, neg_one_minus_d, field_square(B));
    };

    // inv(B)²·B² = sq(inv(B)·B) = sq(1) = 1
    assert(field_square(1nat) == 1nat) by {
        p_gt_2();
        lemma_small_mod(1nat, p());
    };
    assert(field_mul(sq_inv_B, field_square(B)) == 1nat) by {
        p_gt_2();
        lemma_product_of_squares_eq_square_of_product(field_inv(B), B);
        lemma_inv_mul_cancel(B);
    };

    // z_inv_std = c_iad²·(−1−d) · 1 = c_iad²·(−1−d) = 1
    assert(z_inv_std == 1) by {
        lemma_field_mul_one_right(field_mul(sq_c, neg_one_minus_d));
        lemma_field_element_reduced(field_mul(sq_c, neg_one_minus_d));
    };
}

/// Algebraic setup for no-rotation case: proves the key identities
/// connecting batch and standard negcheck arguments and invsqrt relationship.
proof fn lemma_no_rotation_algebraic_setup(
    e: nat,
    f: nat,
    g: nat,
    h: nat,
    eg: nat,
    fh: nat,
    invsqrt_std: nat,
    c_iad: nat,
    B: nat,
    t_aff: nat,
    x_aff: nat,
    y_aff: nat,
    zinv: nat,
    tinv: nat,
)
    requires
        eg == field_mul(e, g),
        fh == field_mul(f, h),
        x_aff == field_mul(e, field_inv(f)),
        y_aff == field_mul(g, field_inv(h)),
        t_aff == field_mul(x_aff, y_aff),
        t_aff == field_mul(eg, field_inv(fh)),
        zinv == field_inv(fh),
        tinv == field_inv(eg),
        invsqrt_std == field_abs(field_mul(c_iad, field_inv(B))),
        B == field_mul(field_mul(e, eg), field_inv(field_mul(h, fh))),
        e % p() != 0,
        f % p() != 0,
        g % p() != 0,
        h % p() != 0,
        eg % p() != 0,
        fh % p() != 0,
        B % p() != 0,
    ensures
        field_mul(field_mul(h, e), zinv) == x_aff,
        field_mul(g, tinv) == field_inv(e),
        ({
            let K = field_mul(t_aff, field_inv(h));
            let ciad_inv_e = field_mul(c_iad, field_inv(e));
            (field_mul(invsqrt_std, K) == ciad_inv_e || field_mul(invsqrt_std, K) == field_neg(
                ciad_inv_e,
            )) && K % p() != 0
        }),
{
    p_gt_2();
    let ciad_inv_e = field_mul(c_iad, field_inv(e));
    let inv_h = field_inv(h);
    let K = field_mul(t_aff, inv_h);
    let ciad_inv_B = field_mul(c_iad, field_inv(B));

    // batch negcheck2 arg = x_aff
    assert(field_mul(field_mul(h, e), zinv) == x_aff) by {
        lemma_inv_of_product(f, h);
        lemma_field_mul_comm(field_inv(f), field_inv(h));
        lemma_field_mul_exchange(h, e, field_inv(h), field_inv(f));
        lemma_inv_mul_cancel(h);
        lemma_field_mul_comm(field_inv(h), h);
        lemma_field_mul_one_left(field_mul(e, field_inv(f)));
        lemma_field_element_reduced(field_mul(e, field_inv(f)));
    };

    // g * tinv = inv(e)
    assert(field_mul(g, tinv) == field_inv(e)) by {
        lemma_a_times_inv_ab_is_inv_b(g, e);
        lemma_field_mul_comm(g, e);
    };

    // B = e * K
    assert(B == field_mul(e, K)) by {
        lemma_field_mul_assoc(eg, field_inv(fh), inv_h);
        lemma_inv_of_product(fh, h);
        lemma_field_mul_comm(fh, h);
        lemma_field_mul_assoc(e, eg, field_inv(field_mul(h, fh)));
    };

    // K nonzero
    assert(K % p() != 0) by {
        if K % p() == 0 {
            lemma_mul_mod_noop_left(e as int, K as int, p() as int);
            lemma_field_element_reduced(K);
        }
    };

    // inv(B) * K = inv(e)
    assert(field_mul(field_inv(B), K) == field_inv(e)) by {
        lemma_a_times_inv_ab_is_inv_b(K, e);
        lemma_field_mul_comm(K, e);
        lemma_field_mul_comm(field_inv(B), K);
        lemma_field_mul_comm(K, field_inv(field_mul(K, e)));
    };

    // c_iad * inv(B) * K = c_iad / e
    assert(field_mul(ciad_inv_B, K) == ciad_inv_e) by {
        lemma_field_mul_assoc(c_iad, field_inv(B), K);
    };

    // invsqrt_std * K = ±c_iad/e
    assert(field_mul(invsqrt_std, K) == ciad_inv_e || field_mul(invsqrt_std, K) == field_neg(
        ciad_inv_e,
    )) by {
        if !is_negative(ciad_inv_B) {
        } else {
            lemma_field_neg_mul_left(ciad_inv_B, K);
        }
    };
}

/// Proves field_abs(s_batch) == field_abs(s_std) for both negcheck2 subcases.
proof fn lemma_no_rotation_s_matching(
    e: nat,
    g: nat,
    h: nat,
    eg: nat,
    invsqrt_std: nat,
    c_iad: nat,
    t_aff: nat,
    y_aff: nat,
    tinv: nat,
)
    requires
        y_aff == field_mul(g, field_inv(h)),
        tinv == field_inv(eg),
        h % p() != 0,
        field_mul(g, tinv) == field_inv(e),
        ({
            let K = field_mul(t_aff, field_inv(h));
            let ciad_inv_e = field_mul(c_iad, field_inv(e));
            (field_mul(invsqrt_std, K) == ciad_inv_e || field_mul(invsqrt_std, K) == field_neg(
                ciad_inv_e,
            )) && K % p() != 0
        }),
    ensures
        ({
            let den_inv = field_mul(invsqrt_std, t_aff);
            // negcheck2=false
            field_abs(field_mul(field_sub(h, g), field_mul(c_iad, field_mul(g, tinv))))
                == field_abs(
                field_mul(den_inv, field_sub(1nat, y_aff)),
            )
            // negcheck2=true
             && field_abs(
                field_mul(
                    field_sub(h, field_neg(g)),
                    field_mul(c_iad, field_mul(field_neg(g), tinv)),
                ),
            ) == field_abs(
                field_mul(den_inv, field_sub(1nat, field_neg(y_aff))),
            )
            // identities for spec unfolding
             && field_sub(1nat, field_neg(y_aff)) == field_add(1nat, y_aff) && field_sub(
                h,
                field_neg(g),
            ) == field_add(h, g) && field_mul(field_neg(g), tinv) == field_neg(field_inv(e))
                && field_mul(c_iad, field_mul(field_neg(g), tinv)) == field_neg(
                field_mul(c_iad, field_inv(e)),
            )
        }),
{
    p_gt_2();
    let ciad_inv_e = field_mul(c_iad, field_inv(e));
    let inv_h = field_inv(h);
    let K = field_mul(t_aff, inv_h);

    // 1 - y_aff = (h-g)/h
    assert(field_sub(1nat, y_aff) == field_mul(field_sub(h, g), inv_h)) by {
        lemma_inv_mul_cancel(h);
        lemma_field_mul_comm(field_inv(h), h);
        lemma_field_mul_distributes_over_sub_right(h, g, inv_h);
        lemma_field_mul_one_left(inv_h);
        lemma_field_element_reduced(inv_h);
    };

    // den_inv * (1-y_aff) = invsqrt*K * (h-g)
    let den_inv = field_mul(invsqrt_std, t_aff);
    assert(field_mul(den_inv, field_sub(1nat, y_aff)) == field_mul(
        field_mul(invsqrt_std, K),
        field_sub(h, g),
    )) by {
        lemma_field_mul_exchange(invsqrt_std, t_aff, field_sub(h, g), inv_h);
        lemma_field_mul_assoc(invsqrt_std, field_sub(h, g), K);
        lemma_field_mul_comm(field_sub(h, g), K);
        lemma_field_mul_assoc(invsqrt_std, K, field_sub(h, g));
    };

    // field_abs(s_batch) == field_abs(s_std) for negcheck2=false
    assert(field_abs(field_mul(field_sub(h, g), field_mul(c_iad, field_mul(g, tinv)))) == field_abs(
        field_mul(den_inv, field_sub(1nat, y_aff)),
    )) by {
        lemma_field_mul_comm(field_sub(h, g), field_mul(c_iad, field_mul(g, tinv)));
        lemma_field_abs_mul_sign(field_mul(invsqrt_std, K), ciad_inv_e, field_sub(h, g));
    };

    // negcheck2=true identities
    assert(field_sub(1nat, field_neg(y_aff)) == field_add(1nat, y_aff)) by {
        lemma_sub_neg_eq_add(1nat, y_aff);
    };
    assert(field_add(1nat, y_aff) == field_mul(field_add(h, g), inv_h)) by {
        lemma_inv_mul_cancel(h);
        lemma_field_mul_comm(field_inv(h), h);
        lemma_field_mul_comm(field_add(h, g), inv_h);
        lemma_field_mul_distributes_over_add(inv_h, h, g);
        lemma_field_mul_comm(inv_h, g);
    };
    assert(field_mul(field_neg(g), tinv) == field_neg(field_inv(e))) by {
        lemma_field_neg_mul_left(g, tinv);
    };
    assert(field_mul(c_iad, field_mul(field_neg(g), tinv)) == field_neg(ciad_inv_e)) by {
        lemma_field_mul_neg(c_iad, field_inv(e));
    };
    assert(field_sub(h, field_neg(g)) == field_add(h, g)) by {
        lemma_sub_neg_eq_add(h, g);
    };
    assert(field_mul(den_inv, field_sub(1nat, field_neg(y_aff))) == field_mul(
        field_mul(invsqrt_std, K),
        field_add(h, g),
    )) by {
        lemma_field_mul_exchange(invsqrt_std, t_aff, field_add(h, g), inv_h);
        lemma_field_mul_assoc(invsqrt_std, field_add(h, g), K);
        lemma_field_mul_comm(field_add(h, g), K);
        lemma_field_mul_assoc(invsqrt_std, K, field_add(h, g));
    };

    // field_abs(s_batch) == field_abs(s_std) for negcheck2=true
    assert(field_abs(
        field_mul(field_sub(h, field_neg(g)), field_mul(c_iad, field_mul(field_neg(g), tinv))),
    ) == field_abs(field_mul(den_inv, field_sub(1nat, field_neg(y_aff))))) by {
        lemma_field_mul_comm(field_add(h, g), field_neg(ciad_inv_e));
        lemma_mod_bound((ciad_inv_e * field_add(h, g)) as int, p() as int);
        lemma_field_abs_mul_sign(field_mul(invsqrt_std, K), ciad_inv_e, field_add(h, g));
        lemma_field_abs_mul_sign(field_neg(ciad_inv_e), ciad_inv_e, field_add(h, g));
    };
}

/// No-rotation case: proves batch_compress_body == ristretto_compress_affine
/// when t_aff is non-negative (negcheck1 = false, rotate = false).
proof fn lemma_no_rotation_case(
    e: nat,
    f: nat,
    g: nat,
    h: nat,
    eg: nat,
    fh: nat,
    inv: nat,
    invsqrt_std: nat,
    c_iad: nat,
    B: nat,
    t_aff: nat,
    x_aff: nat,
    y_aff: nat,
    zinv: nat,
    tinv: nat,
)
    requires
        eg == field_mul(e, g),
        fh == field_mul(f, h),
        x_aff == field_mul(e, field_inv(f)),
        y_aff == field_mul(g, field_inv(h)),
        t_aff == field_mul(x_aff, y_aff),
        zinv == field_inv(fh),
        tinv == field_inv(eg),
        invsqrt_std == field_abs(field_mul(c_iad, field_inv(B))),
        invsqrt_std == nat_invsqrt(
            field_mul(
                field_mul(field_add(1nat, y_aff), field_sub(1nat, y_aff)),
                field_square(t_aff),
            ),
        ),
        B == field_mul(field_mul(e, eg), field_inv(field_mul(h, fh))),
        e % p() != 0,
        f % p() != 0,
        g % p() != 0,
        h % p() != 0,
        eg % p() != 0,
        fh % p() != 0,
        B % p() != 0,
        c_iad == fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D),
        !is_negative(t_aff),
        ({
            let i1 = field_mul(
                invsqrt_std,
                field_mul(field_add(1nat, y_aff), field_sub(1nat, y_aff)),
            );
            let i2 = field_mul(invsqrt_std, t_aff);
            field_mul(i1, field_mul(i2, t_aff)) == 1
        }),
        zinv == field_mul(eg, inv),
        tinv == field_mul(fh, inv),
    ensures
        batch_compress_body(e, f, g, h, eg, fh, inv) == ristretto_compress_affine(x_aff, y_aff),
{
    assert(p() > 2) by {
        p_gt_2();
    };

    // Derive t_aff == eg/fh from the definitional preconditions
    assert(t_aff == field_mul(eg, field_inv(fh))) by {
        lemma_four_factor_rearrange(e, field_inv(f), g, field_inv(h));
        lemma_inv_of_product(f, h);
    };

    // Algebraic setup: batch negcheck args match standard encoding args
    lemma_no_rotation_algebraic_setup(
        e,
        f,
        g,
        h,
        eg,
        fh,
        invsqrt_std,
        c_iad,
        B,
        t_aff,
        x_aff,
        y_aff,
        zinv,
        tinv,
    );

    // s values match up to sign
    lemma_no_rotation_s_matching(e, g, h, eg, invsqrt_std, c_iad, t_aff, y_aff, tinv);

    // Standard z_inv = 1 simplifications for spec unfolding
    let u1 = field_mul(field_add(1nat, y_aff), field_sub(1nat, y_aff));
    let invsqrt = nat_invsqrt(field_mul(u1, field_square(t_aff)));
    assert(invsqrt == invsqrt_std);
    let i1 = field_mul(invsqrt, u1);
    let i2 = field_mul(invsqrt, t_aff);
    let z_inv = field_mul(i1, field_mul(i2, t_aff));
    assert(z_inv == 1nat);
    assert(field_mul(t_aff, z_inv) == t_aff && field_mul(x_aff, z_inv) == x_aff) by {
        lemma_mul_one_identity(t_aff);
        lemma_mul_one_identity(x_aff);
    };
}

/// Algebraic setup for rotation case: proves key identities connecting
/// batch and standard rotation arguments.
proof fn lemma_rotation_algebraic_setup(
    e: nat,
    f: nat,
    g: nat,
    h: nat,
    eg: nat,
    fh: nat,
    invsqrt_std: nat,
    c_iad: nat,
    B: nat,
    t_aff: nat,
    x_aff: nat,
    y_aff: nat,
    u1: nat,
    neg_one_minus_d: nat,
    zinv: nat,
    tinv: nat,
)
    requires
        eg == field_mul(e, g),
        fh == field_mul(f, h),
        x_aff == field_mul(e, field_inv(f)),
        y_aff == field_mul(g, field_inv(h)),
        t_aff == field_mul(eg, field_inv(fh)),
        u1 == field_mul(field_add(1nat, y_aff), field_sub(1nat, y_aff)),
        zinv == field_inv(fh),
        tinv == field_inv(eg),
        invsqrt_std == field_abs(field_mul(c_iad, field_inv(B))),
        B == field_mul(field_mul(e, eg), field_inv(field_mul(h, fh))),
        field_mul(field_square(c_iad), neg_one_minus_d) == 1,
        field_mul(u1, field_square(t_aff)) == field_mul(neg_one_minus_d, field_square(B)),
        e % p() != 0,
        f % p() != 0,
        g % p() != 0,
        h % p() != 0,
        eg % p() != 0,
        fh % p() != 0,
        B % p() != 0,
        neg_one_minus_d % p() != 0,
        t_aff % p() != 0,
    ensures
        field_mul(field_mul(field_mul(f, sqrt_m1()), g), zinv) == field_mul(sqrt_m1(), y_aff),
        field_mul(e, tinv) == field_inv(g),
        field_mul(field_neg(e), tinv) == field_neg(field_inv(g)),
        ({
            let enchanted = field_mul(field_mul(invsqrt_std, u1), c_iad);
            enchanted == field_mul(f, field_inv(g)) || enchanted == field_neg(
                field_mul(f, field_inv(g)),
            )
        }),
{
    p_gt_2();

    // batch negcheck2 arg: (f*i)*g * inv(f*h) = (i*g)*f * inv(h*f) = i*g*inv(h) = i*y_aff
    let i = sqrt_m1();
    assert(field_mul(field_mul(field_mul(f, i), g), zinv) == field_mul(i, y_aff)) by {
        // Rewrite (f*i)*g as (i*g)*f
        lemma_field_mul_comm(f, i);
        lemma_field_mul_assoc(i, f, g);
        lemma_field_mul_comm(f, g);
        lemma_field_mul_assoc(i, g, f);
        // Rewrite f*h = h*f for cancel
        lemma_field_mul_comm(f, h);
        // Cancel f: (i*g)*f * inv(h*f) = (i*g) * inv(h)
        lemma_cancel_common_factor(field_mul(i, g), h, f);
        // (i*g)*inv(h) = i*(g*inv(h)) = i*y_aff
        lemma_field_mul_assoc(i, g, field_inv(h));
    };

    // e * tinv = inv(g)
    assert(field_mul(e, tinv) == field_inv(g)) by {
        lemma_a_times_inv_ab_is_inv_b(e, g);
    };

    // -e * tinv = -inv(g)
    assert(field_mul(field_neg(e), tinv) == field_neg(field_inv(g))) by {
        lemma_field_neg_mul_left(e, tinv);
    };

    // Key identity: c_iad² * u1 * inv(B) = f/g
    // Proof: u1*t² = (-1-d)*B² and c_iad²*(-1-d) = 1
    //   => c_iad²*u1*t² = B²
    //   => c_iad²*u1 = B²*inv(t²)
    //   => c_iad²*u1*inv(B) = B*inv(t²) = f/g

    // Step: B * inv(t²) = f/g
    // B = e*eg*inv(h*fh), t_aff = eg*inv(fh)
    // B*inv(t²) = e*eg*inv(h*fh) * fh²*inv(eg²) = ... = f/g
    // We prove this indirectly through cancellation:
    //   B * g = f * t²

    // Step 1: c_iad²*u1*t² = c_iad²*(-1-d)*B² = 1*B² = B²
    assert(field_mul(field_square(c_iad), field_mul(u1, field_square(t_aff))) == field_square(B))
        by {
        lemma_field_mul_assoc(field_square(c_iad), u1, field_square(t_aff));
        lemma_field_mul_assoc(field_square(c_iad), neg_one_minus_d, field_square(B));
        lemma_field_mul_one_left(field_square(B));
        lemma_field_element_reduced(field_square(B));
    };

    // Step 2: B*g = f*t² (by algebraic cancellation)
    // B = e*eg*inv(h*fh), so B*g = e*eg*g*inv(h*fh) = eg²*inv(h*fh)
    // t² = eg²*inv(fh²), so f*t² = f*eg²*inv(fh²) = eg²*f*inv(fh²)
    // h*fh = h*(f*h) = f*h² and (fh)² = (f*h)² = f²*h²
    // So B*g = eg²*inv(f*h²) and f*t² = eg²*f*inv(f²*h²) = eg²*inv(f*h²)
    assert(field_mul(B, g) == field_mul(f, field_square(t_aff))) by {
        let eg2 = field_square(eg);
        let hfh = field_mul(h, fh);
        let fh2 = field_square(fh);

        // LHS: B*g = ((e*eg)*inv(h*fh))*g => eg²*inv(f*h²)
        // Rearrange: (e*eg)*inv(hfh)*g => ((e*eg)*g)*inv(hfh)
        lemma_field_mul_assoc(field_mul(e, eg), field_inv(hfh), g);
        lemma_field_mul_comm(field_inv(hfh), g);
        lemma_field_mul_assoc(field_mul(e, eg), g, field_inv(hfh));
        // (e*eg)*g = e²*g² = eg²
        lemma_field_mul_assoc(e, e, g);
        lemma_field_mul_assoc(field_square(e), g, g);
        lemma_product_of_squares_eq_square_of_product(e, g);
        // h*fh = h*(f*h) = (f*h)*h = f*(h*h) = f*h²
        lemma_field_mul_comm(h, fh);
        lemma_field_mul_assoc(f, h, h);

        // RHS: f*t² = f*eg²*inv(fh²) => eg²*inv(f*h²)
        // t² = (eg/fh)² = eg²/fh²
        lemma_quotient_of_squares(eg, fh);
        // f * (eg² * inv(fh²)) => eg² * (f * inv(fh²))
        lemma_field_mul_assoc(f, eg2, field_inv(fh2));
        lemma_field_mul_comm(f, eg2);
        lemma_field_mul_assoc(eg2, f, field_inv(fh2));
        // fh² = (f*h)² = f²*h², and f²*h² = f*(f*h²)
        lemma_product_of_squares_eq_square_of_product(f, h);
        lemma_field_mul_assoc(f, f, field_square(h));
        // f * inv(f*(f*h²)) = inv(f*h²)
        lemma_a_times_inv_ab_is_inv_b(f, field_mul(f, field_square(h)));
    };

    // Step 3: c_iad²*u1*inv(B) = f/g
    // From step 1: c_iad²*u1 = B²/t² (multiply step 1 by inv(t²))
    // From step 2: B*g = f*t², so B*inv(t²) = f*inv(g) (by cancel_common_factor)
    // So c_iad²*u1*inv(B) = B²/t²*inv(B) = B/t² = f/g
    // t² nonzero (since t_aff nonzero in a field)
    let t2 = field_square(t_aff);
    assert(t2 % p() != 0) by {
        lemma_nonzero_product(t_aff, t_aff);
        lemma_mod_bound((t_aff * t_aff) as int, p() as int);
        lemma_small_mod(t2, p());
    };

    let c2u1 = field_mul(field_square(c_iad), u1);
    assert(field_mul(c2u1, field_inv(B)) == field_mul(f, field_inv(g))) by {
        // Link c2u1*t2 to Step 1: c2u1*t2 = c_iad²*(u1*t2) = B²
        lemma_field_mul_assoc(field_square(c_iad), u1, t2);

        // From B*g = f*t², cancel to get B*inv(t²) = f*inv(g):
        // (B*g)*inv(t²*g) = B*inv(t²) and (f*t²)*inv(g*t²) = f*inv(g)
        lemma_cancel_common_factor(B, t2, g);
        lemma_cancel_common_factor(f, g, t2);
        lemma_field_mul_comm(t2, g);

        // From c2u1*t² = B²: cancel to get c2u1*inv(B) = B*inv(t²):
        // (c2u1*t²)*inv(B*t²) = c2u1*inv(B) and (B*B)*inv(t²*B) = B*inv(t²)
        lemma_cancel_common_factor(c2u1, B, t2);
        lemma_cancel_common_factor(B, t2, B);
        lemma_field_mul_comm(B, t2);
    };

    // Step 4: invsqrt_std * u1 * c_iad = ±f/g
    let enchanted = field_mul(field_mul(invsqrt_std, u1), c_iad);
    assert(enchanted == field_mul(f, field_inv(g)) || enchanted == field_neg(
        field_mul(f, field_inv(g)),
    )) by {
        // invsqrt_std = field_abs(c_iad*inv(B)) = ±c_iad*inv(B)
        // enchanted = (±c_iad*inv(B))*u1*c_iad
        // Positive case: c_iad*inv(B)*u1*c_iad = c_iad*(inv(B)*u1)*c_iad
        //   = c_iad*(u1*inv(B))*c_iad [comm] = (c_iad*u1*inv(B))*c_iad [assoc]
        //   = Wait, need c_iad²*u1*inv(B) = (c_iad*c_iad)*(u1*inv(B))
        //   enchanted = (c_iad*inv(B))*u1*c_iad
        //   = ((c_iad*inv(B))*u1)*c_iad
        //   = (c_iad*(inv(B)*u1))*c_iad [assoc]
        //   = (c_iad*(u1*inv(B)))*c_iad [comm on inv(B),u1]
        //   = c_iad*u1*inv(B)*c_iad [flatten]
        //   Hmm, this is c_iad * (u1*inv(B)) * c_iad, not c_iad² * u1 * inv(B)
        //   Need to rearrange to c_iad*c_iad*u1*inv(B) = field_square(c_iad)*u1*inv(B)
        let ciad_inv_B = field_mul(c_iad, field_inv(B));
        if !is_negative(ciad_inv_B) {
            // invsqrt_std = ciad_inv_B
            // enchanted = ciad_inv_B * u1 * c_iad
            //   = c_iad * inv(B) * u1 * c_iad
            //   = (c_iad * (inv(B) * u1)) * c_iad  [assoc]
            //   = (c_iad * (u1 * inv(B))) * c_iad  [comm on inv(B), u1]
            //   Need to get to c_iad * c_iad * u1 * inv(B) = c_iad² * u1 * inv(B)
            lemma_field_mul_assoc(c_iad, field_inv(B), u1);
            lemma_field_mul_comm(field_inv(B), u1);
            // Now: ciad_inv_B * u1 = c_iad * (u1 * inv(B))
            lemma_field_mul_assoc(c_iad, u1, field_inv(B));
            // c_iad * (u1 * inv(B)) = (c_iad * u1) * inv(B)
            // enchanted = ((c_iad * u1) * inv(B)) * c_iad
            lemma_field_mul_assoc(field_mul(c_iad, u1), field_inv(B), c_iad);
            lemma_field_mul_comm(field_inv(B), c_iad);
            lemma_field_mul_assoc(field_mul(c_iad, u1), c_iad, field_inv(B));
            // = ((c_iad * u1) * c_iad) * inv(B)
            lemma_field_mul_assoc(c_iad, u1, c_iad);
            lemma_field_mul_comm(u1, c_iad);
            lemma_field_mul_assoc(c_iad, c_iad, u1);
            // (c_iad * c_iad) * u1 = field_square(c_iad) * u1
            lemma_field_mul_assoc(field_square(c_iad), u1, field_inv(B));
        } else {
            // invsqrt_std = field_neg(ciad_inv_B)
            // enchanted = field_neg(ciad_inv_B) * u1 * c_iad = -(c_iad²*u1*inv(B)) = -f/g
            lemma_field_neg_mul_left(ciad_inv_B, u1);
            // field_neg(ciad_inv_B) * u1 = field_neg(ciad_inv_B * u1)
            lemma_field_neg_mul_left(field_mul(ciad_inv_B, u1), c_iad);
            // field_neg(ciad_inv_B * u1) * c_iad = field_neg((ciad_inv_B * u1) * c_iad)
            // Now (ciad_inv_B * u1) * c_iad = c_iad² * u1 * inv(B) = f/g (same rearrangement)
            lemma_field_mul_assoc(c_iad, field_inv(B), u1);
            lemma_field_mul_comm(field_inv(B), u1);
            lemma_field_mul_assoc(c_iad, u1, field_inv(B));
            lemma_field_mul_assoc(field_mul(c_iad, u1), field_inv(B), c_iad);
            lemma_field_mul_comm(field_inv(B), c_iad);
            lemma_field_mul_assoc(field_mul(c_iad, u1), c_iad, field_inv(B));
            lemma_field_mul_assoc(c_iad, u1, c_iad);
            lemma_field_mul_comm(u1, c_iad);
            lemma_field_mul_assoc(c_iad, c_iad, u1);
            lemma_field_mul_assoc(field_square(c_iad), u1, field_inv(B));
        }
    };
}

/// Helper: (a*i)*i = -a in the field, since i²=-1.
proof fn lemma_mul_i_squared_is_neg(a: nat)
    ensures
        field_mul(field_mul(a, sqrt_m1()), sqrt_m1()) == field_neg(a),
{
    let pn = p();
    assert(pn > 2) by {
        p_gt_2();
    };
    let i = sqrt_m1();
    assert(field_mul(field_mul(a, i), i) == field_mul(a, field_mul(i, i))) by {
        lemma_field_mul_assoc(a, i, i);
    };
    assert(field_mul(i, i) == field_neg(1nat)) by {
        axiom_sqrt_m1_squared();
        lemma_small_mod(1nat, pn);
        lemma_small_mod((pn - 1) as nat, pn);
    };
    assert(field_mul(a, field_neg(1nat)) == field_neg(a)) by {
        lemma_field_mul_comm(a, field_neg(1nat));
        lemma_neg_one_times_is_neg(a);
    };
}

/// Helper: 1 - (e/f)*i = (f - e*i)/f, i.e.,
/// field_sub(1, field_mul(field_mul(e, inv(f)), i)) = field_mul(field_sub(f, e*i), inv(f)).
proof fn lemma_one_minus_x_times_i(e: nat, f: nat)
    requires
        f % p() != 0,
    ensures
        field_sub(1nat, field_mul(field_mul(e, field_inv(f)), sqrt_m1())) == field_mul(
            field_sub(f, field_mul(e, sqrt_m1())),
            field_inv(f),
        ),
{
    assert(p() > 2) by {
        p_gt_2();
    };
    let i = sqrt_m1();
    let inv_f = field_inv(f);
    // 1 = f·inv(f)
    assert(1nat == field_mul(f, inv_f)) by {
        lemma_inv_mul_cancel(f);
        lemma_field_mul_comm(inv_f, f);
    };
    // (e·inv(f))·i = (e·i)·inv(f)
    assert(field_mul(field_mul(e, inv_f), i) == field_mul(field_mul(e, i), inv_f)) by {
        lemma_field_mul_assoc(e, inv_f, i);
        lemma_field_mul_comm(inv_f, i);
        lemma_field_mul_assoc(e, i, inv_f);
    };
    // f·inv(f) − (e·i)·inv(f) = (f − e·i)·inv(f)
    assert(field_sub(field_mul(f, inv_f), field_mul(field_mul(e, i), inv_f)) == field_mul(
        field_sub(f, field_mul(e, i)),
        inv_f,
    )) by {
        lemma_reverse_distribute_sub(f, field_mul(e, i), inv_f);
    };
}

/// Helper: 1 + (e/f)*i = (f + e*i)/f, i.e.,
/// field_add(1, field_mul(field_mul(e, inv(f)), i)) = field_mul(field_add(f, e*i), inv(f)).
proof fn lemma_one_plus_x_times_i(e: nat, f: nat)
    requires
        f % p() != 0,
    ensures
        field_add(1nat, field_mul(field_mul(e, field_inv(f)), sqrt_m1())) == field_mul(
            field_add(f, field_mul(e, sqrt_m1())),
            field_inv(f),
        ),
{
    assert(p() > 2) by {
        p_gt_2();
    };
    let i = sqrt_m1();
    let inv_f = field_inv(f);
    // 1 = f·inv(f)
    assert(1nat == field_mul(f, inv_f)) by {
        lemma_inv_mul_cancel(f);
        lemma_field_mul_comm(inv_f, f);
    };
    // (e·inv(f))·i = (e·i)·inv(f)
    assert(field_mul(field_mul(e, inv_f), i) == field_mul(field_mul(e, i), inv_f)) by {
        lemma_field_mul_assoc(e, inv_f, i);
        lemma_field_mul_comm(inv_f, i);
        lemma_field_mul_assoc(e, i, inv_f);
    };
    // f·inv(f) + (e·i)·inv(f) = inv(f)·(f + e·i) = (f + e·i)·inv(f)
    assert(field_add(field_mul(f, inv_f), field_mul(field_mul(e, i), inv_f)) == field_mul(
        field_add(f, field_mul(e, i)),
        inv_f,
    )) by {
        lemma_field_mul_comm(field_add(f, field_mul(e, i)), inv_f);
        lemma_field_mul_distributes_over_add(inv_f, f, field_mul(e, i));
        lemma_field_mul_comm(inv_f, f);
        lemma_field_mul_comm(inv_f, field_mul(e, i));
    };
}

/// Proves field_abs(s_batch) == field_abs(s_std) for both negcheck2 subcases
/// in the rotation case.
proof fn lemma_rotation_s_matching(
    e: nat,
    f: nat,
    g: nat,
    h: nat,
    invsqrt_std: nat,
    c_iad: nat,
    t_aff: nat,
    x_aff: nat,
    y_aff: nat,
    u1: nat,
    tinv: nat,
)
    requires
        x_aff == field_mul(e, field_inv(f)),
        y_aff == field_mul(g, field_inv(h)),
        field_mul(e, tinv) == field_inv(g),
        field_mul(field_neg(e), tinv) == field_neg(field_inv(g)),
        ({
            let enchanted = field_mul(field_mul(invsqrt_std, u1), c_iad);
            enchanted == field_mul(f, field_inv(g)) || enchanted == field_neg(
                field_mul(f, field_inv(g)),
            )
        }),
        e % p() != 0,
        f % p() != 0,
        g % p() != 0,
        h % p() != 0,
    ensures
        ({
            let i = sqrt_m1();
            let h_rot = field_mul(f, i);
            let enchanted = field_mul(field_mul(invsqrt_std, u1), c_iad);
            // negcheck2=false: g_final = field_neg(e)
            field_abs(
                field_mul(
                    field_sub(h_rot, field_neg(e)),
                    field_mul(i, field_mul(field_neg(e), tinv)),
                ),
            ) == field_abs(
                field_mul(enchanted, field_sub(1nat, field_mul(x_aff, i))),
            )
            // negcheck2=true: g_final = e (= field_neg(field_neg(e)))
             && field_abs(field_mul(field_sub(h_rot, e), field_mul(i, field_mul(e, tinv))))
                == field_abs(field_mul(enchanted, field_sub(1nat, field_neg(field_mul(x_aff, i)))))
        }),
{
    p_gt_2();
    let i = sqrt_m1();
    let inv_g = field_inv(g);
    let inv_f = field_inv(f);
    let enchanted = field_mul(field_mul(invsqrt_std, u1), c_iad);
    let f_over_g = field_mul(f, inv_g);
    let C_neg = field_sub(f, field_mul(e, i));
    let C_pos = field_add(f, field_mul(e, i));

    // === negcheck2=false case ===
    // batch s = (f*i + e) * (-i*inv(g)) = (f - e*i) * inv(g)
    // std s = enchanted * (1 - x*i) = ±(f - e*i) * inv(g)

    // Batch side: sub(f*i, neg(e)) = add(f*i, e) and neg(e)*tinv = -inv(g)
    assert(field_sub(field_mul(f, i), field_neg(e)) == field_add(field_mul(f, i), e)) by {
        lemma_sub_neg_eq_add(field_mul(f, i), e);
    };
    assert(field_mul(i, field_mul(field_neg(e), tinv)) == field_neg(field_mul(i, inv_g))) by {
        lemma_field_mul_neg(i, inv_g);
    };

    // (f*i + e) * i = -f + e*i = neg(C_neg)
    assert(field_mul(field_add(field_mul(f, i), e), i) == field_neg(C_neg)) by {
        lemma_field_mul_comm(field_add(field_mul(f, i), e), i);
        lemma_field_mul_distributes_over_add(i, field_mul(f, i), e);
        lemma_field_mul_comm(i, e);
        // i*(f*i) = (f*i)*i = -f
        lemma_mul_i_squared_is_neg(f);
        lemma_field_mul_comm(i, field_mul(f, i));
        // add(-f, e*i) = add(e*i, -f) = sub(e*i, f) = neg(sub(f, e*i)) = neg(C_neg)
        lemma_field_add_comm(field_neg(f), field_mul(e, i));
        lemma_field_sub_eq_add_neg(field_mul(e, i), f);
        lemma_field_sub_antisymmetric(f, field_mul(e, i));
    };

    // batch s = neg(neg(C_neg) * inv(g)) = neg(neg(C_neg*inv(g))) = C_neg*inv(g)
    let batch_s_false = field_mul(
        field_sub(field_mul(f, i), field_neg(e)),
        field_mul(i, field_mul(field_neg(e), tinv)),
    );
    assert(batch_s_false == field_mul(C_neg, inv_g)) by {
        // batch_s = add(fi, e) * neg(i*inv(g))
        //         = neg(add(fi, e) * (i*inv(g)))
        lemma_field_mul_neg(field_add(field_mul(f, i), e), field_mul(i, inv_g));
        // add(fi, e) * (i*inv(g)) = (add(fi,e)*i) * inv(g)
        lemma_field_mul_assoc(field_add(field_mul(f, i), e), i, inv_g);
        // (add(fi,e)*i) = neg(C_neg)
        // neg(C_neg) * inv(g) = neg(C_neg*inv(g))
        lemma_field_neg_mul_left(C_neg, inv_g);
        // batch_s = neg(neg(C_neg*inv(g))) = C_neg*inv(g)
        lemma_field_neg_neg(field_mul(C_neg, inv_g));
        lemma_mod_bound((C_neg * inv_g) as int, p() as int);
        lemma_small_mod(field_mul(C_neg, inv_g), p());
    };

    // Std side: 1 - x*i = C_neg*inv(f), so enchanted*(C_neg*inv(f)) = ±C_neg*inv(g)
    let std_inner_false = field_sub(1nat, field_mul(x_aff, i));
    assert(std_inner_false == field_mul(C_neg, inv_f)) by {
        lemma_one_minus_x_times_i(e, f);
    };

    // enchanted * (C_neg * inv(f)):
    // If enchanted = f/g: (f*inv(g))*(C_neg*inv(f)) = (f*inv(f))*(C_neg*inv(g)) = C_neg*inv(g)
    // If enchanted = neg(f/g): neg(C_neg*inv(g))
    let std_s_false = field_mul(enchanted, std_inner_false);
    assert(std_s_false == field_mul(C_neg, inv_g) || std_s_false == field_neg(
        field_mul(C_neg, inv_g),
    )) by {
        if enchanted == f_over_g {
            lemma_field_mul_exchange(f, inv_g, inv_f, C_neg);
            lemma_field_mul_comm(inv_f, C_neg);
            lemma_inv_mul_cancel(f);
            lemma_field_mul_comm(inv_f, f);
            lemma_field_mul_one_left(field_mul(inv_g, C_neg));
            lemma_mod_bound((inv_g * C_neg) as int, p() as int);
            lemma_small_mod(field_mul(inv_g, C_neg), p());
            lemma_field_mul_comm(inv_g, C_neg);
        } else {
            lemma_field_neg_mul_left(f_over_g, field_mul(C_neg, inv_f));
            lemma_field_mul_exchange(f, inv_g, inv_f, C_neg);
            lemma_field_mul_comm(inv_f, C_neg);
            lemma_inv_mul_cancel(f);
            lemma_field_mul_comm(inv_f, f);
            lemma_field_mul_one_left(field_mul(inv_g, C_neg));
            lemma_mod_bound((inv_g * C_neg) as int, p() as int);
            lemma_small_mod(field_mul(inv_g, C_neg), p());
            lemma_field_mul_comm(inv_g, C_neg);
        }
    };

    // field_abs(batch_s) == field_abs(std_s) for negcheck2=false
    assert(field_abs(batch_s_false) == field_abs(std_s_false)) by {
        if std_s_false == field_mul(C_neg, inv_g) {
        } else {
            lemma_mod_bound((C_neg * inv_g) as int, p() as int);
            lemma_small_mod(field_mul(C_neg, inv_g), p());
            lemma_field_abs_neg(field_mul(C_neg, inv_g));
        }
    };

    // === negcheck2=true case ===
    // batch s = (f*i - e) * (i * inv(g)) = neg(C_pos) * inv(g)
    // std s = enchanted * (1 + x*i) = ±C_pos * inv(g)

    // sub(f*i, e) = f*i - e
    // (f*i - e)*i = (f*i)*i - e*i = -f - e*i = neg(f + e*i) = neg(C_pos)
    assert(field_mul(field_sub(field_mul(f, i), e), i) == field_neg(C_pos)) by {
        // (f*i - e)*i = (f*i)*i - e*i [by distrib]
        lemma_field_mul_distributes_over_sub_right(field_mul(f, i), e, i);
        // (f*i)*i = -f
        lemma_mul_i_squared_is_neg(f);
        // sub(-f, e*i) = neg(sub(e*i, -f)) = neg(add(e*i, f)) = neg(C_pos)
        lemma_field_sub_antisymmetric(field_mul(e, i), field_neg(f));
        lemma_sub_neg_eq_add(field_mul(e, i), f);
        lemma_field_add_comm(field_mul(e, i), f);
    };

    // batch s = (f*i - e) * i * inv(g) = neg(C_pos) * inv(g) = neg(C_pos*inv(g))
    let batch_s_true = field_mul(field_sub(field_mul(f, i), e), field_mul(i, field_mul(e, tinv)));
    assert(batch_s_true == field_neg(field_mul(C_pos, inv_g))) by {
        lemma_field_mul_assoc(field_sub(field_mul(f, i), e), i, inv_g);
        lemma_field_neg_mul_left(C_pos, inv_g);
    };

    // Std side: sub(1, neg(x*i)) = add(1, x*i) = C_pos*inv(f)
    assert(field_sub(1nat, field_neg(field_mul(x_aff, i))) == field_add(1nat, field_mul(x_aff, i)))
        by {
        lemma_sub_neg_eq_add(1nat, field_mul(x_aff, i));
    };
    let std_inner_true = field_add(1nat, field_mul(x_aff, i));
    assert(std_inner_true == field_mul(C_pos, inv_f)) by {
        lemma_one_plus_x_times_i(e, f);
    };

    // enchanted * C_pos*inv(f) = ±C_pos*inv(g)
    let std_s_true = field_mul(enchanted, std_inner_true);
    assert(std_s_true == field_mul(C_pos, inv_g) || std_s_true == field_neg(
        field_mul(C_pos, inv_g),
    )) by {
        if enchanted == f_over_g {
            lemma_field_mul_exchange(f, inv_g, inv_f, C_pos);
            lemma_field_mul_comm(inv_f, C_pos);
            lemma_inv_mul_cancel(f);
            lemma_field_mul_comm(inv_f, f);
            lemma_field_mul_one_left(field_mul(inv_g, C_pos));
            lemma_mod_bound((inv_g * C_pos) as int, p() as int);
            lemma_small_mod(field_mul(inv_g, C_pos), p());
            lemma_field_mul_comm(inv_g, C_pos);
        } else {
            lemma_field_neg_mul_left(f_over_g, field_mul(C_pos, inv_f));
            lemma_field_mul_exchange(f, inv_g, inv_f, C_pos);
            lemma_field_mul_comm(inv_f, C_pos);
            lemma_inv_mul_cancel(f);
            lemma_field_mul_comm(inv_f, f);
            lemma_field_mul_one_left(field_mul(inv_g, C_pos));
            lemma_mod_bound((inv_g * C_pos) as int, p() as int);
            lemma_small_mod(field_mul(inv_g, C_pos), p());
            lemma_field_mul_comm(inv_g, C_pos);
        }
    };

    // field_abs(batch_s) == field_abs(std_s) for negcheck2=true
    assert(field_abs(batch_s_true) == field_abs(std_s_true)) by {
        // batch = neg(C_pos*inv(g)), std = ±C_pos*inv(g)
        // field_abs(neg(X)) = field_abs(X) = field_abs(±X)
        lemma_mod_bound((C_pos * inv_g) as int, p() as int);
        lemma_small_mod(field_mul(C_pos, inv_g), p());
        lemma_field_abs_neg(field_mul(C_pos, inv_g));
        if std_s_true == field_neg(field_mul(C_pos, inv_g)) {
        } else {
        }
    };
}

/// Rotation case: proves batch_compress_body == ristretto_compress_affine
/// when t_aff is negative (negcheck1 = true, rotate = true).
proof fn lemma_rotation_case(
    e: nat,
    f: nat,
    g: nat,
    h: nat,
    eg: nat,
    fh: nat,
    inv: nat,
    invsqrt_std: nat,
    c_iad: nat,
    B: nat,
    t_aff: nat,
    x_aff: nat,
    y_aff: nat,
    u1: nat,
    neg_one_minus_d: nat,
    zinv: nat,
    tinv: nat,
)
    requires
        eg == field_mul(e, g),
        fh == field_mul(f, h),
        x_aff == field_mul(e, field_inv(f)),
        y_aff == field_mul(g, field_inv(h)),
        t_aff == field_mul(x_aff, y_aff),
        u1 == field_mul(field_add(1nat, y_aff), field_sub(1nat, y_aff)),
        zinv == field_inv(fh),
        tinv == field_inv(eg),
        invsqrt_std == field_abs(field_mul(c_iad, field_inv(B))),
        invsqrt_std == nat_invsqrt(field_mul(u1, field_square(t_aff))),
        B == field_mul(field_mul(e, eg), field_inv(field_mul(h, fh))),
        field_mul(field_square(c_iad), neg_one_minus_d) == 1,
        field_mul(u1, field_square(t_aff)) == field_mul(neg_one_minus_d, field_square(B)),
        e % p() != 0,
        f % p() != 0,
        g % p() != 0,
        h % p() != 0,
        eg % p() != 0,
        fh % p() != 0,
        B % p() != 0,
        neg_one_minus_d % p() != 0,
        c_iad == fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D),
        is_negative(t_aff),
        ({
            let i1 = field_mul(invsqrt_std, u1);
            let i2 = field_mul(invsqrt_std, t_aff);
            field_mul(i1, field_mul(i2, t_aff)) == 1
        }),
        zinv == field_mul(eg, inv),
        tinv == field_mul(fh, inv),
    ensures
        batch_compress_body(e, f, g, h, eg, fh, inv) == ristretto_compress_affine(x_aff, y_aff),
{
    p_gt_2();

    // Derive t_aff == eg/fh from the definitional preconditions
    assert(t_aff == field_mul(eg, field_inv(fh))) by {
        lemma_four_factor_rearrange(e, field_inv(f), g, field_inv(h));
        lemma_inv_of_product(f, h);
    };

    assert(t_aff % p() != 0) by {
        if t_aff % p() == 0 {
            lemma_small_mod(0nat, p());
        }
    };
    assert(batch_compress_body(e, f, g, h, eg, fh, inv) == ristretto_compress_affine(x_aff, y_aff))
        by {
        lemma_rotation_case_body(
            e,
            f,
            g,
            h,
            eg,
            fh,
            inv,
            invsqrt_std,
            c_iad,
            B,
            t_aff,
            x_aff,
            y_aff,
            u1,
            neg_one_minus_d,
            zinv,
            tinv,
        );
    };
}

/// Carries out the full rotation case proof: algebraic setup, s matching,
/// z_inv=1 simplifications, branch matching, and final spec equality.
proof fn lemma_rotation_case_body(
    e: nat,
    f: nat,
    g: nat,
    h: nat,
    eg: nat,
    fh: nat,
    inv: nat,
    invsqrt_std: nat,
    c_iad: nat,
    B: nat,
    t_aff: nat,
    x_aff: nat,
    y_aff: nat,
    u1: nat,
    neg_one_minus_d: nat,
    zinv: nat,
    tinv: nat,
)
    requires
        eg == field_mul(e, g),
        fh == field_mul(f, h),
        x_aff == field_mul(e, field_inv(f)),
        y_aff == field_mul(g, field_inv(h)),
        t_aff == field_mul(x_aff, y_aff),
        t_aff == field_mul(eg, field_inv(fh)),
        u1 == field_mul(field_add(1nat, y_aff), field_sub(1nat, y_aff)),
        zinv == field_inv(fh),
        tinv == field_inv(eg),
        invsqrt_std == field_abs(field_mul(c_iad, field_inv(B))),
        invsqrt_std == nat_invsqrt(field_mul(u1, field_square(t_aff))),
        B == field_mul(field_mul(e, eg), field_inv(field_mul(h, fh))),
        field_mul(field_square(c_iad), neg_one_minus_d) == 1,
        field_mul(u1, field_square(t_aff)) == field_mul(neg_one_minus_d, field_square(B)),
        e % p() != 0,
        f % p() != 0,
        g % p() != 0,
        h % p() != 0,
        eg % p() != 0,
        fh % p() != 0,
        B % p() != 0,
        neg_one_minus_d % p() != 0,
        t_aff % p() != 0,
        c_iad == fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D),
        is_negative(t_aff),
        ({
            let i1 = field_mul(invsqrt_std, u1);
            let i2 = field_mul(invsqrt_std, t_aff);
            field_mul(i1, field_mul(i2, t_aff)) == 1
        }),
        field_mul(eg, field_mul(eg, inv)) == t_aff,
        zinv == field_mul(eg, inv),
        tinv == field_mul(fh, inv),
    ensures
        batch_compress_body(e, f, g, h, eg, fh, inv) == ristretto_compress_affine(x_aff, y_aff),
{
    p_gt_2();

    // Algebraic setup: negcheck2 argument simplification and enchanted identity
    assert(field_mul(field_mul(field_mul(f, sqrt_m1()), g), zinv) == field_mul(sqrt_m1(), y_aff)
        && field_mul(e, tinv) == field_inv(g) && field_mul(field_neg(e), tinv) == field_neg(
        field_inv(g),
    ) && ({
        let enchanted = field_mul(field_mul(invsqrt_std, u1), c_iad);
        enchanted == field_mul(f, field_inv(g)) || enchanted == field_neg(
            field_mul(f, field_inv(g)),
        )
    })) by {
        lemma_rotation_algebraic_setup(
            e,
            f,
            g,
            h,
            eg,
            fh,
            invsqrt_std,
            c_iad,
            B,
            t_aff,
            x_aff,
            y_aff,
            u1,
            neg_one_minus_d,
            zinv,
            tinv,
        );
    };

    // S values match for both negcheck2 subcases
    assert({
        let i = sqrt_m1();
        let h_rot = field_mul(f, i);
        let enchanted = field_mul(field_mul(invsqrt_std, u1), c_iad);
        field_abs(
            field_mul(field_sub(h_rot, field_neg(e)), field_mul(i, field_mul(field_neg(e), tinv))),
        ) == field_abs(field_mul(enchanted, field_sub(1nat, field_mul(x_aff, i)))) && field_abs(
            field_mul(field_sub(h_rot, e), field_mul(i, field_mul(e, tinv))),
        ) == field_abs(field_mul(enchanted, field_sub(1nat, field_neg(field_mul(x_aff, i)))))
    }) by {
        lemma_rotation_s_matching(e, f, g, h, invsqrt_std, c_iad, t_aff, x_aff, y_aff, u1, tinv);
    };

    // z_inv = 1 simplifications
    let invsqrt = nat_invsqrt(field_mul(u1, field_square(t_aff)));
    assert(invsqrt == invsqrt_std);
    let i1 = field_mul(invsqrt, u1);
    let i2 = field_mul(invsqrt, t_aff);
    let z_inv = field_mul(i1, field_mul(i2, t_aff));
    assert(z_inv == 1nat);
    assert(field_mul(t_aff, z_inv) == t_aff && field_mul(x_aff, z_inv) == x_aff) by {
        lemma_mul_one_identity(t_aff);
        lemma_mul_one_identity(x_aff);
    };

    // Final: batch and standard specs agree
    assert(batch_compress_body(e, f, g, h, eg, fh, inv) == ristretto_compress_affine(x_aff, y_aff))
        by {
        lemma_rotation_case_final(
            e,
            f,
            g,
            h,
            eg,
            fh,
            inv,
            invsqrt_std,
            c_iad,
            t_aff,
            x_aff,
            y_aff,
            u1,
            zinv,
            tinv,
        );
    };
}

/// Final step of the rotation case: given algebraic setup results, s_matching
/// results, and z_inv=1 simplifications, proves the spec functions agree.
proof fn lemma_rotation_case_final(
    e: nat,
    f: nat,
    g: nat,
    h: nat,
    eg: nat,
    fh: nat,
    inv: nat,
    invsqrt_std: nat,
    c_iad: nat,
    t_aff: nat,
    x_aff: nat,
    y_aff: nat,
    u1: nat,
    zinv: nat,
    tinv: nat,
)
    requires
        eg == field_mul(e, g),
        fh == field_mul(f, h),
        x_aff == field_mul(e, field_inv(f)),
        y_aff == field_mul(g, field_inv(h)),
        t_aff == field_mul(x_aff, y_aff),
        t_aff == field_mul(eg, field_inv(fh)),
        u1 == field_mul(field_add(1nat, y_aff), field_sub(1nat, y_aff)),
        zinv == field_inv(fh),
        tinv == field_inv(eg),
        zinv == field_mul(eg, inv),
        tinv == field_mul(fh, inv),
        invsqrt_std == nat_invsqrt(field_mul(u1, field_square(t_aff))),
        c_iad == fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D),
        e % p() != 0,
        f % p() != 0,
        g % p() != 0,
        h % p() != 0,
        eg % p() != 0,
        fh % p() != 0,
        t_aff % p() != 0,
        is_negative(t_aff),
        field_mul(eg, zinv) == t_aff,
        // z_inv = 1 and simplifications
        ({
            let i1 = field_mul(invsqrt_std, u1);
            let i2 = field_mul(invsqrt_std, t_aff);
            let z_inv = field_mul(i1, field_mul(i2, t_aff));
            z_inv == 1nat
        }),
        // algebraic_setup result: negcheck2 arg simplification
        field_mul(field_mul(field_mul(f, sqrt_m1()), g), zinv) == field_mul(sqrt_m1(), y_aff),
        // algebraic_setup result: e*tinv = inv(g)
        field_mul(e, tinv) == field_inv(g),
        field_mul(field_neg(e), tinv) == field_neg(field_inv(g)),
        // algebraic_setup result: enchanted = ±f/g
        ({
            let enchanted = field_mul(field_mul(invsqrt_std, u1), c_iad);
            enchanted == field_mul(f, field_inv(g)) || enchanted == field_neg(
                field_mul(f, field_inv(g)),
            )
        }),
        // s_matching for both negcheck2 subcases
        ({
            let i = sqrt_m1();
            let h_rot = field_mul(f, i);
            let enchanted = field_mul(field_mul(invsqrt_std, u1), c_iad);
            field_abs(
                field_mul(
                    field_sub(h_rot, field_neg(e)),
                    field_mul(i, field_mul(field_neg(e), tinv)),
                ),
            ) == field_abs(field_mul(enchanted, field_sub(1nat, field_mul(x_aff, i)))) && field_abs(
                field_mul(field_sub(h_rot, e), field_mul(i, field_mul(e, tinv))),
            ) == field_abs(field_mul(enchanted, field_sub(1nat, field_neg(field_mul(x_aff, i)))))
        }),
    ensures
        batch_compress_body(e, f, g, h, eg, fh, inv) == ristretto_compress_affine(x_aff, y_aff),
{
    assert(p() > 2) by {
        p_gt_2();
    };

    // z_inv = 1 simplifications: mul(a, 1) == a
    let i = sqrt_m1();
    assert(field_mul(t_aff, 1nat) == t_aff && field_mul(x_aff, 1nat) == x_aff && field_mul(
        field_mul(y_aff, i),
        1nat,
    ) == field_mul(y_aff, i)) by {
        lemma_mul_one_identity(t_aff);
        lemma_mul_one_identity(x_aff);
        lemma_mul_one_identity(field_mul(y_aff, i));
    };

    // negcheck2 arguments match: batch uses i*y, std uses y*i
    assert(field_mul(i, y_aff) == field_mul(y_aff, i)) by {
        lemma_field_mul_comm(i, y_aff);
    };

    // double negation for negcheck2=true branch
    assert(field_neg(field_neg(e)) == e % p()) by {
        lemma_field_neg_neg(e);
    };

    // Explicitly unfold batch spec to its s_final in the rotation case
    let h_rot = field_mul(f, i);
    let nc2_batch = is_negative(field_mul(field_mul(h_rot, g), zinv));
    let g_rot = field_neg(e);
    let g_final = if nc2_batch {
        field_neg(g_rot)
    } else {
        g_rot
    };
    let s_batch = field_mul(field_sub(h_rot, g_final), field_mul(i, field_mul(g_final, tinv)));
    let s_final_batch = field_abs(s_batch);

    // batch_compress_body evaluates to u8_32_from_nat(s_final_batch) in rotation case
    assert(batch_compress_body(e, f, g, h, eg, fh, inv) == u8_32_from_nat(s_final_batch));

    // Explicitly unfold std spec to its s_final in the rotation case
    let enchanted = field_mul(field_mul(invsqrt_std, u1), c_iad);
    let nc2_std = is_negative(field_mul(y_aff, i));
    let y_rot = field_mul(x_aff, i);
    let y_final = if nc2_std {
        field_neg(y_rot)
    } else {
        y_rot
    };
    let s_std = field_mul(enchanted, field_sub(1nat, y_final));
    let s_final_std = field_abs(s_std);

    // ristretto_compress_affine evaluates to u8_32_from_nat(s_final_std) in rotation case
    assert(ristretto_compress_affine(x_aff, y_aff) == u8_32_from_nat(s_final_std));

    // negcheck2 decisions match, so both branches correspond
    assert(nc2_batch == nc2_std);

    // Connect field_neg(field_neg(e)) to e in field operations
    if nc2_batch {
        // g_final = field_neg(field_neg(e)), need to connect to s_matching which uses e
        assert(field_sub(h_rot, field_neg(field_neg(e))) == field_sub(h_rot, e)) by {
            lemma_field_neg_neg(e);
            lemma_mod_bound(e as int, p() as int);
            lemma_small_mod(e % p(), p());
        };
        assert(field_mul(field_neg(field_neg(e)), tinv) == field_mul(e, tinv)) by {
            lemma_field_neg_neg(e);
            lemma_mod_bound(e as int, p() as int);
            lemma_small_mod(e % p(), p());
            lemma_mul_mod_noop_left(e as int, tinv as int, p() as int);
        };
        assert(field_abs(s_batch) == field_abs(s_std));
    } else {
        assert(field_abs(s_batch) == field_abs(s_std));
    }
    assert(s_final_batch == s_final_std);
}

/// Core encoding equality: proves z_inv_std = 1, then shows both algorithms
/// agree on rotation decisions and produce s values equal up to sign.
///
/// Preconditions include all established algebraic facts from the outer lemmas.
proof fn lemma_encoding_equality_core(e: nat, f: nat, g: nat, h: nat, eg: nat, fh: nat, inv: nat)
    requires
        eg == field_mul(e, g),
        fh == field_mul(f, h),
        field_mul(eg, fh) != 0,
        field_mul(inv, field_mul(eg, fh)) == 1,
        ({
            let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
            field_sub(field_square(h), field_square(g)) == field_neg(
                field_mul(field_square(e), field_add(d, 1)),
            )
        }),
        e % p() != 0,
        f % p() != 0,
        g % p() != 0,
        h % p() != 0,
        eg % p() != 0,
        fh % p() != 0,
        field_mul(eg, inv) == field_inv(fh),
        field_mul(fh, inv) == field_inv(eg),
        ({
            let c_iad = fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D);
            let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
            let x_aff = field_mul(e, field_inv(f));
            let y_aff = field_mul(g, field_inv(h));
            let t_aff = field_mul(x_aff, y_aff);
            let u1 = field_mul(field_add(1nat, y_aff), field_sub(1nat, y_aff));
            let neg_one_minus_d = field_sub(field_neg(1nat), d);
            let B = field_mul(field_mul(e, eg), field_inv(field_mul(h, fh)));
            nat_invsqrt(field_mul(u1, field_square(t_aff))) == field_abs(
                field_mul(c_iad, field_inv(B)),
            ) && field_mul(u1, field_square(t_aff)) == field_mul(neg_one_minus_d, field_square(B))
                && B % p() != 0 && neg_one_minus_d % p() != 0 && field_mul(
                field_square(c_iad),
                neg_one_minus_d,
            ) == 1
        }),
    ensures
        batch_compress_body(e, f, g, h, eg, fh, inv) == ristretto_compress_affine(
            field_mul(e, field_inv(f)),
            field_mul(g, field_inv(h)),
        ),
{
    let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
    let c_iad = fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D);
    let x_aff = field_mul(e, field_inv(f));
    let y_aff = field_mul(g, field_inv(h));
    let t_aff = field_mul(x_aff, y_aff);
    let u1 = field_mul(field_add(1nat, y_aff), field_sub(1nat, y_aff));
    let neg_one_minus_d = field_sub(field_neg(1nat), d);
    let B = field_mul(field_mul(e, eg), field_inv(field_mul(h, fh)));
    let invsqrt_std = nat_invsqrt(field_mul(u1, field_square(t_aff)));
    assert(p() > 2) by {
        p_gt_2();
    };

    // Phase C: z_inv_std = 1
    let i1_std = field_mul(invsqrt_std, u1);
    let i2_std = field_mul(invsqrt_std, t_aff);
    let z_inv_std = field_mul(i1_std, field_mul(i2_std, t_aff));
    assert(z_inv_std == 1) by {
        lemma_z_inv_std_is_one(invsqrt_std, u1, t_aff, c_iad, B, neg_one_minus_d);
    };

    // Phase D: rotation case analysis + final s match

    // D.1: z_inv_std = 1 simplifications
    assert(field_mul(t_aff, z_inv_std) == t_aff && field_mul(x_aff, z_inv_std) == x_aff) by {
        lemma_mul_one_identity(t_aff);
        lemma_mul_one_identity(x_aff);
    };

    // D.2: batch rotation decision = is_negative(t_aff)
    let zinv = field_mul(eg, inv);
    let tinv = field_mul(fh, inv);
    assert(zinv == field_inv(fh));
    assert(tinv == field_inv(eg));

    // Dispatch to case-specific helpers
    assert(batch_compress_body(e, f, g, h, eg, fh, inv) == ristretto_compress_affine(x_aff, y_aff))
        by {
        if !is_negative(t_aff) {
            lemma_no_rotation_case(
                e,
                f,
                g,
                h,
                eg,
                fh,
                inv,
                invsqrt_std,
                c_iad,
                B,
                t_aff,
                x_aff,
                y_aff,
                zinv,
                tinv,
            );
        } else {
            lemma_rotation_case(
                e,
                f,
                g,
                h,
                eg,
                fh,
                inv,
                invsqrt_std,
                c_iad,
                B,
                t_aff,
                x_aff,
                y_aff,
                u1,
                neg_one_minus_d,
                zinv,
                tinv,
            );
        }
    };
}

/// Sub-proof: dispatch on the rotation case and prove s_final values match.
///
/// This lemma handles both the negcheck1=false (no rotation) and negcheck1=true
/// (rotation) cases. In each case it shows the batch and standard s values are
/// equal up to sign, so field_abs equalizes them.
///
/// The inverse correspondence facts (zinv=inv(fh), tinv=inv(eg)) are accepted
/// as preconditions rather than re-derived; the caller establishes them.
proof fn lemma_batch_std_case_dispatch(e: nat, f: nat, g: nat, h: nat, eg: nat, fh: nat, inv: nat)
    requires
        eg == field_mul(e, g),
        fh == field_mul(f, h),
        field_mul(eg, fh) != 0,
        field_mul(inv, field_mul(eg, fh)) == 1,
        ({
            let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
            field_sub(field_square(h), field_square(g)) == field_neg(
                field_mul(field_square(e), field_add(d, 1)),
            )
        }),
        e % p() != 0,
        f % p() != 0,
        g % p() != 0,
        h % p() != 0,
        eg % p() != 0,
        fh % p() != 0,
        field_mul(eg, inv) == field_inv(fh),
        field_mul(fh, inv) == field_inv(eg),
    ensures
        batch_compress_body(e, f, g, h, eg, fh, inv) == ristretto_compress_affine(
            field_mul(e, field_inv(f)),
            field_mul(g, field_inv(h)),
        ),
{
    let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
    let c_iad = fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D);
    let x_aff = field_mul(e, field_inv(f));
    let y_aff = field_mul(g, field_inv(h));
    let t_aff = field_mul(x_aff, y_aff);
    let inv_fh = field_inv(fh);
    let neg_one_minus_d = field_sub(field_neg(1nat), d);
    let B = field_mul(field_mul(e, eg), field_inv(field_mul(h, fh)));
    assert(p() > 2) by {
        p_gt_2();
    };

    // Re-establish t_aff = eg/fh
    assert(t_aff == field_mul(eg, inv_fh)) by {
        lemma_four_factor_rearrange(e, field_inv(f), g, field_inv(h));
        lemma_inv_of_product(f, h);
    };

    let zinv = field_mul(eg, inv);
    let tinv = field_mul(fh, inv);

    // Invsqrt factoring (Phase B): u1·t² = (−1−d)·B²
    // (Complex postcondition with let-bindings; left as direct call
    // to avoid restricting solver access to intermediate equalities.)
    let u1 = field_mul(field_add(1nat, y_aff), field_sub(1nat, y_aff));
    lemma_u1_u2_sq_factoring(e, f, g, h, eg, fh, d);
    assert(field_mul(u1, field_square(t_aff)) == field_mul(neg_one_minus_d, field_square(B)));

    // (−1−d) and B nonzero (needed for axiom_invsqrt_factors_over_square)
    assert(neg_one_minus_d % p() != 0) by {
        lemma_d_plus_one_nonzero();
        lemma_field_add_comm(d, 1);
        let d_plus_1 = field_add(1nat, d);
        assert(d_plus_1 % p() != 0) by {
            lemma_field_element_reduced(d_plus_1);
        };
        lemma_field_neg_nonzero(d_plus_1);
        lemma_neg_one_times_is_neg(d_plus_1);
        lemma_field_mul_distributes_over_add(field_neg(1nat), 1nat, d);
        lemma_neg_one_times_is_neg(d);
        lemma_field_mul_one_right(field_neg(1nat));
        lemma_field_element_reduced(field_neg(1nat));
        lemma_field_sub_eq_add_neg(field_neg(1nat), d);
        lemma_field_element_reduced(neg_one_minus_d);
    };
    assert(B % p() != 0) by {
        let e_eg = field_mul(e, eg);
        let h_fh = field_mul(h, fh);
        assert(e_eg % p() != 0) by {
            lemma_nonzero_product(e, eg);
            lemma_field_element_reduced(e_eg);
        };
        assert(h_fh % p() != 0) by {
            lemma_nonzero_product(h, fh);
            lemma_field_element_reduced(h_fh);
        };
        field_inv_property(h_fh);
        let inv_h_fh = field_inv(h_fh);
        assert(inv_h_fh != 0) by {
            if inv_h_fh == 0 {
                assert(field_mul(field_canonical(h_fh), 0nat) == 0nat) by {
                    lemma_mul_mod_noop_left(h_fh as int, 0int, p() as int);
                };
            }
        };
        assert(inv_h_fh % p() != 0) by {
            lemma_field_element_reduced(inv_h_fh);
        };
        lemma_nonzero_product(e_eg, inv_h_fh);
        lemma_field_element_reduced(B);
    };

    // invsqrt((−1−d)·B²) = abs(invsqrt(−1−d) · inv(B)) = abs(c_iad · inv(B))
    // (Axiom postconditions needed unscoped for downstream inference.)
    axiom_invsqrt_factors_over_square(neg_one_minus_d, B);
    axiom_invsqrt_a_minus_d();
    let invsqrt_std = nat_invsqrt(field_mul(u1, field_square(t_aff)));
    assert(invsqrt_std == field_abs(field_mul(c_iad, field_inv(B))));

    // Phase C+D: z_inv_std = 1, then case dispatch showing s_final values match.
    // (Postconditions of lemma_encoding_equality_core are needed unscoped
    // for the solver to close the proof, so we leave this as a direct call.)
    lemma_encoding_equality_core(e, f, g, h, eg, fh, inv);
}

/// Lemma: batch encoding equals standard encoding.
///
/// For a point with completed-point intermediates (e, f, g, h) from doubling,
/// the Ristretto encoding using batch inverse 1/(eg·fh) equals the standard
/// affine encoding of the point (e/f, g/h).
///
/// The proof composes two axioms and one precondition:
///   1. `axiom_invsqrt_factors_over_square` — nat_invsqrt factors over perfect squares
///   2. `axiom_invsqrt_a_minus_d` — nat_invsqrt(−1−d) = C_IAD and C_IAD²·(−1−d) = 1
///   3. Batch identity h² − g² = −e²(1+d) (precondition, from `lemma_curve_eq_batch_identity`)
///
/// Reference: Hamburg (2015) "Decaf" Section 6, Equation (6)
/// URL: https://eprint.iacr.org/2015/673.pdf
/// Runtime validation: `test_batch_compress_equals_single_compress_of_double`,
///   `test_batch_axiom_intermediate_values`
pub proof fn lemma_batch_encoding_equals_standard_encoding(
    e: nat,
    f: nat,
    g: nat,
    h: nat,
    eg: nat,
    fh: nat,
    inv: nat,
)
    requires
        eg == field_mul(e, g),
        fh == field_mul(f, h),
        field_mul(eg, fh) != 0,
        field_mul(inv, field_mul(eg, fh)) == 1,
        ({
            let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
            field_sub(field_square(h), field_square(g)) == field_neg(
                field_mul(field_square(e), field_add(d, 1)),
            )
        }),
    ensures
        batch_compress_body(e, f, g, h, eg, fh, inv) == ristretto_compress_affine(
            field_mul(e, field_inv(f)),
            field_mul(g, field_inv(h)),
        ),
{
    assert(p() > 2) by {
        p_gt_2();
    };
    let egfh = field_mul(eg, fh);
    assert(egfh != 0) by {
        lemma_field_element_reduced(egfh);
    };
    assert(eg % p() != 0) by {
        if eg % p() == 0 {
            lemma_mul_mod_noop_left(eg as int, fh as int, p() as int);
        }
    };
    assert(fh % p() != 0) by {
        if fh % p() == 0 {
            lemma_field_mul_comm(eg, fh);
            lemma_mul_mod_noop_left(fh as int, eg as int, p() as int);
        }
    };
    assert(e % p() != 0 && g % p() != 0) by {
        if e % p() == 0 {
            lemma_mul_mod_noop_left(e as int, g as int, p() as int);
        }
        if g % p() == 0 {
            lemma_mul_mod_noop_left(g as int, e as int, p() as int);
            lemma_field_mul_comm(e, g);
        }
    };
    assert(f % p() != 0 && h % p() != 0) by {
        if f % p() == 0 {
            lemma_mul_mod_noop_left(f as int, h as int, p() as int);
        }
        if h % p() == 0 {
            lemma_mul_mod_noop_left(h as int, f as int, p() as int);
            lemma_field_mul_comm(f, h);
        }
    };
    assert(batch_compress_body(e, f, g, h, eg, fh, inv) == ristretto_compress_affine(
        field_mul(e, field_inv(f)),
        field_mul(g, field_inv(h)),
    )) by {
        lemma_batch_std_final_matching(e, f, g, h, eg, fh, inv);
    };
}

/// Lemma: the batch compression loop body produces the same encoding
/// as compressing the doubled affine point.
///
/// This is the top-level composition that combines:
///   1. `lemma_doubled_affine_from_batch_state` -- edwards_double(X/Z, Y/Z) == (e/f, g/h)
///   2. `lemma_batch_compress_body_inv_zero` -- degenerate case (inv = 0)
///   3. `lemma_degenerate_double_compresses_to_zero` -- degenerate encoding is zero
///   4. `lemma_batch_encoding_equals_standard_encoding` -- generic batch == standard encoding
///
/// Reference: Hamburg (2015) "Decaf" §6; https://eprint.iacr.org/2015/673.pdf
/// Runtime validation: `test_batch_compress_equals_single_compress_of_double`
pub proof fn lemma_batch_compress_equals_compress_of_double(
    x: nat,
    y: nat,
    z: nat,
    t: nat,
    e: nat,
    f: nat,
    g: nat,
    h: nat,
    eg: nat,
    fh: nat,
    inv: nat,
)
    requires
        x < p(),
        y < p(),
        z < p(),
        t < p(),
        z % p() != 0,
        field_mul(z, t) == field_mul(x, y),
        is_on_edwards_curve_projective(x, y, z),
        ({
            let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
            e == field_mul(2, field_mul(x, y)) && f == field_add(
                field_square(z),
                field_mul(d, field_square(t)),
            ) && g == field_add(field_square(y), field_square(x)) && h == field_sub(
                field_square(z),
                field_mul(d, field_square(t)),
            ) && eg == field_mul(e, g) && fh == field_mul(f, h)
        }),
        (field_mul(eg, fh) != 0) ==> field_mul(inv, field_mul(eg, fh)) == 1,
        (field_mul(eg, fh) == 0) ==> inv == 0,
    ensures
        batch_compress_body(e, f, g, h, eg, fh, inv) == ristretto_compress_affine(
            edwards_double(field_mul(x, field_inv(z)), field_mul(y, field_inv(z))).0,
            edwards_double(field_mul(x, field_inv(z)), field_mul(y, field_inv(z))).1,
        ),
{
    // doubled = (e/f, g/h)
    let doubled = edwards_double(field_mul(x, field_inv(z)), field_mul(y, field_inv(z)));
    assert(doubled == (field_mul(e, field_inv(f)), field_mul(g, field_inv(h)))) by {
        lemma_doubled_affine_from_batch_state(x, y, z, t, e, f, g, h);
    };

    if field_mul(eg, fh) == 0 {
        // Degenerate: both sides equal u8_32_from_nat(0)
        assert(batch_compress_body(e, f, g, h, eg, fh, inv) == u8_32_from_nat(0)) by {
            lemma_batch_compress_body_inv_zero(e, f, g, h, eg, fh);
        };
        assert(field_mul(field_mul(e, g), field_mul(f, h)) % p() == 0) by {
            lemma_small_mod(0nat, p());
        };
        assert(ristretto_compress_affine(doubled.0, doubled.1) == u8_32_from_nat(0)) by {
            lemma_degenerate_double_compresses_to_zero(x, y, z, t, e, f, g, h);
        };
    } else {
        // Establish h²-g² = -e²(1+d) from the projective curve equation
        assert(({
            let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
            field_sub(field_square(h), field_square(g)) == field_neg(
                field_mul(field_square(e), field_add(d, 1)),
            )
        })) by {
            lemma_batch_identity_projective(x, y, z, t, e, g, h);
        };

        // Generic: batch body == ristretto_compress_affine(e/f, g/h) by Decaf §6
        assert(batch_compress_body(e, f, g, h, eg, fh, inv) == ristretto_compress_affine(
            field_mul(e, field_inv(f)),
            field_mul(g, field_inv(h)),
        )) by {
            lemma_batch_encoding_equals_standard_encoding(e, f, g, h, eg, fh, inv);
        };
    }
}

} // verus!
#[cfg(test)]
mod test_batch_compress_axiom {
    use crate::backend::serial::u64::field::FieldElement51;
    use crate::constants;
    use crate::edwards::EdwardsPoint;
    use crate::field::FieldElement;
    use crate::ristretto::RistrettoPoint;
    use subtle::{ConditionallyNegatable, ConditionallySelectable, ConstantTimeEq};

    /// Validate lemma_batch_compress_equals_compress_of_double:
    /// For each point P, the batch double-and-compress algorithm produces the
    /// same bytes as single-point compress(2*P).
    #[test]
    fn test_batch_compress_equals_single_compress_of_double() {
        use crate::scalar::Scalar;

        // Helper: compute compress(2*P) via single-point path
        fn compress_doubled(p: &RistrettoPoint) -> [u8; 32] {
            let doubled = &p.0 + &p.0;
            let rp = RistrettoPoint(doubled);
            *rp.compress().as_bytes()
        }

        // Helper: compute batch double-and-compress for a single point
        fn batch_compress_one(p: &RistrettoPoint) -> [u8; 32] {
            let results = RistrettoPoint::double_and_compress_batch(&[*p]);
            *results[0].as_bytes()
        }

        // Test with identity
        let identity = RistrettoPoint(EdwardsPoint::default());
        assert_eq!(
            compress_doubled(&identity),
            batch_compress_one(&identity),
            "identity: batch != single"
        );

        // Test with basepoint
        let bp = constants::RISTRETTO_BASEPOINT_POINT;
        assert_eq!(
            compress_doubled(&bp),
            batch_compress_one(&bp),
            "basepoint: batch != single"
        );

        // Test with many small multiples of basepoint
        let mut point = bp;
        for i in 2..100u32 {
            point = &point + &bp;
            assert_eq!(
                compress_doubled(&point),
                batch_compress_one(&point),
                "{}*B: batch != single",
                i
            );
        }

        // Test with hash-derived points
        use sha2::{Digest, Sha512};
        for seed in 0u32..100 {
            let mut hasher = Sha512::new();
            hasher.update(b"batch_compress_axiom_test_");
            hasher.update(seed.to_le_bytes());
            let hash = hasher.finalize();
            let mut bytes = [0u8; 64];
            bytes.copy_from_slice(&hash);
            let pt = RistrettoPoint::hash_from_bytes::<Sha512>(&seed.to_le_bytes());
            assert_eq!(
                compress_doubled(&pt),
                batch_compress_one(&pt),
                "hash-derived seed {}: batch != single",
                seed
            );
        }

        // Test batch with multiple points at once
        let points: alloc::vec::Vec<RistrettoPoint> = (1u64..=20)
            .map(|i| &Scalar::from(i) * &bp.0)
            .map(RistrettoPoint)
            .collect();
        let batch_results = RistrettoPoint::double_and_compress_batch(&points);
        for (idx, (p, batch_r)) in points.iter().zip(batch_results.iter()).enumerate() {
            let single = compress_doubled(p);
            assert_eq!(
                &single,
                batch_r.as_bytes(),
                "multi-batch point {}: batch != single",
                idx
            );
        }

        // --- Degenerate points: eg*fh = 0 (identity, torsion) ---
        // These validate the axiom's zero-case branch: when eg*fh = 0,
        // batch_invert returns inv = 0 and the result is the identity encoding.

        let identity_encoding = [0u8; 32];
        let torsion = crate::backend::serial::u64::constants::EIGHT_TORSION;

        // Verify identity produces identity encoding via batch
        let identity_batch = batch_compress_one(&RistrettoPoint(torsion[0]));
        assert_eq!(
            identity_batch, identity_encoding,
            "torsion[0] (identity): batch should produce identity encoding"
        );

        // 2-torsion: T[4] = (0, -1, 1, 0) — doubling gives identity
        let t4_batch = batch_compress_one(&RistrettoPoint(torsion[4]));
        let t4_single = compress_doubled(&RistrettoPoint(torsion[4]));
        assert_eq!(
            t4_batch, t4_single,
            "torsion[4] (2-torsion): batch != single"
        );

        // 4-torsion: T[2] and T[6] — doubling gives 2-torsion
        for &ti in &[2usize, 6] {
            let batch = batch_compress_one(&RistrettoPoint(torsion[ti]));
            let single = compress_doubled(&RistrettoPoint(torsion[ti]));
            assert_eq!(
                batch, single,
                "torsion[{}] (4-torsion): batch != single",
                ti
            );
        }

        // All 8-torsion elements
        for (ti, t_pt) in torsion.iter().enumerate() {
            let batch = batch_compress_one(&RistrettoPoint(*t_pt));
            let single = compress_doubled(&RistrettoPoint(*t_pt));
            assert_eq!(batch, single, "torsion[{}]: batch != single", ti);
        }

        // Mixed batch: identity + torsion + generic points
        let mixed: alloc::vec::Vec<RistrettoPoint> = alloc::vec![
            RistrettoPoint(torsion[0]),                   // identity
            bp,                                           // basepoint (generic)
            RistrettoPoint(torsion[4]),                   // 2-torsion
            RistrettoPoint(&Scalar::from(7u64) * &bp.0),  // 7*B (generic)
            RistrettoPoint(torsion[2]),                   // 4-torsion
            RistrettoPoint(torsion[6]),                   // 4-torsion
            RistrettoPoint(&Scalar::from(42u64) * &bp.0), // 42*B (generic)
        ];
        let mixed_batch = RistrettoPoint::double_and_compress_batch(&mixed);
        for (idx, (p, batch_r)) in mixed.iter().zip(mixed_batch.iter()).enumerate() {
            let single = compress_doubled(p);
            assert_eq!(
                &single,
                batch_r.as_bytes(),
                "mixed batch point {}: batch != single",
                idx
            );
        }

        // Verify BatchCompressState fields for identity: eg*fh == 0
        // Identity is (0:1:1:0), so e = 2*0*1 = 0, g = 1+0 = 1, eg = 0*1 = 0
        // This confirms the degenerate case is exercised.
        let id_point = torsion[0];
        let id_x = &id_point.X;
        let id_y = &id_point.Y;
        let id_z = &id_point.Z;
        let id_t = &id_point.T;
        let e = &(id_x * id_y) + &(id_x * id_y);
        let e_bytes = e.as_bytes();
        assert_eq!(e_bytes, [0u8; 32], "identity: e = 2XY should be 0");
        let eg = &e * &(&id_y.square() + &id_x.square());
        let eg_bytes = eg.as_bytes();
        assert_eq!(eg_bytes, [0u8; 32], "identity: eg should be 0");
    }

    /// Validate lemma_batch_encoding_equals_standard_encoding:
    /// For generic (non-degenerate) points, batch_compress_body(e,f,g,h,eg,fh,inv)
    /// equals ristretto_compress_affine(e/f, g/h).
    ///
    /// This test independently computes both sides and compares, also tracking
    /// which code path (square vs non-square / rotated vs non-rotated) each point takes.
    #[test]
    fn test_batch_axiom_intermediate_values() {
        use crate::scalar::Scalar;

        let d = &constants::EDWARDS_D;
        let bp = constants::RISTRETTO_BASEPOINT_POINT;
        let sqrt_m1 = FieldElement::from_bytes(&[
            0xb0, 0xa0, 0x0e, 0x4a, 0x27, 0x1b, 0xee, 0xc4, 0x78, 0xe4, 0x2f, 0xad, 0x06, 0x18,
            0x43, 0x2f, 0xa7, 0xd7, 0xfb, 0x3d, 0x99, 0x00, 0x4d, 0x2b, 0x0b, 0xdf, 0xc1, 0x4f,
            0x80, 0x24, 0x83, 0x2b,
        ]);
        let invsqrt_a_minus_d = FieldElement::from_bytes(&[
            0x78, 0xc4, 0xee, 0x18, 0x46, 0xbe, 0x91, 0xa0, 0x35, 0xc3, 0xa3, 0x5c, 0x32, 0x08,
            0x53, 0x52, 0xc3, 0xb2, 0xd3, 0x76, 0xf1, 0xee, 0x2e, 0x07, 0xc3, 0x3a, 0x01, 0x65,
            0x12, 0xa6, 0xf8, 0x24,
        ]);

        let mut square_count = 0u32;
        let mut nonsquare_count = 0u32;

        let test_points: alloc::vec::Vec<RistrettoPoint> = (1u64..=200)
            .map(|i| RistrettoPoint(&Scalar::from(i) * &bp.0))
            .collect();

        for (idx, p) in test_points.iter().enumerate() {
            let ep = &p.0;
            let x = &ep.X;
            let y = &ep.Y;
            let z = &ep.Z;
            let t = &ep.T;

            let e = &(x * y) + &(x * y);
            let f = &z.square() + &(d * &t.square());
            let g = &y.square() + &x.square();
            let h = &z.square() - &(d * &t.square());
            let eg = &e * &g;
            let fh = &f * &h;
            let egfh = &eg * &fh;

            if egfh == FieldElement::ZERO {
                continue;
            }

            let inv = egfh.invert();
            let zinv = &eg * &inv;
            let tinv = &fh * &inv;

            // Check: zinv * fh == 1 (since zinv = eg/(eg*fh) = 1/fh)
            let zinv_fh = &zinv * &fh;
            assert!(
                bool::from(zinv_fh.ct_eq(&FieldElement::ONE)),
                "point {}: zinv * fh should be 1",
                idx
            );

            // Check: tinv * eg == 1
            let tinv_eg = &tinv * &eg;
            assert!(
                bool::from(tinv_eg.ct_eq(&FieldElement::ONE)),
                "point {}: tinv * eg should be 1",
                idx
            );

            // Determine square/non-square case via negcheck1
            let negcheck1_val = &eg * &zinv;
            let negcheck1 = negcheck1_val.is_negative();

            if bool::from(negcheck1) {
                nonsquare_count += 1;
            } else {
                square_count += 1;
            }

            // Compute batch side
            let batch_result = RistrettoPoint::double_and_compress_batch(&[*p]);

            // Compute single side: compress(2*P)
            let doubled = ep + ep;
            let single_result = *RistrettoPoint(doubled).compress().as_bytes();

            assert_eq!(
                batch_result[0].as_bytes(),
                &single_result,
                "point {}: batch != single (negcheck1={})",
                idx,
                bool::from(negcheck1)
            );

            // Verify affine doubling matches e/f, g/h
            let z_inv_fe = z.invert();
            let ax = x * &z_inv_fe;
            let ay = y * &z_inv_fe;

            let f_inv = f.invert();
            let h_inv = h.invert();
            let ef = &e * &f_inv;
            let gh = &g * &h_inv;

            // Compute affine doubled point
            let two_ab = &(&ax * &ay) + &(&ax * &ay);
            let aa = ax.square();
            let bb = ay.square();
            let aabb = &aa * &bb;
            let d_aabb = d * &aabb;
            let denom_x = &FieldElement::ONE + &d_aabb;
            let denom_y = &FieldElement::ONE - &d_aabb;
            let doubled_x = &two_ab * &denom_x.invert();
            let doubled_y = &(&bb + &aa) * &denom_y.invert();

            assert!(
                bool::from(doubled_x.ct_eq(&ef)),
                "point {}: doubled_x != e/f",
                idx
            );
            assert!(
                bool::from(doubled_y.ct_eq(&gh)),
                "point {}: doubled_y != g/h",
                idx
            );
        }

        assert!(
            square_count > 0,
            "no square (non-rotated) cases encountered"
        );
        assert!(
            nonsquare_count > 0,
            "no non-square (rotated) cases encountered"
        );
        eprintln!(
            "batch axiom intermediate test: {} square, {} non-square cases",
            square_count, nonsquare_count
        );
    }

    /// Stress test: 1000 random hash-derived points
    #[test]
    fn test_batch_compress_stress_random() {
        use sha2::{Digest, Sha512};

        fn compress_doubled(p: &RistrettoPoint) -> [u8; 32] {
            let doubled = &p.0 + &p.0;
            *RistrettoPoint(doubled).compress().as_bytes()
        }

        fn batch_compress_one(p: &RistrettoPoint) -> [u8; 32] {
            let results = RistrettoPoint::double_and_compress_batch(&[*p]);
            *results[0].as_bytes()
        }

        for seed in 0u32..1000 {
            let pt = RistrettoPoint::hash_from_bytes::<Sha512>(&seed.to_le_bytes());
            assert_eq!(
                compress_doubled(&pt),
                batch_compress_one(&pt),
                "stress seed {}: batch != single",
                seed
            );
        }

        // Also test large batches
        for batch_start in (0u32..1000).step_by(50) {
            let points: alloc::vec::Vec<RistrettoPoint> = (batch_start..batch_start + 50)
                .map(|seed| RistrettoPoint::hash_from_bytes::<Sha512>(&seed.to_le_bytes()))
                .collect();
            let batch_results = RistrettoPoint::double_and_compress_batch(&points);
            for (i, (p, batch_r)) in points.iter().zip(batch_results.iter()).enumerate() {
                let single = compress_doubled(p);
                assert_eq!(
                    &single,
                    batch_r.as_bytes(),
                    "batch[{}..{}] point {}: batch != single",
                    batch_start,
                    batch_start + 50,
                    i
                );
            }
        }
    }

    /// Validate axiom_invsqrt_a_minus_d_squared:
    /// C_IAD² · (a − d) ≡ 1 (mod p), where a = −1 for Ed25519.
    #[test]
    fn test_invsqrt_a_minus_d_squared() {
        use crate::backend::serial::u64::constants::INVSQRT_A_MINUS_D;

        let c_iad: FieldElement = INVSQRT_A_MINUS_D;
        let d = &constants::EDWARDS_D;

        let c_iad_sq = c_iad.square();
        let neg_one = &FieldElement::ZERO - &FieldElement::ONE;
        let a_minus_d = &neg_one - d;

        let product = &c_iad_sq * &a_minus_d;
        assert!(
            bool::from(product.ct_eq(&FieldElement::ONE)),
            "C_IAD² · (a − d) should be 1"
        );
    }

    /// Validate axiom_nat_invsqrt_neg_one_minus_d:
    /// nat_invsqrt(−1 − d) == C_IAD.
    #[test]
    fn test_nat_invsqrt_neg_one_minus_d() {
        use crate::backend::serial::u64::constants::INVSQRT_A_MINUS_D;

        let c_iad: FieldElement = INVSQRT_A_MINUS_D;
        let d = &constants::EDWARDS_D;

        let neg_one = &FieldElement::ZERO - &FieldElement::ONE;
        let a_minus_d = &neg_one - d; // −1 − d

        let (_was_sq, invsqrt) = FieldElement::sqrt_ratio_i(&FieldElement::ONE, &a_minus_d);
        assert!(
            bool::from(invsqrt.ct_eq(&c_iad)),
            "nat_invsqrt(−1 − d) should equal INVSQRT_A_MINUS_D"
        );
    }

    /// Validate axiom_curve_eq_batch_identity:
    /// For 200 points on the curve: h² − g² = −e²·(1 + d).
    #[test]
    fn test_curve_eq_batch_identity() {
        use crate::scalar::Scalar;

        let d = &constants::EDWARDS_D;
        let bp = constants::RISTRETTO_BASEPOINT_POINT;

        for i in 1u64..=200 {
            let p = RistrettoPoint(&Scalar::from(i) * &bp.0);
            let ep = &p.0;

            let z_inv = ep.Z.invert();
            let a = &ep.X * &z_inv;
            let b = &ep.Y * &z_inv;

            let e = &(&a * &b) + &(&a * &b);
            let g = &a.square() + &b.square();
            let dab2 = &(d * &a.square()) * &b.square();
            let h = &FieldElement::ONE - &dab2;

            let h_sq = h.square();
            let g_sq = g.square();
            let lhs = &h_sq - &g_sq;
            let e_sq = e.square();
            let d_plus_1 = &FieldElement::ONE + d;
            let rhs_neg = &e_sq * &d_plus_1;
            let rhs = &FieldElement::ZERO - &rhs_neg;

            assert!(bool::from(lhs.ct_eq(&rhs)), "point {}: h²−g² ≠ −e²(1+d)", i);
        }
    }

    /// Validate axiom_invsqrt_factors_over_square:
    /// invsqrt(a · b²) = field_abs(invsqrt(a) · inv(b)) for nonzero a, b.
    #[test]
    fn test_invsqrt_factors_over_square() {
        use crate::scalar::Scalar;
        use subtle::ConditionallyNegatable;

        let bp = constants::RISTRETTO_BASEPOINT_POINT;

        for i in 1u64..=200 {
            let p = RistrettoPoint(&Scalar::from(i) * &bp.0);
            let ep = &p.0;

            // Use X, Y coordinates as arbitrary nonzero field elements
            let a_fe = &ep.X;
            let b_fe = &ep.Y;

            // Skip if either is zero
            if bool::from(a_fe.ct_eq(&FieldElement::ZERO))
                || bool::from(b_fe.ct_eq(&FieldElement::ZERO))
            {
                continue;
            }

            // Compute invsqrt(a * b²) via sqrt_ratio_i(1, a*b²)
            let b_sq = b_fe.square();
            let ab2 = a_fe * &b_sq;
            let (_, lhs_raw) = FieldElement::sqrt_ratio_i(&FieldElement::ONE, &ab2);
            let mut lhs = lhs_raw;
            let lhs_neg = lhs.is_negative();
            lhs.conditional_negate(lhs_neg);

            // Compute field_abs(invsqrt(a) * inv(b))
            let (_, invsqrt_a_raw) = FieldElement::sqrt_ratio_i(&FieldElement::ONE, a_fe);
            let mut invsqrt_a = invsqrt_a_raw;
            let invsqrt_a_neg = invsqrt_a.is_negative();
            invsqrt_a.conditional_negate(invsqrt_a_neg);

            let inv_b = b_fe.invert();
            let mut rhs = &invsqrt_a * &inv_b;
            let rhs_neg = rhs.is_negative();
            rhs.conditional_negate(rhs_neg);

            assert!(
                bool::from(lhs.ct_eq(&rhs)),
                "point {}: invsqrt(a·b²) ≠ field_abs(invsqrt(a)·inv(b))",
                i
            );
        }
    }

    /// Test the degenerate axiom: for all 8-torsion points, verify that
    /// 2*P compresses to the identity encoding [0u8; 32].
    #[test]
    fn test_degenerate_double_compresses_to_zero() {
        let torsion = crate::backend::serial::u64::constants::EIGHT_TORSION;
        let identity_encoding = [0u8; 32];

        for (ti, t_pt) in torsion.iter().enumerate() {
            let doubled = t_pt + t_pt;
            let rp = RistrettoPoint(doubled);
            let encoding = *rp.compress().as_bytes();
            assert_eq!(
                encoding, identity_encoding,
                "2*torsion[{}] should encode to zero",
                ti
            );
        }

        // Also test torsion + basepoint equivalences:
        // For any torsion T, P+T is in the same Ristretto equivalence class as P.
        // So compress(2*(P+T)) == compress(2*P) for any generic P.
        let bp = constants::RISTRETTO_BASEPOINT_POINT;
        let bp_doubled = *RistrettoPoint(&bp.0 + &bp.0).compress().as_bytes();

        for (ti, t_pt) in torsion.iter().enumerate() {
            let shifted = RistrettoPoint(&bp.0 + t_pt);
            let shifted_doubled = *RistrettoPoint(&shifted.0 + &shifted.0)
                .compress()
                .as_bytes();
            assert_eq!(
                shifted_doubled, bp_doubled,
                "compress(2*(B+T[{}])) should equal compress(2*B)",
                ti
            );
        }
    }
}
