//! Lemmas for E[4] torsion elements and their Edwards addition rules.
//!
//! These are pure Edwards-curve algebra: they use `edwards_add`, field ops,
//! and `is_on_edwards_curve` but have no Ristretto or Lizard dependencies.
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
use crate::specs::core_specs::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::primality_specs::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::sqrt_m1_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::number_theory_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::backend::serial::u64::constants::spec_eight_torsion;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// E[4] torsion bridge axiom
// =============================================================================
/// Bridge axiom: affine coordinates of the even-indexed 8-torsion elements.
///
/// T[2] and T[6] are the two 4-torsion points (y = 0, x = ±√(−1));
/// T[4] is the 2-torsion point (0, −1).
///
/// On a twisted Edwards curve E_{a,d} with a = −1, the points of exact
/// order 4 have coordinates (±1/√a, 0) = (±√(−1), 0), and the unique
/// point of order 2 is (0, −1).
///
/// Reference:
/// - Hamburg (2015) "Decaf" (https://eprint.iacr.org/2015/673), §7
///   ("Removing larger cofactors": E[8] ≅ Z₈, 4-torsion subgroup).
/// - https://ristretto.group/details/isogeny_encoding.html
///   ("The points of exact order 4 are (±1/√a, 0)").
///
/// These are concrete numerical facts following from the limb values
/// in `spec_eight_torsion`.  The function is `closed spec`, so its body
/// cannot be revealed; this axiom bridges the gap.
///
/// Runtime validation: `test_axiom_four_torsion_affine` in lizard_ristretto.rs.
pub proof fn axiom_four_torsion_affine()
    ensures
        edwards_point_as_affine(spec_eight_torsion()[2]) == (sqrt_m1(), 0nat),
        edwards_point_as_affine(spec_eight_torsion()[4]) == (0nat, field_neg(1)),
        edwards_point_as_affine(spec_eight_torsion()[6]) == (field_neg(sqrt_m1()), 0nat),
{
    admit();
}

// =============================================================================
// On-curve edge-case lemmas
// =============================================================================
/// On-curve with y = 0 implies x² = −1.
pub proof fn lemma_on_curve_y_zero_implies_x_sq_neg_one(x: nat, y: nat)
    requires
        is_on_edwards_curve(x, y),
        y == 0,
    ensures
        field_square(x) == field_neg(1),
{
    p_gt_2();
    lemma_small_mod(0nat, p());
    let x2 = field_square(x);
    let d = fe51_as_canonical_nat(&crate::backend::serial::u64::constants::EDWARDS_D);

    // y = 0 ⟹ y² = 0 ⟹ d·x²·y² = 0
    assert(field_mul(x2, field_square(0nat)) == 0) by {
        lemma_field_mul_zero_right(x2, 0nat);
    };
    assert(field_mul(d, 0nat) == 0) by {
        lemma_field_mul_zero_right(d, 0nat);
    };

    // Curve equation simplifies to −x² ≡ 1, i.e. x² = −1
    lemma_small_mod(1nat, p());
    assert(field_square(x) == field_neg(1)) by {
        lemma_field_neg_neg(x2);
        lemma_mod_bound((x * x) as int, p() as int);
        lemma_small_mod(x2, p());
    };
}

/// On-curve with x = 0 implies y = ±1.
pub proof fn lemma_on_curve_x_zero_implies_y_pm_one(x: nat, y: nat)
    requires
        is_on_edwards_curve(x, y),
        x == 0,
        y < p(),
    ensures
        y == 1 || y == field_neg(1),
{
    p_gt_2();
    lemma_small_mod(0nat, p());
    lemma_small_mod(1nat, p());

    let d = fe51_as_canonical_nat(&crate::backend::serial::u64::constants::EDWARDS_D);
    let x2 = field_square(x);
    let y2 = field_square(y);
    let x2y2 = field_mul(x2, y2);

    // x = 0 ⟹ x² = 0
    assert(x2 == 0);
    assert(x2y2 == 0) by {
        lemma_field_mul_zero_left(x2, y2);
    };
    assert(field_mul(d, x2y2) == 0) by {
        lemma_field_mul_zero_right(d, 0nat);
    };

    // Curve equation simplifies to y² = 1
    lemma_field_sub_eq_add_neg(y2, x2);
    assert(field_add(1nat, 0nat) == 1);
    assert(field_neg(x2) == 0) by {
        vstd::arithmetic::div_mod::lemma_mod_self_0(p() as int);
    };
    assert(y2 < p()) by {
        lemma_mod_bound((y * y) as int, p() as int);
    };
    lemma_small_mod(y2, p());

    assert(field_square(y) == 1);

    // y² ≡ 1 (mod p) with p prime ⟹ y = 1 or y = p − 1
    axiom_p_is_prime();
    lemma_square_root_of_unity(y, p());
    lemma_small_mod(y, p());
    lemma_small_mod((p() - 1) as nat, p());
}

/// a·z⁻¹ = 0 with z ≢ 0 implies a = 0.
// =============================================================================
// Edwards addition helpers for E[4] elements (fully proved)
// =============================================================================
/// x₁x₂ · y₁y₂ = 0 ⟹ edwards_add denominators are both 1.
///
/// Shared pattern for E[4]/E[2] addition where at least one input
/// has a zero coordinate, forcing x₁x₂·y₁y₂ = 0.
pub proof fn lemma_edwards_add_zero_coord_denom(x1x2: nat, y1y2: nat)
    requires
        field_mul(x1x2, y1y2) == 0,
    ensures
        ({
            let d = fe51_as_canonical_nat(&crate::backend::serial::u64::constants::EDWARDS_D);
            let t = field_mul(d, field_mul(x1x2, y1y2));
            &&& t == 0
            &&& field_add(1nat, t) == 1
            &&& field_sub(1nat, t) == 1
            &&& field_inv(field_add(1nat, t)) == 1
            &&& field_inv(field_sub(1nat, t)) == 1
        }),
{
    p_gt_2();
    lemma_small_mod(0nat, p());
    lemma_small_mod(1nat, p());
    let d = fe51_as_canonical_nat(&crate::backend::serial::u64::constants::EDWARDS_D);
    let t = field_mul(d, field_mul(x1x2, y1y2));
    assert(t == 0) by {
        lemma_field_mul_zero_right(d, 0nat);
    };
    let denom_x = field_add(1nat, t);
    let denom_y = field_sub(1nat, t);
    assert(denom_x == 1 && denom_y == 1) by {
        lemma_mod_add_multiples_vanish(1int, p() as int);
    };
    lemma_field_inv_one();
    assert(field_inv(denom_x) == 1 && field_inv(denom_y) == 1);
}

/// [2]·T₄ = O: doubling the 2-torsion (0, −1) gives identity (0, 1).
pub proof fn lemma_edwards_add_two_torsion_self()
    ensures
        edwards_add(0, field_neg(1), 0, field_neg(1)) == (0nat, 1nat),
{
    let neg1 = field_neg(1);
    p_gt_2();
    lemma_small_mod(0nat, p());
    lemma_small_mod(1nat, p());

    assert(field_mul(0nat, 0nat) == 0) by {
        lemma_field_mul_zero_left(0nat, 0nat);
    };
    assert(field_mul(0nat, neg1) == 0) by {
        lemma_field_mul_zero_left(0nat, neg1);
    };
    assert(field_mul(neg1, 0nat) == 0) by {
        lemma_field_mul_zero_right(neg1, 0nat);
    };
    assert(field_mul(neg1, neg1) == 1) by {
        lemma_neg_square_eq(1nat);
        lemma_small_mod(1nat, p());
    };

    let x1x2 = field_mul(0nat, 0nat);
    let y1y2 = field_mul(neg1, neg1);
    let x1y2 = field_mul(0nat, neg1);
    let y1x2 = field_mul(neg1, 0nat);
    assert(x1x2 == 0 && y1y2 == 1 && x1y2 == 0 && y1x2 == 0);

    assert(field_mul(x1x2, y1y2) == 0) by {
        lemma_field_mul_zero_left(x1x2, y1y2);
    };
    lemma_edwards_add_zero_coord_denom(x1x2, y1y2);

    assert(field_add(x1y2, y1x2) == 0);
    assert(field_add(y1y2, x1x2) == 1);
    assert(field_mul(0nat, 1nat) == 0) by {
        lemma_field_mul_zero_left(0nat, 1nat);
    };
    assert(field_mul(1nat, 1nat) == 1) by {
        lemma_field_mul_one_right(1nat);
    };
}

/// T₄ + T₂ = (−i, 0): adding 2-torsion to 4-torsion.
pub proof fn lemma_edwards_add_two_torsion_four_torsion(i_val: nat)
    requires
        i_val < p(),
        field_square(i_val) == field_neg(1),
    ensures
        edwards_add(0, field_neg(1), i_val, 0) == (field_neg(i_val), 0nat),
{
    let neg1 = field_neg(1);
    p_gt_2();
    lemma_small_mod(0nat, p());
    lemma_small_mod(1nat, p());

    assert(field_mul(0nat, i_val) == 0) by {
        lemma_field_mul_zero_left(0nat, i_val);
    };
    assert(field_mul(neg1, 0nat) == 0) by {
        lemma_field_mul_zero_right(neg1, 0nat);
    };
    assert(field_mul(0nat, 0nat) == 0) by {
        lemma_field_mul_zero_left(0nat, 0nat);
    };
    assert(field_mul(neg1, i_val) == field_neg(i_val)) by {
        lemma_field_neg_mul_left(1nat, i_val);
        lemma_field_mul_one_left(i_val);
        lemma_small_mod(i_val, p());
    };

    let x1x2 = field_mul(0nat, i_val);
    let y1y2 = field_mul(neg1, 0nat);
    let x1y2 = field_mul(0nat, 0nat);
    let y1x2 = field_mul(neg1, i_val);
    assert(x1x2 == 0 && y1y2 == 0 && x1y2 == 0);

    assert(field_mul(x1x2, y1y2) == 0) by {
        lemma_field_mul_zero_left(x1x2, y1y2);
    };
    lemma_edwards_add_zero_coord_denom(x1x2, y1y2);

    assert(field_neg(i_val) < p()) by {
        lemma_mod_bound(field_neg(i_val) as int, p() as int);
    };
    lemma_small_mod(field_neg(i_val), p());

    assert(field_add(x1y2, y1x2) == field_neg(i_val));
    assert(field_mul(field_neg(i_val), 1nat) == field_neg(i_val)) by {
        lemma_field_mul_one_right(field_neg(i_val));
    };

    assert(field_add(y1y2, x1x2) == 0);
    assert(field_mul(0nat, 1nat) == 0) by {
        lemma_field_mul_zero_left(0nat, 1nat);
    };
}

/// T₄ + T₆ = (i, 0): adding 2-torsion to the other 4-torsion point.
pub proof fn lemma_edwards_add_two_torsion_four_torsion_neg(i_val: nat)
    requires
        i_val < p(),
        field_square(i_val) == field_neg(1),
    ensures
        edwards_add(0, field_neg(1), field_neg(i_val), 0) == (i_val % p(), 0nat),
{
    let neg1 = field_neg(1);
    let neg_i = field_neg(i_val);
    p_gt_2();
    lemma_small_mod(0nat, p());
    lemma_small_mod(1nat, p());

    assert(field_mul(0nat, neg_i) == 0) by {
        lemma_field_mul_zero_left(0nat, neg_i);
    };
    assert(field_mul(neg1, 0nat) == 0) by {
        lemma_field_mul_zero_right(neg1, 0nat);
    };
    assert(field_mul(0nat, 0nat) == 0) by {
        lemma_field_mul_zero_left(0nat, 0nat);
    };
    assert(neg_i < p()) by {
        lemma_mod_bound(neg_i as int, p() as int);
    };
    lemma_small_mod(neg_i, p());
    assert(field_mul(neg1, neg_i) == i_val % p()) by {
        lemma_field_neg_mul_left(1nat, neg_i);
        lemma_field_mul_one_left(neg_i);
        lemma_field_neg_neg(i_val);
    };

    let x1x2 = field_mul(0nat, neg_i);
    let y1y2 = field_mul(neg1, 0nat);
    let x1y2 = field_mul(0nat, 0nat);
    let y1x2 = field_mul(neg1, neg_i);
    assert(x1x2 == 0 && y1y2 == 0 && x1y2 == 0);

    assert(field_mul(x1x2, y1y2) == 0) by {
        lemma_field_mul_zero_left(x1x2, y1y2);
    };
    lemma_edwards_add_zero_coord_denom(x1x2, y1y2);

    lemma_small_mod(i_val, p());
    assert(i_val % p() < p());
    lemma_small_mod(i_val % p(), p());
    assert(field_add(x1y2, y1x2) == i_val % p());
    assert(field_mul(i_val % p(), 1nat) == i_val % p()) by {
        lemma_field_mul_one_right(i_val % p());
        lemma_small_mod(i_val % p(), p());
    };

    assert(field_add(y1y2, x1x2) == 0);
    assert(field_mul(0nat, 1nat) == 0) by {
        lemma_field_mul_zero_left(0nat, 1nat);
    };
}

/// (x, 0) + (−x, 0) = O when x² = −1.
pub proof fn lemma_edwards_add_four_torsion_with_neg(x: nat)
    requires
        x < p(),
        field_square(x) == field_neg(1),
    ensures
        edwards_add(x, 0, field_neg(x), 0) == (0nat, 1nat),
{
    let neg_x = field_neg(x);
    p_gt_2();
    lemma_small_mod(0nat, p());
    lemma_small_mod(1nat, p());

    assert(field_mul(x, neg_x) == field_neg(field_mul(x, x))) by {
        lemma_field_mul_neg(x, x);
    };
    assert(field_neg(field_mul(x, x)) == field_neg(field_neg(1)));
    assert(field_neg(field_neg(1)) == 1) by {
        lemma_field_neg_neg(1nat);
        lemma_small_mod(1nat, p());
    };
    assert(field_mul(x, neg_x) == 1);
    assert(field_mul(0nat, 0nat) == 0) by {
        lemma_field_mul_zero_left(0nat, 0nat);
    };
    assert(field_mul(x, 0nat) == 0) by {
        lemma_field_mul_zero_right(x, 0nat);
    };
    assert(field_mul(0nat, neg_x) == 0) by {
        lemma_field_mul_zero_left(0nat, neg_x);
    };

    let x1x2 = field_mul(x, neg_x);
    let y1y2 = field_mul(0nat, 0nat);
    let x1y2 = field_mul(x, 0nat);
    let y1x2 = field_mul(0nat, neg_x);
    assert(x1x2 == 1 && y1y2 == 0 && x1y2 == 0 && y1x2 == 0);

    assert(field_mul(x1x2, y1y2) == 0) by {
        lemma_field_mul_one_left(0nat);
        lemma_small_mod(0nat, p());
    };
    lemma_edwards_add_zero_coord_denom(x1x2, y1y2);

    assert(field_add(x1y2, y1x2) == 0);
    assert(field_mul(0nat, 1nat) == 0) by {
        lemma_field_mul_zero_left(0nat, 1nat);
    };

    assert(field_add(y1y2, x1x2) == 1);
    assert(field_mul(1nat, 1nat) == 1) by {
        lemma_field_mul_one_right(1nat);
    };
}

/// (x, 0) + T₄ = (−x, 0): adding a 4-torsion point to the 2-torsion.
pub proof fn lemma_edwards_add_four_torsion_with_two_torsion(x: nat)
    requires
        x < p(),
    ensures
        edwards_add(x, 0, 0, field_neg(1)) == (field_neg(x), 0nat),
{
    let neg1 = field_neg(1);
    p_gt_2();
    lemma_small_mod(0nat, p());
    lemma_small_mod(1nat, p());

    assert(field_mul(x, 0nat) == 0) by {
        lemma_field_mul_zero_right(x, 0nat);
    };
    assert(field_mul(0nat, neg1) == 0) by {
        lemma_field_mul_zero_left(0nat, neg1);
    };
    assert(field_mul(0nat, 0nat) == 0) by {
        lemma_field_mul_zero_left(0nat, 0nat);
    };
    assert(field_mul(x, neg1) == field_neg(x)) by {
        lemma_field_mul_neg(x, 1nat);
        lemma_field_mul_one_right(x);
        lemma_small_mod(x, p());
    };

    let x1x2 = field_mul(x, 0nat);
    let y1y2 = field_mul(0nat, neg1);
    let x1y2 = field_mul(x, neg1);
    let y1x2 = field_mul(0nat, 0nat);
    assert(x1x2 == 0 && y1y2 == 0 && y1x2 == 0);

    assert(field_mul(x1x2, y1y2) == 0) by {
        lemma_field_mul_zero_left(x1x2, y1y2);
    };
    lemma_edwards_add_zero_coord_denom(x1x2, y1y2);

    assert(field_neg(x) < p()) by {
        lemma_mod_bound(field_neg(x) as int, p() as int);
    };
    lemma_small_mod(field_neg(x), p());
    assert(field_add(x1y2, y1x2) == field_neg(x));
    assert(field_mul(field_neg(x), 1nat) == field_neg(x)) by {
        lemma_field_mul_one_right(field_neg(x));
    };

    assert(field_add(y1y2, x1x2) == 0);
    assert(field_mul(0nat, 1nat) == 0) by {
        lemma_field_mul_zero_left(0nat, 1nat);
    };
}

} // verus!
