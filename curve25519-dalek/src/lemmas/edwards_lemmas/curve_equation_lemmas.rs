//! Lemmas about the Edwards curve equation
//!
//! This module contains proofs for general properties of the twisted Edwards curve
//! equation and coordinate representations. These are fundamental mathematical facts
//! about the curve, not specific to any particular operation.
//!
//! ## Key Properties Proven
//!
//! 1. **Negation preserves curve**: (-x, y) is on the curve if (x, y) is (since x² = (-x)²)
//! 2. **Affine to extended validity**: (x, y, 1, xy) is a valid extended point when (x, y) is on curve
#![allow(unused_imports)]
use crate::backend::serial::u64::constants::EDWARDS_D;
use crate::backend::serial::u64::field::FieldElement51;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::specs::edwards_specs::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// Negation Lemmas
// =============================================================================
/// Lemma: Negation preserves the curve equation
///
/// If (x, y) is on the curve, then (-x, y) is also on the curve.
/// This is because the curve equation involves x² which is the same for x and -x.
pub proof fn lemma_negation_preserves_curve(x: nat, y: nat)
    requires
        math_on_edwards_curve(x, y),
    ensures
        math_on_edwards_curve(math_field_neg(x), y),
{
    // Goal: on_curve(-x, y)
    // Strategy: The curve equation uses x², and (-x)² = x², so the equation is identical
    //
    //   y² - (-x)² = 1 + d·(-x)²·y²
    //   y² - x²    = 1 + d·x²·y²      (same equation!)
    //
    // The precondition says (x, y) satisfies this, so (-x, y) does too.
    let neg_x = math_field_neg(x);

    assert(math_on_edwards_curve(neg_x, y)) by {
        // Key insight: (-x)² = x²
        assert(math_field_square(neg_x) == math_field_square(x)) by {
            lemma_neg_square_eq(x);  // (-x)² = (x % p)²
            lemma_square_mod_noop(x);  // (x % p)² = x²
        };
        // With (-x)² = x², the curve equations are identical
    };
}

// =============================================================================
// Extended Coordinates Validity
// =============================================================================
/// Lemma: Converting affine coordinates to extended coordinates yields a valid point
///
/// When (x, y) is on the Edwards curve, the extended representation (x, y, 1, x·y)
/// is a valid extended Edwards point.
///
/// ## Mathematical Proof
///
/// For extended coordinates (X:Y:Z:T) to be valid, we need:
/// 1. Z ≠ 0
/// 2. (X/Z, Y/Z) is on the curve
/// 3. T = X·Y/Z
///
/// With Z = 1:
/// - Z ≠ 0 ✓
/// - (X/1, Y/1) = (X, Y) is on curve (given)
/// - T = X·Y/1 = X·Y ✓
pub proof fn lemma_affine_to_extended_valid(x: nat, y: nat, z: nat, t: nat)
    requires
        z == 1,
        math_on_edwards_curve(x, y),
        t == math_field_mul(x, y),
    ensures
        math_is_valid_edwards_point_xyzt(x, y, z, t),
{
    // Goal: Show (X:Y:Z:T) with Z=1 is a valid extended point
    //
    // Need to prove:
    //   1. Z ≠ 0
    //   2. (X/Z, Y/Z) is on curve
    //   3. T = X·Y/Z
    let p = p();
    p_gt_2();

    // Part 1: Z = 1 ≠ 0
    assert(z != 0);

    // Part 2: (X/Z, Y/Z) is on curve
    assert(math_on_edwards_curve(
        math_field_mul(x, math_field_inv(z)),
        math_field_mul(y, math_field_inv(z)),
    )) by {
        // Since Z = 1, inv(Z) = 1
        assert(math_field_inv(z) == 1) by {
            lemma_field_inv_one();
        };

        // X · inv(Z) = X · 1 = X % p
        assert(math_field_mul(x, math_field_inv(z)) == (x * 1) % p);
        assert(math_field_mul(y, math_field_inv(z)) == (y * 1) % p);

        // on_curve(X % p, Y % p) ⟺ on_curve(X, Y) via square_mod_noop
        // (inlined from lemma_curve_mod_noop)
        lemma_square_mod_noop(x);
        lemma_square_mod_noop(y);
    };

    // Part 3: T = X·Y/Z
    assert(t == math_field_mul(math_field_mul(x, y), math_field_inv(z))) by {
        lemma_field_inv_one();
        let xy = math_field_mul(x, y);
        // xy < p (mod result), so xy · 1 = xy
        assert(xy < p) by {
            lemma_mod_bound((x * y) as int, p as int);
        };
        lemma_small_mod(xy, p);
        assert(math_field_mul(xy, math_field_inv(z)) == xy);
        // t = xy (from precondition)
    };
}

} // verus!
