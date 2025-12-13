//! Lemmas for Edwards point decompression
//!
//! This module contains proofs for the `decompress` operation on Ed25519 points.
//! For step_1 lemmas (curve equation, validity), see `step1_lemmas.rs`.
//!
//! ## Key Properties Proven
//!
//! 1. **Extended coordinate correctness**: T = X·Y/Z for valid points with Z = 1
//! 2. **Negation preserves curve**: (-x, y) is on curve if (x, y) is
//! 3. **Sign bit correctness**: After conditional_negate, the sign bit matches
#![allow(unused_imports)]
use crate::backend::serial::u64::constants;
use crate::backend::serial::u64::constants::EDWARDS_D;
use crate::backend::serial::u64::field::FieldElement51;
use crate::edwards::EdwardsPoint;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::common_lemmas::sqrt_ratio_lemmas::*;
use crate::lemmas::edwards_lemmas::step1_lemmas::*;
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::specs::edwards_specs::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// Step 1 Helper Lemmas for decompress
// =============================================================================
//
// These lemmas organize the step_1 proof into three phases:
// 1. Limb bounds: Preconditions for field operations
// 2. sqrt_ratio_i postconditions: Properties of the computed X
// 3. Curve semantics: Connecting to math_is_valid_y and math_on_edwards_curve
/// Phase 1: Limb bounds are established for sqrt_ratio_i preconditions
///
/// This lemma documents that:
/// - Y from from_bytes has 51-bit bounded limbs
/// - Z = ONE has 51-bit bounded limbs
/// - After operations, u and v have 54-bit bounded limbs (for sqrt_ratio_i)
pub proof fn lemma_step1_limb_bounds_established()
    ensures
// ONE has 51-bit and 54-bit bounded limbs

        fe51_limbs_bounded(&FieldElement51::ONE, 51),
        fe51_limbs_bounded(&FieldElement51::ONE, 54),
        // EDWARDS_D has 54-bit bounded limbs
        fe51_limbs_bounded(&EDWARDS_D, 54),
{
    use crate::lemmas::field_lemmas::constants_lemmas::*;
    use crate::lemmas::edwards_lemmas::constants_lemmas::*;

    lemma_one_limbs_bounded();
    lemma_one_limbs_bounded_54();
    lemma_edwards_d_limbs_bounded_54();
}

/// Main Lemma: decompress produces a valid Edwards point
///
/// When Z = 1 and (X, Y) is on the curve with T = X * Y,
/// the result is a valid Edwards point.
pub proof fn lemma_decompress_produces_valid_point(
    x: nat,
    y: nat,
    z: nat,
    t: nat,
    sign_applied: bool,
)
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
// Sign Bit Lemmas
// =============================================================================
/// Lemma: After conditional_negate based on sign_bit, the result has the correct sign
///
/// ## Mathematical Proof
/// ```text
/// sqrt_ratio_i returns the non-negative root (LSB = 0)
/// conditional_negate flips the sign when sign_bit = 1
///
/// Case sign_bit = 0: result = x % p (even), LSB = 0 ✓
/// Case sign_bit = 1: result = -x = p - x
///                    Since p is odd and x is even: odd - even = odd
///                    So LSB = 1 ✓
/// ```
pub proof fn lemma_sign_bit_after_conditional_negate(x: nat, sign_bit: u8)
    requires
        (x % p()) % 2 == 0,  // x is non-negative root (LSB = 0)
        sign_bit == 0 || sign_bit == 1,
        sign_bit == 1 ==> x % p() != 0,  // if asking for odd, x ≠ 0

    ensures
        ({
            let result = if sign_bit == 1 {
                math_field_neg(x)
            } else {
                x % p()
            };
            (result % 2) as u8 == sign_bit
        }),
{
    let pval = p();
    let x_red = x % pval;
    let result = if sign_bit == 1 {
        math_field_neg(x)
    } else {
        x % pval
    };

    // Goal: LSB(result) = sign_bit
    assert((result % 2) as u8 == sign_bit) by {
        lemma_p_is_odd();  // p is odd

        if sign_bit == 0 {
            // Case: sign_bit = 0 → result = x % p (even)
            assert(result == x_red);
            assert(result % 2 == 0);
        } else {
            // Case: sign_bit = 1 → result = -x = p - x_red
            let neg_x = (pval - x_red) as nat;

            assert(result % 2 == 1) by {
                p_gt_2();

                assert(result == neg_x) by {
                    lemma_small_mod(neg_x, pval);
                };

                // (p - x_red) % 2 = (odd - even) % 2 = 1
                assert(neg_x % 2 == 1) by {
                    lemma_sub_mod_noop(pval as int, x_red as int, 2int);
                };
            };
        }
    };
}

// =============================================================================
// Sign Bit Correctness for Decompress
// =============================================================================
/// Top-level lemma for decompress sign bit using concrete field element
///
/// Connects to spec_field_element_sign_bit: ((x % p) % 2) as u8
pub proof fn lemma_decompress_field_element_sign_bit(
    x_before_negate: nat,
    x_after_negate: nat,
    repr_byte_31: u8,
)
    requires
        (x_before_negate % p()) % 2 == 0,  // sqrt_ratio_i returns even
        (repr_byte_31 >> 7) == 1 ==> x_before_negate % p() != 0,  // x ≠ 0 when negating
        x_after_negate == if (repr_byte_31 >> 7) == 1 {
            math_field_neg(x_before_negate)
        } else {
            x_before_negate % p()
        },
    ensures
        ((x_after_negate % p()) % 2) as u8 == (repr_byte_31 >> 7),
{
    let sign_bit = repr_byte_31 >> 7;

    // sign_bit ∈ {0, 1}
    assert(sign_bit == 0 || sign_bit == 1) by (bit_vector)
        requires
            sign_bit == repr_byte_31 >> 7,
    ;

    // (x_after % 2) as u8 == sign_bit
    assert((x_after_negate % 2) as u8 == sign_bit) by {
        lemma_sign_bit_after_conditional_negate(x_before_negate, sign_bit);
    }

    // x_after < p, so x_after % p = x_after
    assert(x_after_negate % p() == x_after_negate) by {
        assert(x_after_negate < p()) by {
            p_gt_2();
            if sign_bit == 1 {
                lemma_mod_bound((p() as int - (x_before_negate % p()) as int), p() as int);
            } else {
                lemma_mod_bound(x_before_negate as int, p() as int);
            }
        }
        lemma_small_mod(x_after_negate, p());
    }
}

// =============================================================================
// Curve Equation Lemmas
// =============================================================================
/// Lemma: If x = 0 (mod p) and (x, y) is on the Edwards curve, then y² = 1 (mod p)
///
/// ## Mathematical Proof
///
/// From the curve equation: y² - x² = 1 + d·x²·y² (mod p)
///
/// If x ≡ 0 (mod p):
/// - x² = (x * x) % p = (0 * 0) % p = 0
/// - x²·y² = 0 * y² = 0
/// - Curve becomes: y² - 0 = 1 + d·0
/// - Therefore: y² = 1 (mod p)
pub proof fn lemma_x_zero_implies_y_squared_one(x: nat, y: nat)
    requires
        math_on_edwards_curve(x, y),
        x % p() == 0,
    ensures
        math_field_square(y) == 1,
{
    let modulus = p();
    let d = spec_field_element(&EDWARDS_D);
    let x2 = math_field_square(x);
    let y2 = math_field_square(y);
    let x2y2 = math_field_mul(x2, y2);
    let d_x2y2 = math_field_mul(d, x2y2);
    let lhs = math_field_sub(y2, x2);
    let rhs = math_field_add(1, d_x2y2);

    // Establish p > 1 for lemma preconditions
    assert(modulus > 1) by {
        p_gt_2();
    };

    // Goal: y² = 1
    // Strategy: From curve equation y² - x² = 1 + d·x²·y², show all terms simplify

    assert(x2 == 0) by {
        // x² = (x * x) % p = ((x % p) * (x % p)) % p = (0 * 0) % p = 0
        lemma_mul_mod_noop_general(x as int, x as int, modulus as int);
        assert((x * x) % modulus == ((x % modulus) * (x % modulus)) % modulus);
    };

    assert(x2y2 == 0) by {
        // x²·y² = 0 * y² = 0
        assert(x2 == 0);
        lemma_mul_by_zero_is_zero(y2 as int);
        lemma_small_mod(0nat, modulus);
    };

    assert(d_x2y2 == 0) by {
        // d * x²y² = d * 0 = 0
        assert(x2y2 == 0);
        lemma_mul_by_zero_is_zero(d as int);
    };

    assert(rhs == 1) by {
        // rhs = (1 + d·x²·y²) % p = (1 + 0) % p = 1 % p = 1
        assert(d_x2y2 == 0);
        lemma_small_mod(1nat, modulus);
    };

    // From curve equation (precondition): lhs == rhs
    assert(lhs == rhs);
    assert(lhs == 1);

    assert(lhs == y2) by {
        // lhs = math_field_sub(y2, 0) = (y2 + p) % p = y2
        assert(x2 == 0);

        // y2 < p (math_field_square output is reduced)
        assert(y2 < modulus) by {
            lemma_mod_bound(y as int * y as int, modulus as int);
        };

        // (p + y2) % p = y2 % p = y2 (since y2 < p)
        lemma_small_mod(y2, modulus);
        lemma_mod_multiples_vanish(1int, y2 as int, modulus as int);
    };

    // Conclusion: y2 == lhs == 1
    assert(y2 == 1);
}

/// Lemma: From compressed_y_has_valid_sign_bit, derive that sign_bit=1 implies x≠0
///
/// ## Mathematical Proof
///
/// The twisted Edwards curve equation is: -x² + y² = 1 + d·x²·y²
/// Rearranging: y² - 1 = x²(1 + d·y²)
///
/// If x = 0, then y² - 1 = 0, so y² = 1.
/// Contrapositive: If y² ≠ 1, then x ≠ 0.
///
/// From precondition: sign_bit = 1 ==> y² ≠ 1
/// From curve: y² ≠ 1 ==> x ≠ 0
/// Combined: sign_bit = 1 ==> x ≠ 0
pub proof fn lemma_sign_bit_one_implies_x_nonzero(bytes: &[u8; 32], x: nat, y: nat)
    requires
        compressed_y_has_valid_sign_bit(bytes),  // decompress precondition
        y == spec_field_element_from_bytes(bytes),  // Y from bytes
        math_on_edwards_curve(x, y),  // (x, y) on curve
        x < p(),  // X bounded

    ensures
// If sign bit is 1, x must be non-zero (since -0 = 0)

        (bytes[31] >> 7) == 1 ==> x % p() != 0,
{
    let sign_bit = bytes[31] >> 7;
    let y_sq = math_field_square(y);

    if sign_bit == 1 {
        // From compressed_y_has_valid_sign_bit: y² == 1 ==> sign_bit == 0
        // Contrapositive: sign_bit == 1 ==> y² != 1
        assert(y_sq != 1);

        // From curve equation and y² != 1, x must be non-zero (contrapositive)
        assert(x % p() != 0) by {
            // If x % p == 0, then by lemma_x_zero_implies_y_squared_one, y² == 1
            // But we have y² != 1, contradiction
            if x % p() == 0 {
                lemma_x_zero_implies_y_squared_one(x, y);
            }
        };
    }
}

// =============================================================================
// Main Decompress Lemma
// =============================================================================
/// Main lemma for decompress valid branch: proves all postconditions for Some(point).
/// It takes the mathematical values and the final point, proving the ensures clauses.
///
/// ## Parameters
/// - `repr_bytes`: The compressed representation bytes
/// - `x_orig`: The X value from step_1 (before conditional negate)
/// - `y`: The Y value from step_1
/// - `point`: The final EdwardsPoint from step_2
///
/// ## Proves
/// - is_valid_edwards_point(point)
/// - spec_field_element(&point.Y) == spec_field_element_from_bytes(repr_bytes)
/// - spec_field_element_sign_bit(&point.X) == (repr_bytes[31] >> 7)
pub proof fn lemma_decompress_valid_branch(
    repr_bytes: &[u8; 32],
    x_orig: nat,
    y: nat,
    point: &EdwardsPoint,
)
    requires
        compressed_y_has_valid_sign_bit(repr_bytes),
        // step_1 postconditions (as nat values)
        y == spec_field_element_from_bytes(repr_bytes),
        math_on_edwards_curve(x_orig, y),
        // X is non-negative root (LSB = 0) and bounded
        (x_orig % p()) % 2 == 0,
        x_orig < p(),
        // step_2 postconditions
        spec_field_element(&point.X) == (if (repr_bytes[31] >> 7) == 1 {
            math_field_neg(x_orig)
        } else {
            x_orig
        }),
        spec_field_element(&point.Y) == y,
        spec_field_element(&point.Z) == 1,
        spec_field_element(&point.T) == math_field_mul(
            spec_field_element(&point.X),
            spec_field_element(&point.Y),
        ),
    ensures
        is_valid_edwards_point(*point),
        spec_field_element(&point.Y) == spec_field_element_from_bytes(repr_bytes),
        spec_field_element_sign_bit(&point.X) == (repr_bytes[31] >> 7),
{
    let x_final = spec_field_element(&point.X);
    let y_final = spec_field_element(&point.Y);
    let z_final = spec_field_element(&point.Z);
    let t_final = spec_field_element(&point.T);
    let sign_bit = repr_bytes[31] >> 7;

    // =========================================================================
    // Goal 1: is_valid_edwards_point(point)
    // =========================================================================
    assert(is_valid_edwards_point(*point)) by {
        // Establish that (x_final, y_final) is on curve
        assert(math_on_edwards_curve(x_final, y_final)) by {
            // X is conditionally negated; negation preserves curve membership
            if sign_bit == 1 {
                assert(x_final == math_field_neg(x_orig));
                lemma_negation_preserves_curve(x_orig, y);
            } else {
                assert(x_final == x_orig);
            }
        };

        // Z = 1, Y preserved, T = X * Y
        assert(z_final == 1);
        assert(y_final == y);
        assert(t_final == math_field_mul(x_final, y_final));

        // Apply the validity lemma
        lemma_decompress_produces_valid_point(x_final, y_final, z_final, t_final, sign_bit == 1);
    };

    // =========================================================================
    // Goal 2: Y coordinate preserved
    // =========================================================================
    assert(spec_field_element(&point.Y) == spec_field_element_from_bytes(repr_bytes)) by {
        assert(spec_field_element(&point.Y) == y);
        // y == spec_field_element_from_bytes(repr_bytes) from requires
    };

    // =========================================================================
    // Goal 3: Sign bit correctness
    // =========================================================================
    assert(spec_field_element_sign_bit(&point.X) == (repr_bytes[31] >> 7)) by {
        let x_before = x_orig;
        let x_after = x_final;
        let repr_byte_31 = repr_bytes[31];

        // ((x_after % p) % 2) as u8 == sign_bit
        assert(((x_after % p()) % 2) as u8 == (repr_byte_31 >> 7)) by {
            // Precondition 1: sqrt_ratio_i returns non-negative root (LSB = 0)
            assert((x_before % p()) % 2 == 0);

            // Precondition 2: sign_bit == 1 ==> x != 0
            assert((repr_byte_31 >> 7) == 1 ==> x_before % p() != 0) by {
                lemma_sign_bit_one_implies_x_nonzero(repr_bytes, x_before, y);
            };

            // Precondition 3: x_after matches conditional expression
            assert(x_after == if (repr_byte_31 >> 7) == 1 {
                math_field_neg(x_before)
            } else {
                x_before % p()
            }) by {
                lemma_small_mod(x_before, p());
            };

            lemma_decompress_field_element_sign_bit(x_before, x_after, repr_byte_31);
        };
    };
}

} // verus!
