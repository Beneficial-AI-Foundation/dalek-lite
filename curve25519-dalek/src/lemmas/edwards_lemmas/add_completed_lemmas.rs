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

// =============================================================================
// Pure mathematical axiom
// =============================================================================
// This is the ONLY irreducible mathematical assumption in this module.
// Everything else (FOIL, PP/MM, factor cancellation, exec bridges) is
// algebraically derivable from this axiom plus existing field lemmas.
/// Core mathematical axiom: Edwards curve addition is complete and closed.
///
/// For the twisted Edwards curve -x² + y² = 1 + d·x²·y² where d is a non-square
/// in F_p, if both input points lie on the curve, then:
///   1. The addition denominators 1 ± d·x₁x₂y₁y₂ are non-zero
///      (completeness — the formula has no exceptional cases)
///   2. The result of `edwards_add` lies on the curve (closure under addition)
///
/// This is a standard result for complete twisted Edwards curves.
/// Reference: Bernstein, Birkner, Joye, Lange, Peters (2008), Section 6.
///
/// Proof sketch: d non-square in F_p implies that for any (x₁,y₁), (x₂,y₂)
/// on the curve, d·x₁²·x₂²·y₁²·y₂² ≠ 1. This makes both 1 ± d·x₁x₂y₁y₂ ≠ 0.
/// Closure follows by direct algebraic verification of the curve equation.
///
/// To fully formalize, one would need to:
/// (a) Prove d is a non-square in F_p for the specific Ed25519 constant d
///     (can be done computationally for this concrete value)
/// (b) Use the non-square property to show d·x₁²x₂²y₁²y₂² ≠ 1
///     (standard argument: if d·r² = 1 then d = (1/r)², contradicting d non-square)
/// (c) Verify the curve equation on the result by expanding edwards_add
///     and simplifying using the curve equations for (x₁,y₁) and (x₂,y₂)
pub proof fn axiom_edwards_add_complete(x1: nat, y1: nat, x2: nat, y2: nat)
    requires
        math_on_edwards_curve(x1, y1),
        math_on_edwards_curve(x2, y2),
    ensures
        ({
            let d = fe51_as_canonical_nat(&EDWARDS_D);
            let t = field_mul(d, field_mul(field_mul(x1, x2), field_mul(y1, y2)));
            field_add(1, t) != 0 && field_sub(1, t) != 0
        }),
        math_on_edwards_curve(edwards_add(x1, y1, x2, y2).0, edwards_add(x1, y1, x2, y2).1),
{
    admit();
}

// =============================================================================
// Pure math helper lemmas (proven)
// =============================================================================
/// Negation preserves the Edwards curve equation: if (x, y) is on the curve,
/// so is (-x, y). This follows from (-x)² = x² in the field.
pub proof fn lemma_neg_preserves_curve(x: nat, y: nat)
    requires
        math_on_edwards_curve(x, y),
    ensures
        math_on_edwards_curve(field_neg(x), y),
{
    let neg_x = field_neg(x);
    let pp = p();
    p_gt_2();

    // Step 1: square(neg(x)) == square(x % p) by lemma_neg_square_eq
    lemma_neg_square_eq(x);

    // Step 2: square(x % p) == square(x) by modular arithmetic
    assert(field_square(x % p()) == field_square(x)) by {
        // (x*x)%p == (x*(x%p))%p
        lemma_mul_mod_noop_right(x as int, x as int, pp as int);
        // ((x%p)*x)%p == ((x%p)*(x%p))%p
        lemma_mul_mod_noop_right((x % pp) as int, x as int, pp as int);
        // x*(x%p) == (x%p)*x by integer commutativity (automatic)
    };

    // Step 3: square(neg(x)) == square(x)
    let neg_x_sq = field_square(neg_x);
    let x_sq = field_square(x);
    let y_sq = field_square(y);
    let d = fe51_as_canonical_nat(&EDWARDS_D);

    // Since neg(x)² = x², all derived curve equation terms are identical
    assert(neg_x_sq == x_sq);
    assert(field_mul(neg_x_sq, y_sq) == field_mul(x_sq, y_sq));
    assert(field_sub(y_sq, neg_x_sq) == field_sub(y_sq, x_sq));
    assert(field_mul(d, field_mul(neg_x_sq, y_sq)) == field_mul(d, field_mul(x_sq, y_sq)));
}

/// Given abstract CompletedPoint values that are 2x the edwards_add numerators
/// and denominators, the ratios X/Z and Y/T equal the edwards_add result.
///
/// This bridges the factor-of-2 representation used in the P1xP1 formulas
/// (PP-MM, PP+MM, 2ZZ+TT2d, 2ZZ-TT2d) to the affine edwards_add formula.
/// Proven from axiom_edwards_add_complete (denominator non-zero) and
/// lemma_cancel_common_factor (to cancel the common factor of 2).
pub proof fn lemma_completed_point_ratios(
    x1: nat,
    y1: nat,
    x2: nat,
    y2: nat,
    result_x: nat,
    result_y: nat,
    result_z: nat,
    result_t: nat,
)
    requires
        math_on_edwards_curve(x1, y1),
        math_on_edwards_curve(x2, y2),
        result_x == field_mul(2, field_add(field_mul(x1, y2), field_mul(y1, x2))),
        result_y == field_mul(2, field_add(field_mul(y1, y2), field_mul(x1, x2))),
        result_z == field_mul(
            2,
            field_add(
                1,
                field_mul(
                    fe51_as_canonical_nat(&EDWARDS_D),
                    field_mul(field_mul(x1, x2), field_mul(y1, y2)),
                ),
            ),
        ),
        result_t == field_mul(
            2,
            field_sub(
                1,
                field_mul(
                    fe51_as_canonical_nat(&EDWARDS_D),
                    field_mul(field_mul(x1, x2), field_mul(y1, y2)),
                ),
            ),
        ),
    ensures
        result_z != 0,
        result_t != 0,
        field_mul(result_x, field_inv(result_z)) == edwards_add(x1, y1, x2, y2).0,
        field_mul(result_y, field_inv(result_t)) == edwards_add(x1, y1, x2, y2).1,
        math_on_edwards_curve(
            field_mul(result_x, field_inv(result_z)),
            field_mul(result_y, field_inv(result_t)),
        ),
{
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let x1y2 = field_mul(x1, y2);
    let y1x2 = field_mul(y1, x2);
    let y1y2 = field_mul(y1, y2);
    let x1x2 = field_mul(x1, x2);
    let t = field_mul(d, field_mul(x1x2, y1y2));
    let denom_x = field_add(1, t);
    let denom_y = field_sub(1, t);
    let num_x = field_add(x1y2, y1x2);
    let num_y = field_add(y1y2, x1x2);
    let two: nat = 2;

    // From pure math axiom: denominators non-zero and result on curve
    axiom_edwards_add_complete(x1, y1, x2, y2);

    // 2 is non-zero mod p (since p > 2)
    p_gt_2();
    assert(two % p() != 0) by {
        lemma_small_mod(two, p());
    };

    // denom_x, denom_y are < p (results of modular reduction), hence denom % p = denom
    assert(denom_x % p() != 0) by {
        lemma_small_mod(denom_x, p());
    };
    assert(denom_y % p() != 0) by {
        lemma_small_mod(denom_y, p());
    };

    // result_z = mul(2, denom_x) != 0 (product of non-zero field elements)
    lemma_field_mul_comm(two, denom_x);
    lemma_nonzero_product(denom_x, two);

    // result_t = mul(2, denom_y) != 0
    lemma_field_mul_comm(two, denom_y);
    lemma_nonzero_product(denom_y, two);

    // Factor cancellation for x-coordinate:
    // result_x/result_z = mul(2,num_x)/mul(2,denom_x) = num_x/denom_x = edwards_add.0
    lemma_field_mul_comm(two, num_x);
    lemma_cancel_common_factor(num_x, denom_x, two);

    // Factor cancellation for y-coordinate:
    // result_y/result_t = mul(2,num_y)/mul(2,denom_y) = num_y/denom_y = edwards_add.1
    lemma_field_mul_comm(two, num_y);
    lemma_cancel_common_factor(num_y, denom_y, two);

    // On curve: axiom_edwards_add_complete ensures math_on_edwards_curve(edwards_add(...)...)
    // Since result_x/result_z == edwards_add.0 and result_y/result_t == edwards_add.1,
    // the CompletedPoint affine coords are on curve.
}

// =============================================================================
// Exec bridge axioms: CompletedPoint correctness
// =============================================================================
// These axioms connect exec-level computation (FieldElement51 structs and
// ProjectiveNiels/AffineNiels representations) to the spec-level edwards_add.
//
// They depend on:
//   1. axiom_edwards_add_complete (pure math — denominators non-zero, curve closure)
//   2. FOIL/PP-MM lemmas above (proven — algebraic identities)
//   3. lemma_completed_point_ratios (proven — factor-of-2 cancellation)
//   4. Extended coordinate algebra: connecting T·Z = X·Y and Niels form
//      (Y+X, Y-X, Z, T2d) to affine coordinates
//
// Once (4) is proven, these axioms become fully proven lemmas. The key steps
// for (4) are:
//   - Factor Z1·Z2 out of PP-MM and PP+MM using the projective-to-affine relation
//     Y_i = y_i·Z_i, X_i = x_i·Z_i
//   - Connect TT2d to d·x1·x2·y1·y2·Z1·Z2 using the extended coordinate
//     invariant T·Z = X·Y and the Niels T2d = 2d·T definition
//   - Cancel the common Z1·Z2 factor via lemma_cancel_common_factor
//   - Apply lemma_completed_point_ratios for the final formula match
//
// The sub variants follow from the add variants via edwards_sub = edwards_add ∘ neg:
//   - Swapping Y_plus_X/Y_minus_X in the Niels point corresponds to negating x2
//   - Swapping Z/T in the result reflects the sign change in 1 ± d·x₁x₂y₁y₂
//   - lemma_neg_preserves_curve ensures the negated point is still on curve
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
    // === SETUP: Extract projective coordinates ===
    let sX = fe51_as_canonical_nat(&self_point.X);
    let sY = fe51_as_canonical_nat(&self_point.Y);
    let sZ = fe51_as_canonical_nat(&self_point.Z);
    let sT = fe51_as_canonical_nat(&self_point.T);
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    p_gt_2();

    // sZ, sX, sY, sT are < p (fe51_as_canonical_nat returns values mod p)
    assert(sZ != 0);  // from is_valid_edwards_point: Z != 0
    assert(sZ % p() != 0) by {
        lemma_field_element_reduced(sZ);
    };

    // === Extract witness from is_valid_projective_niels_point ===
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

    // Segre relations
    assert(field_mul(sX, sY) == field_mul(sZ, sT));
    assert(field_mul(X2, Y2) == field_mul(Z2, T2));

    // === From correspondence: relate Niels fields to (X2, Y2, Z2, T2) ===
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

    // === Affine coordinates ===
    let x1 = field_mul(sX, field_inv(sZ));
    let y1 = field_mul(sY, field_inv(sZ));
    let x2 = field_mul(X2, field_inv(Z2));
    let y2 = field_mul(Y2, field_inv(Z2));

    // On-curve from axiom_valid_extended_point_affine_on_curve
    axiom_valid_extended_point_affine_on_curve(sX, sY, sZ, sT);
    axiom_valid_extended_point_affine_on_curve(X2, Y2, Z2, T2);

    // === STEP 1: FOIL on PP and MM ===
    // pp_val = mul(add(sY,sX), add(Y2,X2)) and mm_val = mul(sub(sY,sX), sub(Y2,X2))
    // By FOIL: PP - MM = 2*(sY*X2 + sX*Y2) and PP + MM = 2*(sY*Y2 + sX*X2)
    lemma_pp_minus_mm(sY, sX, Y2, X2);
    lemma_pp_plus_mm(sY, sX, Y2, X2);

    let result_x = field_sub(pp_val, mm_val);
    let result_y = field_add(pp_val, mm_val);
    assert(result_x == field_mul(2, field_add(field_mul(sY, X2), field_mul(sX, Y2))));
    assert(result_y == field_mul(2, field_add(field_mul(sY, Y2), field_mul(sX, X2))));

    // === STEP 2: Factor Z1*Z2 from projective products ===
    let z1z2 = field_mul(sZ, Z2);

    // sY * X2 = (y1*sZ) * (x2*Z2) = (y1*x2) * (sZ*Z2) = mul(mul(y1,x2), z1z2)
    // Using div_mul_cancel: mul(y1, sZ) = sY (since y1 = sY/sZ)
    // Similarly: mul(x2, Z2) = X2
    assert(field_mul(sY, X2) == field_mul(field_mul(y1, x2), z1z2)) by {
        lemma_four_factor_rearrange(y1, sZ, x2, Z2);
        // mul(mul(y1,sZ), mul(x2,Z2)) = mul(mul(y1,x2), mul(sZ,Z2))
        // But mul(y1, sZ) = sY? We need: mul(mul(sY*inv(sZ)), sZ) = sY
        lemma_div_mul_cancel(sY, sZ);
        lemma_div_mul_cancel(X2, Z2);
        // mul(y1, sZ) = sY % p = sY (since sY < p)
        lemma_field_element_reduced(sY);
        lemma_field_element_reduced(X2);
        // Now: mul(sY, X2) = mul(mul(y1,sZ), mul(x2,Z2)) = mul(mul(y1,x2), mul(sZ,Z2))
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

    // Numerator factoring: sY*X2 + sX*Y2 = z1z2 * (y1*x2 + x1*y2)
    let y1x2 = field_mul(y1, x2);
    let x1y2 = field_mul(x1, y2);
    let y1y2 = field_mul(y1, y2);
    let x1x2 = field_mul(x1, x2);

    assert(field_add(field_mul(sY, X2), field_mul(sX, Y2)) == field_mul(
        z1z2,
        field_add(y1x2, x1y2),
    )) by {
        // mul(y1x2, z1z2) + mul(x1y2, z1z2) = mul(y1x2 + x1y2, z1z2) = mul(z1z2, y1x2+x1y2)
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

    // result_x = mul(2, z1z2 * (y1x2 + x1y2)) = mul(z1z2, mul(2, y1x2+x1y2))
    let num_x = field_add(y1x2, x1y2);
    let num_y = field_add(y1y2, x1x2);

    // === STEP 3: TT2d expansion using Segre ===
    // tt2d_val = mul(sT, mul(2d, T2))
    // From Segre: sT = mul(sX,sY)*inv(sZ) and T2 = mul(X2,Y2)*inv(Z2)
    // sT * T2 = x1*y1*sZ * x2*y2*Z2 = x1*y1*x2*y2 * z1z2
    // tt2d_val = 2*d * x1*y1*x2*y2 * z1z2

    // First show: sT = mul(mul(x1, y1), sZ)
    // From Segre: mul(sZ, sT) = mul(sX, sY)
    // And mul(sX, sY) = mul(mul(x1,sZ), mul(y1,sZ)) = mul(mul(x1,y1), mul(sZ,sZ))
    // So mul(sZ, sT) = mul(mul(x1,y1), mul(sZ,sZ))
    // sT = mul(x1,y1) * sZ [dividing by sZ]
    let x1y1 = field_mul(x1, y1);
    let x2y2 = field_mul(x2, y2);

    // mul(sX, sY) = mul(x1y1, mul(sZ, sZ)) by four-factor rearrangement
    assert(field_mul(sX, sY) == field_mul(x1y1, field_mul(sZ, sZ))) by {
        lemma_four_factor_rearrange(x1, sZ, y1, sZ);
        lemma_div_mul_cancel(sX, sZ);
        lemma_div_mul_cancel(sY, sZ);
        lemma_field_element_reduced(sX);
        lemma_field_element_reduced(sY);
    };

    // From Segre: mul(sZ, sT) = mul(x1y1, mul(sZ, sZ)) = mul(x1y1, sZ) * sZ
    // So sT = mul(x1y1, sZ) [cancel sZ from both sides]
    assert(sT == field_mul(x1y1, sZ) % p()) by {
        // mul(sZ, sT) = mul(x1y1, mul(sZ, sZ))
        // mul(x1y1, mul(sZ, sZ)) = mul(mul(x1y1, sZ), sZ) [by assoc]
        lemma_field_mul_assoc(x1y1, sZ, sZ);
        // So mul(sZ, sT) = mul(mul(x1y1, sZ), sZ)
        // By commutativity: mul(sZ, sT) = mul(sZ, sT) and mul(mul(x1y1,sZ), sZ) = mul(sZ, mul(x1y1,sZ))
        lemma_field_mul_comm(field_mul(x1y1, sZ), sZ);
        // So mul(sZ, sT) = mul(sZ, mul(x1y1, sZ))
        // Cancel sZ: sT = mul(x1y1, sZ) (mod p)
        // This follows from: if mul(a, x) = mul(a, y) and a != 0 (mod p), then x = y (mod p)
        // But we need to be more careful. sT < p, so sT % p = sT.
        // mul(sZ, sT) = mul(sZ, mul(x1y1, sZ))
        // Since sZ % p != 0 and we're in a field, sT = mul(x1y1, sZ) (mod p)
        lemma_field_mul_left_cancel(sZ, sT, field_mul(x1y1, sZ));
        lemma_field_element_reduced(sT);
    };

    // Similarly for T2
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

    // Now: sT * T2 = mul(x1y1, sZ) * mul(x2y2, Z2) = mul(x1y1*x2y2, sZ*Z2) = mul(x1y1*x2y2, z1z2)
    // (using four_factor_rearrange)
    assert(field_mul(sT, T2) == field_mul(field_mul(x1y1, x2y2), z1z2)) by {
        // sT % p = mul(x1y1, sZ), T2 % p = mul(x2y2, Z2)
        // mul(sT, T2) = mul(sT % p, T2 % p) = mul(mul(x1y1,sZ), mul(x2y2,Z2))
        lemma_field_element_reduced(sT);
        lemma_field_element_reduced(T2);
        // Handle mod: mul(a, b) = mul(a%p, b%p) since mul is mod p
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

    // tt2d_val = mul(sT, mul(mul(2,d), T2)) = mul(mul(2,d), mul(sT, T2))
    //          = mul(mul(2,d), mul(x1y1*x2y2, z1z2))
    //          = mul(z1z2, mul(mul(2,d), x1y1*x2y2))
    //          = mul(z1z2, mul(2, mul(d, x1y1*x2y2)))
    let t = field_mul(d, field_mul(x1x2, y1y2));

    assert(field_mul(x1y1, x2y2) == field_mul(x1x2, y1y2)) by {
        lemma_four_factor_rearrange(x1, y1, x2, y2);
    };

    // tt2d_val = mul(z1z2, mul(2, t))
    // Break the proof into smaller steps:

    // Step 3a: tt2d_val = mul(mul(sT, T2), mul(2, d))
    assert(tt2d_val == field_mul(field_mul(sT, T2), field_mul(2, d))) by {
        lemma_field_mul_comm(field_mul(2, d), T2);
        lemma_field_mul_assoc(sT, T2, field_mul(2, d));
    };

    // Step 3b: mul(x1x2y1y2, z1z2) * mul(2, d) = mul(z1z2, mul(x1x2y1y2, mul(2, d)))
    let x1x2y1y2 = field_mul(x1x2, y1y2);
    assert(field_mul(field_mul(x1x2y1y2, z1z2), field_mul(2, d)) == field_mul(
        z1z2,
        field_mul(x1x2y1y2, field_mul(2, d)),
    )) by {
        lemma_field_mul_comm(x1x2y1y2, z1z2);
        lemma_field_mul_assoc(z1z2, x1x2y1y2, field_mul(2, d));
    };

    // Step 3c: mul(x1x2y1y2, mul(2, d)) = mul(2, mul(d, x1x2y1y2)) = mul(2, t)
    assert(field_mul(x1x2y1y2, field_mul(2, d)) == field_mul(2, t)) by {
        lemma_field_mul_comm(x1x2y1y2, field_mul(2, d));
        lemma_field_mul_assoc(2, d, x1x2y1y2);
    };

    // Chain: tt2d_val = mul(mul(sT,T2), mul(2,d))
    //                 = mul(mul(x1x2y1y2, z1z2), mul(2,d))  [since mul(sT,T2) = mul(x1x2y1y2,z1z2)]
    //                 = mul(z1z2, mul(x1x2y1y2, mul(2,d)))
    //                 = mul(z1z2, mul(2, t))
    assert(tt2d_val == field_mul(z1z2, field_mul(2, t)));

    // === STEP 4: Denominator factoring ===
    // add(zz_val, zz_val) = mul(2, z1z2) [add self = double]
    lemma_add_self_eq_double(zz_val);
    let zz2 = field_add(zz_val, zz_val);
    assert(zz2 == field_mul(2, z1z2));

    // result_z = zz2 + tt2d_val = mul(2, z1z2) + mul(z1z2, mul(2, t))
    //          = mul(z1z2, 2) + mul(z1z2, mul(2, t))
    //          = mul(z1z2, 2 + mul(2, t))
    //          = mul(z1z2, mul(2, 1 + t))  [factoring out 2]
    //          = mul(z1z2, mul(2, add(1, t)))
    let result_z = field_add(zz2, tt2d_val);
    let result_t = field_sub(zz2, tt2d_val);

    // mul(2, z1z2) = mul(z1z2, 2)
    lemma_field_mul_comm(2nat, z1z2);

    // z1z2*2 + z1z2*mul(2,t) = z1z2*(2 + mul(2,t))
    assert(result_z == field_mul(z1z2, field_add(2, field_mul(2, t)))) by {
        // result_z = add(mul(z1z2, 2), mul(z1z2, mul(2, t)))
        lemma_reverse_distribute_add(2nat, field_mul(2, t), z1z2);
        lemma_field_mul_comm(field_add(2, field_mul(2, t)), z1z2);
    };

    // 2 + mul(2, t) = mul(2, 1) + mul(2, t) = mul(2, 1 + t) = mul(2, add(1, t))
    assert(field_add(2nat, field_mul(2, t)) == field_mul(2, field_add(1, t))) by {
        // mul(2, add(1, t)) = add(mul(2, 1), mul(2, t))
        lemma_field_mul_distributes_over_add(2, 1, t);
        // mul(2, 1) = 2 % p = 2
        lemma_field_mul_one_right(2nat);
        lemma_small_mod(2nat, p());
    };
    assert(result_z == field_mul(z1z2, field_mul(2, field_add(1, t))));

    // Similarly: result_t = zz2 - tt2d = z1z2*2 - z1z2*mul(2,t) = z1z2*(2 - mul(2,t))
    //                     = z1z2 * mul(2, sub(1, t))
    assert(result_t == field_mul(z1z2, field_sub(2nat, field_mul(2, t)))) by {
        lemma_reverse_distribute_sub(2nat, field_mul(2, t), z1z2);
        lemma_field_mul_comm(field_sub(2nat, field_mul(2, t)), z1z2);
    };

    assert(field_sub(2nat, field_mul(2, t)) == field_mul(2, field_sub(1, t))) by {
        // mul(2, sub(1, t)) = mul(sub(1, t), 2) [comm]
        //                   = sub(mul(1, 2), mul(t, 2)) [distributes_over_sub_right]
        //                   = sub(2, mul(2, t))  [mul(1,2)=2, mul(t,2)=mul(2,t)]
        lemma_field_mul_comm(2nat, field_sub(1, t));
        lemma_field_mul_distributes_over_sub_right(1, t, 2);
        lemma_field_mul_one_left(2nat);
        lemma_small_mod(2nat, p());
        lemma_field_mul_comm(t, 2nat);
    };
    assert(result_t == field_mul(z1z2, field_mul(2, field_sub(1, t))));

    // result_x = mul(2, z1z2*(y1x2+x1y2)) = mul(z1z2, mul(2, y1x2+x1y2))
    assert(result_x == field_mul(z1z2, field_mul(2, num_x))) by {
        // result_x = mul(2, mul(z1z2, num_x))
        // = mul(mul(2, z1z2), num_x) [assoc]
        // = mul(mul(z1z2, 2), num_x) [comm]
        // = mul(z1z2, mul(2, num_x)) [assoc]
        lemma_field_mul_assoc(2, z1z2, num_x);
        lemma_field_mul_comm(2nat, z1z2);
        lemma_field_mul_assoc(z1z2, 2, num_x);
    };

    assert(result_y == field_mul(z1z2, field_mul(2, num_y))) by {
        lemma_field_mul_assoc(2, z1z2, num_y);
        lemma_field_mul_comm(2nat, z1z2);
        lemma_field_mul_assoc(z1z2, 2, num_y);
    };

    // === STEP 5: Factor cancellation to get affine ratios ===
    // Define the affine-level 2x values (what lemma_completed_point_ratios expects)
    let aff_rx = field_mul(2, field_add(x1y2, y1x2));
    let aff_ry = field_mul(2, field_add(y1y2, x1x2));
    let aff_rz = field_mul(2, field_add(1, t));
    let aff_rt = field_mul(2, field_sub(1, t));

    // num_x = y1x2 + x1y2 = x1y2 + y1x2 [by add commutativity]
    assert(num_x == field_add(x1y2, y1x2)) by {
        let pp = p();
        lemma_add_mod_noop(y1x2 as int, x1y2 as int, pp as int);
        lemma_add_mod_noop(x1y2 as int, y1x2 as int, pp as int);
    };

    // So aff_rx = mul(2, num_x) and result_x = mul(z1z2, aff_rx)
    assert(result_x == field_mul(z1z2, aff_rx));
    assert(result_y == field_mul(z1z2, aff_ry));
    assert(result_z == field_mul(z1z2, aff_rz));
    assert(result_t == field_mul(z1z2, aff_rt));

    // Apply lemma_completed_point_ratios to get the affine-level ratios
    // Need: the t used in aff_rz matches edwards_add's t
    // In edwards_add: t = mul(d, mul(mul(x1,x2), mul(y1,y2))) ✓ (same as our t)
    lemma_completed_point_ratios(x1, y1, x2, y2, aff_rx, aff_ry, aff_rz, aff_rt);

    // From lemma_completed_point_ratios:
    // aff_rz != 0, aff_rt != 0
    // mul(aff_rx, inv(aff_rz)) == edwards_add(x1, y1, x2, y2).0
    // mul(aff_ry, inv(aff_rt)) == edwards_add(x1, y1, x2, y2).1
    // math_on_edwards_curve(...)

    // z1z2 != 0 (product of non-zero field elements)
    lemma_field_element_reduced(sZ);
    lemma_field_element_reduced(Z2);
    lemma_nonzero_product(sZ, Z2);
    // z1z2 % p() != 0 (since z1z2 < p and z1z2 != 0)
    assert(z1z2 < p()) by {
        lemma_mod_bound((sZ * Z2) as int, p() as int);
    };
    lemma_field_element_reduced(z1z2);
    assert(z1z2 % p() != 0);

    // Cancel z1z2: result_x/result_z = aff_rx/aff_rz (= edwards_add.0)
    // result_x = mul(z1z2, aff_rx), result_z = mul(z1z2, aff_rz)
    // So mul(result_x, inv(result_z)) = mul(aff_rx, inv(aff_rz))
    assert(aff_rz % p() != 0) by {
        lemma_field_element_reduced(aff_rz);
    };
    lemma_cancel_common_factor(aff_rx, aff_rz, z1z2);
    // mul(mul(aff_rx, z1z2), inv(mul(aff_rz, z1z2))) == mul(aff_rx, inv(aff_rz))
    // We need: mul(z1z2, aff_rx) = mul(aff_rx, z1z2)
    lemma_field_mul_comm(z1z2, aff_rx);
    lemma_field_mul_comm(z1z2, aff_rz);

    assert(aff_rt % p() != 0) by {
        lemma_field_element_reduced(aff_rt);
    };
    lemma_cancel_common_factor(aff_ry, aff_rt, z1z2);
    lemma_field_mul_comm(z1z2, aff_ry);
    lemma_field_mul_comm(z1z2, aff_rt);

    // result_z != 0, result_t != 0
    lemma_nonzero_product(aff_rz, z1z2);
    lemma_nonzero_product(aff_rt, z1z2);

    // === STEP 6: Connect to spec_edwards_add_projective_niels ===
    // spec_edwards_add_projective_niels(self_point, other)
    //   = edwards_add(self_affine.0, self_affine.1, other_affine.0, other_affine.1)
    //   = edwards_add(x1, y1, niels_aff.0, niels_aff.1)
    // By lemma_projective_niels_affine_equals_edwards_affine: niels_aff == ep_affine = (x2, y2)
    lemma_projective_niels_affine_equals_edwards_affine(other, ep);
    // So spec_edwards_add_projective_niels(self_point, other) = edwards_add(x1, y1, x2, y2)

    // completed_point_as_affine_edwards(result) = (result_x/result_z, result_y/result_t)
    //   = (edwards_add(x1,y1,x2,y2).0, edwards_add(x1,y1,x2,y2).1)
    //   = edwards_add(x1,y1,x2,y2)
    //   = spec_edwards_add_projective_niels(self_point, other)
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
    // === SETUP: Extract projective coordinates (same as add proof) ===
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

    // === Extract witness from is_valid_projective_niels_point ===
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

    // Segre relations
    assert(field_mul(sX, sY) == field_mul(sZ, sT));
    assert(field_mul(X2, Y2) == field_mul(Z2, T2));

    // === From correspondence: relate Niels fields to (X2, Y2, Z2, T2) ===
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

    // === Affine coordinates ===
    let x1 = field_mul(sX, field_inv(sZ));
    let y1 = field_mul(sY, field_inv(sZ));
    let x2 = field_mul(X2, field_inv(Z2));
    let y2 = field_mul(Y2, field_inv(Z2));

    axiom_valid_extended_point_affine_on_curve(sX, sY, sZ, sT);
    axiom_valid_extended_point_affine_on_curve(X2, Y2, Z2, T2);

    // === STEP 1: Mixed FOIL on PM and MP ===
    // pm_val = mul(add(sY,sX), sub(Y2,X2)) and mp_val = mul(sub(sY,sX), add(Y2,X2))
    // By mixed FOIL: PM - MP = 2*(sX*Y2 - sY*X2) and PM + MP = 2*(sY*Y2 - sX*X2)
    lemma_pm_minus_mp(sY, sX, Y2, X2);
    lemma_pm_plus_mp(sY, sX, Y2, X2);

    let result_x = field_sub(pm_val, mp_val);
    let result_y = field_add(pm_val, mp_val);

    // result_x = 2*(sX*Y2 - sY*X2)
    assert(result_x == field_mul(2, field_sub(field_mul(sX, Y2), field_mul(sY, X2))));
    // result_y = 2*(sY*Y2 - sX*X2)
    assert(result_y == field_mul(2, field_sub(field_mul(sY, Y2), field_mul(sX, X2))));

    // === STEP 2: Factor Z1*Z2 from projective products (same as add) ===
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

    // Numerator factoring with subtraction:
    let y1x2 = field_mul(y1, x2);
    let x1y2 = field_mul(x1, y2);
    let y1y2 = field_mul(y1, y2);
    let x1x2 = field_mul(x1, x2);

    // sX*Y2 - sY*X2 = x1y2*z1z2 - y1x2*z1z2 = (x1y2-y1x2)*z1z2 = z1z2*(x1y2-y1x2)
    assert(field_sub(field_mul(sX, Y2), field_mul(sY, X2)) == field_mul(
        z1z2,
        field_sub(x1y2, y1x2),
    )) by {
        lemma_reverse_distribute_sub(x1y2, y1x2, z1z2);
        lemma_field_mul_comm(field_sub(x1y2, y1x2), z1z2);
    };

    // sY*Y2 - sX*X2 = y1y2*z1z2 - x1x2*z1z2 = z1z2*(y1y2-x1x2)
    assert(field_sub(field_mul(sY, Y2), field_mul(sX, X2)) == field_mul(
        z1z2,
        field_sub(y1y2, x1x2),
    )) by {
        lemma_reverse_distribute_sub(y1y2, x1x2, z1z2);
        lemma_field_mul_comm(field_sub(y1y2, x1x2), z1z2);
    };

    let num_x = field_sub(x1y2, y1x2);
    let num_y = field_sub(y1y2, x1x2);

    // === STEP 3: TT2d expansion using Segre (same as add) ===
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

    // tt2d_val = mul(z1z2, mul(2, t)) — same chain as add proof
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

    // === STEP 4: Denominator factoring (Z/T swapped from add) ===
    lemma_add_self_eq_double(zz_val);
    let zz2 = field_add(zz_val, zz_val);
    assert(zz2 == field_mul(2, z1z2));

    let result_z = field_sub(zz2, tt2d_val);
    let result_t = field_add(zz2, tt2d_val);

    lemma_field_mul_comm(2nat, z1z2);

    // result_z = z1z2*2 - z1z2*mul(2,t) = z1z2*(2 - mul(2,t)) = z1z2*mul(2, sub(1,t))
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

    // result_t = z1z2*2 + z1z2*mul(2,t) = z1z2*(2 + mul(2,t)) = z1z2*mul(2, add(1,t))
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

    // result_x = mul(2, z1z2*num_x) = mul(z1z2, mul(2, num_x))
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

    // === STEP 5: Connect to edwards_sub via neg(x2) ===
    // edwards_sub(x1,y1,x2,y2) = edwards_add(x1,y1,neg(x2),y2)
    // We apply lemma_completed_point_ratios(x1, y1, neg(x2), y2, ...)
    let neg_x2 = field_neg(x2);

    // neg(x2) preserves on-curve
    lemma_neg_preserves_curve(x2, y2);

    // Need to show: sub(x1y2, y1x2) = add(x1*y2, y1*neg(x2))
    // mul(y1, neg(x2)) = neg(mul(y1, x2)) = neg(y1x2)
    lemma_field_mul_neg(y1, x2);
    // add(x1y2, neg(y1x2)) = sub(x1y2, y1x2) = num_x
    lemma_field_sub_eq_add_neg(x1y2, y1x2);

    // Need to show: sub(y1y2, x1x2) = add(y1*y2, x1*neg(x2))
    lemma_field_mul_neg(x1, x2);
    lemma_field_sub_eq_add_neg(y1y2, x1x2);

    // Connect t to neg(x2): t' = mul(d, mul(mul(x1,neg(x2)), mul(y1,y2)))
    // mul(x1, neg(x2)) = neg(mul(x1, x2)) = neg(x1x2)
    // mul(neg(x1x2), y1y2): need neg on first arg
    // = mul(y1y2, neg(x1x2)) [comm] = neg(mul(y1y2, x1x2)) [field_mul_neg]
    // = neg(mul(x1x2, y1y2)) [comm]
    lemma_field_mul_comm(field_neg(x1x2), y1y2);
    lemma_field_mul_neg(y1y2, x1x2);
    lemma_field_mul_comm(y1y2, x1x2);
    // So mul(mul(x1,neg(x2)), mul(y1,y2)) = neg(mul(x1x2, y1y2))

    // mul(d, neg(mul(x1x2, y1y2))) = neg(mul(d, mul(x1x2, y1y2))) = neg(t)
    lemma_field_mul_neg(d, field_mul(x1x2, y1y2));

    let t_prime = field_mul(d, field_mul(field_mul(x1, neg_x2), field_mul(y1, y2)));

    // t' = neg(t)
    assert(t_prime == field_neg(t));

    // sub(1, t) = add(1, neg(t)) = add(1, t')
    lemma_field_sub_eq_add_neg(1nat, t);

    // add(1, t) = sub(1, neg(t)) = sub(1, t')
    // sub(1, t') = add(1, neg(t')) = add(1, neg(neg(t))) = add(1, t%p) = add(1, t)
    lemma_field_sub_eq_add_neg(1nat, t_prime);
    lemma_neg_neg(t);
    assert(field_sub(1nat, t_prime) == field_add(1nat, t)) by {
        let p = p();
        lemma_add_mod_noop(1nat as int, (t % p) as int, p as int);
        lemma_add_mod_noop(1nat as int, t as int, p as int);
        lemma_mod_twice(t as int, p as int);
    };

    // Define affine-level values for lemma_completed_point_ratios with neg(x2)
    let aff_rx = field_mul(2, field_add(field_mul(x1, y2), field_mul(y1, neg_x2)));
    let aff_ry = field_mul(2, field_add(field_mul(y1, y2), field_mul(x1, neg_x2)));
    let aff_rz = field_mul(2, field_add(1, t_prime));
    let aff_rt = field_mul(2, field_sub(1, t_prime));

    // Show our result components = z1z2 * aff_r*
    // num_x = sub(x1y2, y1x2) = add(x1y2, mul(y1,neg_x2)) → matches aff_rx/2
    assert(aff_rx == field_mul(2, num_x));
    assert(aff_ry == field_mul(2, num_y));
    // aff_rz = mul(2, add(1, t')) = mul(2, sub(1, t)) [since t' = neg(t)]
    assert(aff_rz == field_mul(2, field_sub(1, t)));
    // aff_rt = mul(2, sub(1, t')) = mul(2, add(1, t))
    assert(aff_rt == field_mul(2, field_add(1, t)));

    assert(result_x == field_mul(z1z2, aff_rx));
    assert(result_y == field_mul(z1z2, aff_ry));
    assert(result_z == field_mul(z1z2, aff_rz));
    assert(result_t == field_mul(z1z2, aff_rt));

    // Apply lemma_completed_point_ratios(x1, y1, neg(x2), y2, ...)
    lemma_completed_point_ratios(x1, y1, neg_x2, y2, aff_rx, aff_ry, aff_rz, aff_rt);

    // === STEP 6: Factor cancellation (same as add) ===
    lemma_field_element_reduced(sZ);
    lemma_field_element_reduced(Z2);
    lemma_nonzero_product(sZ, Z2);
    assert(z1z2 < p()) by {
        lemma_mod_bound((sZ * Z2) as int, p() as int);
    };
    lemma_field_element_reduced(z1z2);
    assert(z1z2 % p() != 0);

    assert(aff_rz % p() != 0) by {
        lemma_field_element_reduced(aff_rz);
    };
    lemma_cancel_common_factor(aff_rx, aff_rz, z1z2);
    lemma_field_mul_comm(z1z2, aff_rx);
    lemma_field_mul_comm(z1z2, aff_rz);

    assert(aff_rt % p() != 0) by {
        lemma_field_element_reduced(aff_rt);
    };
    lemma_cancel_common_factor(aff_ry, aff_rt, z1z2);
    lemma_field_mul_comm(z1z2, aff_ry);
    lemma_field_mul_comm(z1z2, aff_rt);

    lemma_nonzero_product(aff_rz, z1z2);
    lemma_nonzero_product(aff_rt, z1z2);

    // === STEP 7: Connect to spec_edwards_sub_projective_niels ===
    // lemma_completed_point_ratios gives:
    //   aff_rx/aff_rz = edwards_add(x1, y1, neg(x2), y2).0 = edwards_sub(x1, y1, x2, y2).0
    //   aff_ry/aff_rt = edwards_add(x1, y1, neg(x2), y2).1 = edwards_sub(x1, y1, x2, y2).1
    // (edwards_sub is defined as edwards_add with neg(x2))

    // Connect Niels affine to (x2, y2) via the equivalence lemma
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
    // === SETUP: Extract projective coordinates of self ===
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

    // === Extract witness from is_valid_affine_niels_point ===
    let ep = choose|ep: crate::edwards::EdwardsPoint|
        is_valid_edwards_point(ep) && #[trigger] affine_niels_corresponds_to_edwards(other, ep);
    let X2 = fe51_as_canonical_nat(&ep.X);
    let Y2 = fe51_as_canonical_nat(&ep.Y);
    let Z2 = fe51_as_canonical_nat(&ep.Z);

    let z2_inv = field_inv(Z2);
    let x2 = field_mul(X2, z2_inv);
    let y2 = field_mul(Y2, z2_inv);

    // === Affine coordinates of self ===
    let x1 = field_mul(sX, field_inv(sZ));
    let y1 = field_mul(sY, field_inv(sZ));

    axiom_valid_extended_point_affine_on_curve(sX, sY, sZ, sT);
    axiom_valid_extended_point_affine_on_curve(X2, Y2, Z2, fe51_as_canonical_nat(&ep.T));

    // === From correspondence: Niels fields = affine coords ===
    assert(fe51_as_canonical_nat(&other.y_plus_x) == field_add(y2, x2)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.y_minus_x) == field_sub(y2, x2)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.xy2d) == field_mul(field_mul(field_mul(x2, y2), 2), d)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };

    // === STEP 1: FOIL on PP and MM (affine coords for other) ===
    // pp_val = (sY+sX)(y2+x2), mm_val = (sY-sX)(y2-x2)
    lemma_pp_minus_mm(sY, sX, y2, x2);
    lemma_pp_plus_mm(sY, sX, y2, x2);

    let result_x = field_sub(pp_val, mm_val);
    let result_y = field_add(pp_val, mm_val);

    // result_x = 2*(sY*x2 + sX*y2)
    assert(result_x == field_mul(2, field_add(field_mul(sY, x2), field_mul(sX, y2))));
    // result_y = 2*(sY*y2 + sX*x2)
    assert(result_y == field_mul(2, field_add(field_mul(sY, y2), field_mul(sX, x2))));

    // === STEP 2: Factor sZ from projective*affine products ===
    // sY*x2 = (y1*sZ)*x2 = y1*x2*sZ = mul(mul(y1,x2), sZ)
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

    // Numerator factoring:
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

    // result_x = mul(2, mul(sZ, num_x)) = mul(sZ, mul(2, num_x))
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

    // === STEP 3: Txy2d expansion using Segre ===
    // sT = mul(x1y1, sZ) (from Segre: sZ*sT = sX*sY = x1y1*sZ^2)
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

    // xy2d = mul(mul(mul(x2,y2), 2), d) = mul(mul(2,d), x2y2) [with rearrangement]
    // Txy2d = sT * xy2d = mul(x1y1, sZ) * mul(mul(x2y2, 2), d)
    //       = mul(x1y1 * mul(x2y2,2) * d, sZ)  hmm...
    // Let's work step by step:
    // sT = mul(x1y1, sZ) (mod p)
    // Txy2d = mul(sT, xy2d)
    // xy2d = mul(mul(x2y2, 2), d) = mul(x2y2*2, d)
    //      Rearranging: = mul(d, mul(2, x2y2)) [comm/assoc]

    // We need: Txy2d = mul(sZ, mul(2, t)) where t = mul(d, mul(x1x2, y1y2))
    // Txy2d = sT * mul(mul(x2y2, 2), d)
    //       = mul(x1y1, sZ) * mul(mul(x2y2, 2), d) [mod p for sT]
    let xy2d_spec = field_mul(field_mul(x2y2, 2), d);

    // sT * xy2d = mul(x1y1, sZ) * xy2d (after mod absorption)
    assert(field_mul(sT, xy2d_spec) == field_mul(field_mul(x1y1, sZ), xy2d_spec)) by {
        lemma_field_element_reduced(sT);
        lemma_mul_mod_noop_left(sT as int, xy2d_spec as int, p() as int);
        lemma_mul_mod_noop_left((field_mul(x1y1, sZ)) as int, xy2d_spec as int, p() as int);
    };

    // mul(x1y1, sZ) * mul(mul(x2y2, 2), d)
    // = mul(x1y1 * mul(x2y2, 2), sZ * d) [four_factor_rearrange]
    // Hmm, we want to isolate sZ. Let me try:
    // = mul(mul(x1y1, sZ), mul(mul(x2y2, 2), d))
    // Rearrange xy2d: mul(mul(x2y2, 2), d) = mul(x2y2, mul(2, d)) by assoc
    assert(xy2d_spec == field_mul(x2y2, field_mul(2, d))) by {
        lemma_field_mul_assoc(x2y2, 2, d);
    };

    // mul(mul(x1y1, sZ), mul(x2y2, mul(2,d)))
    // = mul(mul(x1y1, x2y2), mul(sZ, mul(2,d))) [four_factor_rearrange]
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

    // mul(x1x2y1y2, mul(sZ, mul(2,d))) = mul(sZ, mul(x1x2y1y2, mul(2,d)))
    assert(field_mul(x1x2y1y2, field_mul(sZ, field_mul(2, d))) == field_mul(
        sZ,
        field_mul(x1x2y1y2, field_mul(2, d)),
    )) by {
        // x*(s*(2d)) = (x*s)*(2d) [assoc] = (s*x)*(2d) [comm] = s*(x*(2d)) [assoc]
        lemma_field_mul_assoc(x1x2y1y2, sZ, field_mul(2, d));
        lemma_field_mul_comm(x1x2y1y2, sZ);
        lemma_field_mul_assoc(sZ, x1x2y1y2, field_mul(2, d));
    };

    // mul(x1x2y1y2, mul(2,d)) = mul(2, mul(d, x1x2y1y2)) = mul(2, t)
    assert(field_mul(x1x2y1y2, field_mul(2, d)) == field_mul(2, t)) by {
        lemma_field_mul_comm(x1x2y1y2, field_mul(2, d));
        lemma_field_mul_assoc(2, d, x1x2y1y2);
    };

    // Chain: Txy2d = sT * xy2d = mul(x1y1,sZ)*xy2d = mul(x1x2y1y2, mul(sZ, mul(2,d)))
    //      = mul(sZ, mul(x1x2y1y2, mul(2,d))) = mul(sZ, mul(2, t))
    assert(txy2d_val == field_mul(sZ, field_mul(2, t)));

    // === STEP 4: Denominator factoring ===
    // z2_val = add(sZ, sZ) = mul(2, sZ)
    lemma_add_self_eq_double(sZ);
    assert(z2_val == field_mul(2, sZ));

    let result_z = field_add(z2_val, txy2d_val);
    let result_t = field_sub(z2_val, txy2d_val);

    lemma_field_mul_comm(2nat, sZ);

    // result_z = sZ*2 + sZ*mul(2,t) = sZ*(2 + mul(2,t)) = sZ*mul(2, add(1,t))
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

    // result_t = sZ*2 - sZ*mul(2,t) = sZ*(2 - mul(2,t)) = sZ*mul(2, sub(1,t))
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

    // === STEP 5: Factor cancellation ===
    let aff_rx = field_mul(2, field_add(x1y2, y1x2));
    let aff_ry = field_mul(2, field_add(y1y2, x1x2));
    let aff_rz = field_mul(2, field_add(1, t));
    let aff_rt = field_mul(2, field_sub(1, t));

    // num_x = y1x2 + x1y2 = x1y2 + y1x2 (commutative)
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

    // sZ != 0, sZ % p != 0 — already established
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

    lemma_nonzero_product(aff_rz, sZ);
    lemma_nonzero_product(aff_rt, sZ);

    // === STEP 6: Connect to spec_edwards_add_affine_niels ===
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
    // === SETUP: Same as add AffineNiels ===
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

    axiom_valid_extended_point_affine_on_curve(sX, sY, sZ, sT);
    axiom_valid_extended_point_affine_on_curve(X2, Y2, Z2, fe51_as_canonical_nat(&ep.T));

    assert(fe51_as_canonical_nat(&other.y_plus_x) == field_add(y2, x2)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.y_minus_x) == field_sub(y2, x2)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.xy2d) == field_mul(field_mul(field_mul(x2, y2), 2), d)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };

    // === STEP 1: Mixed FOIL ===
    // pm_val = (sY+sX)(y2-x2), mp_val = (sY-sX)(y2+x2)
    lemma_pm_minus_mp(sY, sX, y2, x2);
    lemma_pm_plus_mp(sY, sX, y2, x2);

    let result_x = field_sub(pm_val, mp_val);
    let result_y = field_add(pm_val, mp_val);

    assert(result_x == field_mul(2, field_sub(field_mul(sX, y2), field_mul(sY, x2))));
    assert(result_y == field_mul(2, field_sub(field_mul(sY, y2), field_mul(sX, x2))));

    // === STEP 2: Factor sZ ===
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

    // sX*y2 - sY*x2 = x1y2*sZ - y1x2*sZ = sZ*(x1y2 - y1x2)
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

    // === STEP 3: Txy2d expansion (same as add AffineNiels) ===
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
        // x*(s*(2d)) = (x*s)*(2d) [assoc] = (s*x)*(2d) [comm] = s*(x*(2d)) [assoc]
        lemma_field_mul_assoc(x1x2y1y2, sZ, field_mul(2, d));
        lemma_field_mul_comm(x1x2y1y2, sZ);
        lemma_field_mul_assoc(sZ, x1x2y1y2, field_mul(2, d));
    };

    assert(field_mul(x1x2y1y2, field_mul(2, d)) == field_mul(2, t)) by {
        lemma_field_mul_comm(x1x2y1y2, field_mul(2, d));
        lemma_field_mul_assoc(2, d, x1x2y1y2);
    };

    assert(txy2d_val == field_mul(sZ, field_mul(2, t)));

    // === STEP 4: Denominator factoring (Z/T swapped from add) ===
    lemma_add_self_eq_double(sZ);
    assert(z2_val == field_mul(2, sZ));

    let result_z = field_sub(z2_val, txy2d_val);
    let result_t = field_add(z2_val, txy2d_val);

    lemma_field_mul_comm(2nat, sZ);

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

    // === STEP 5: Connect to edwards_sub via neg(x2) ===
    let neg_x2 = field_neg(x2);
    lemma_neg_preserves_curve(x2, y2);

    lemma_field_mul_neg(y1, x2);
    lemma_field_sub_eq_add_neg(x1y2, y1x2);

    lemma_field_mul_neg(x1, x2);
    lemma_field_sub_eq_add_neg(y1y2, x1x2);

    lemma_field_mul_comm(field_neg(x1x2), y1y2);
    lemma_field_mul_neg(y1y2, x1x2);
    lemma_field_mul_comm(y1y2, x1x2);
    lemma_field_mul_neg(d, field_mul(x1x2, y1y2));

    let t_prime = field_mul(d, field_mul(field_mul(x1, neg_x2), field_mul(y1, y2)));
    assert(t_prime == field_neg(t));

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

    // === STEP 6: Factor cancellation ===
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

    lemma_nonzero_product(aff_rz, sZ);
    lemma_nonzero_product(aff_rt, sZ);

    // === STEP 7: Connect to spec ===
    lemma_affine_niels_affine_equals_edwards_affine(other, ep);
}

} // verus!
