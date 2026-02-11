//! Lemmas for Edwards point addition producing CompletedPoint results.
//!
//! These lemmas prove that the extended addition formulas used in
//! `EdwardsPoint + ProjectiveNielsPoint` and `EdwardsPoint + AffineNielsPoint`
//! correctly compute the Edwards addition in P¹ × P¹ representation.

#[allow(unused_imports)]
use crate::backend::serial::u64::constants::EDWARDS_D;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::add_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
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
// FOIL expansion lemmas
// =============================================================================

/// FOIL: (a+b)(c+d) = (ac + ad) + (bc + bd)
pub proof fn lemma_foil_add(a: nat, b: nat, c: nat, d: nat)
    ensures
        math_field_mul(math_field_add(a, b), math_field_add(c, d))
            == math_field_add(
                math_field_add(math_field_mul(a, c), math_field_mul(a, d)),
                math_field_add(math_field_mul(b, c), math_field_mul(b, d)),
            ),
{
    let ab = math_field_add(a, b);
    let cd = math_field_add(c, d);

    // (a+b)(c+d) = (a+b)*c + (a+b)*d  by commutativity then distribution
    assert(math_field_mul(ab, cd) == math_field_add(
        math_field_mul(ab, c),
        math_field_mul(ab, d),
    )) by {
        lemma_field_mul_comm(ab, cd);
        lemma_field_mul_distributes_over_add(cd, a, b);
        // cd * (a+b) = cd*a + cd*b, but we need (a+b)*c + (a+b)*d
        // Use comm: (a+b)*(c+d) = (c+d)*(a+b) = (c+d)*a + (c+d)*b
        // Then comm each: (c+d)*a = a*(c+d), etc. Not quite right.
        // Let's use: ab * cd = ab*c + ab*d directly
        lemma_field_mul_distributes_over_add(ab, c, d);
    }

    // (a+b)*c = a*c + b*c  by comm then distrib
    assert(math_field_mul(ab, c) == math_field_add(
        math_field_mul(a, c),
        math_field_mul(b, c),
    )) by {
        lemma_field_mul_comm(ab, c);
        lemma_field_mul_distributes_over_add(c, a, b);
        lemma_field_mul_comm(c, a);
        lemma_field_mul_comm(c, b);
    }

    // (a+b)*d = a*d + b*d  by comm then distrib
    assert(math_field_mul(ab, d) == math_field_add(
        math_field_mul(a, d),
        math_field_mul(b, d),
    )) by {
        lemma_field_mul_comm(ab, d);
        lemma_field_mul_distributes_over_add(d, a, b);
        lemma_field_mul_comm(d, a);
        lemma_field_mul_comm(d, b);
    }

    // Now: (a+b)(c+d) = (ac + bc) + (ad + bd)
    // We need: (ac + ad) + (bc + bd)
    // These are equal by associativity and commutativity of field addition
    // (ac + bc) + (ad + bd) = ac + (bc + ad) + bd = ac + (ad + bc) + bd = (ac + ad) + (bc + bd)
    let ac = math_field_mul(a, c);
    let ad = math_field_mul(a, d);
    let bc = math_field_mul(b, c);
    let bd = math_field_mul(b, d);

    // We have: result = (ac + bc) + (ad + bd)
    // We want: result = (ac + ad) + (bc + bd)
    // Both equal ac + ad + bc + bd in the field; prove via modular arithmetic
    assert(math_field_add(math_field_add(ac, bc), math_field_add(ad, bd))
        == math_field_add(math_field_add(ac, ad), math_field_add(bc, bd))) by {
        let p = p();
        p_gt_2();
        lemma_add_mod_noop((ac + bc) as int, (ad + bd) as int, p as int);
        lemma_add_mod_noop(ac as int, bc as int, p as int);
        lemma_add_mod_noop(ad as int, bd as int, p as int);
        lemma_add_mod_noop((ac + ad) as int, (bc + bd) as int, p as int);
        lemma_add_mod_noop(ac as int, ad as int, p as int);
        lemma_add_mod_noop(bc as int, bd as int, p as int);
        // Both reduce to (ac + bc + ad + bd) % p = (ac + ad + bc + bd) % p
        // which holds since integer addition is commutative
        assert((ac + bc + ad + bd) == (ac + ad + bc + bd));
    }
}

/// FOIL for subtraction: (a-b)(c-d) = (ac + bd) - (ad + bc)
/// More precisely: (a-b)(c-d) = ac - ad - bc + bd = (ac+bd) - (ad+bc)
pub proof fn lemma_foil_sub(a: nat, b: nat, c: nat, d: nat)
    ensures
        math_field_mul(math_field_sub(a, b), math_field_sub(c, d))
            == math_field_sub(
                math_field_add(math_field_mul(a, c), math_field_mul(b, d)),
                math_field_add(math_field_mul(a, d), math_field_mul(b, c)),
            ),
{
    let a_minus_b = math_field_sub(a, b);
    let c_minus_d = math_field_sub(c, d);
    let ac = math_field_mul(a, c);
    let ad = math_field_mul(a, d);
    let bc = math_field_mul(b, c);
    let bd = math_field_mul(b, d);

    // (a-b)(c-d) = (a-b)*c - (a-b)*d
    // Use comm: (a-b)*(c-d) = (c-d)*(a-b), then sub_right(c,d,a_minus_b)
    assert(math_field_mul(a_minus_b, c_minus_d) == math_field_sub(
        math_field_mul(a_minus_b, c),
        math_field_mul(a_minus_b, d),
    )) by {
        lemma_field_mul_comm(a_minus_b, c_minus_d);
        // (c-d)*(a-b) = c*(a-b) - d*(a-b)
        lemma_field_mul_distributes_over_sub_right(c, d, a_minus_b);
        // c*(a-b) = (a-b)*c and d*(a-b) = (a-b)*d
        lemma_field_mul_comm(c, a_minus_b);
        lemma_field_mul_comm(d, a_minus_b);
    }

    // (a-b)*c = a*c - b*c
    assert(math_field_mul(a_minus_b, c) == math_field_sub(ac, bc)) by {
        lemma_field_mul_distributes_over_sub_right(a, b, c);
    }

    // (a-b)*d = a*d - b*d
    assert(math_field_mul(a_minus_b, d) == math_field_sub(ad, bd)) by {
        lemma_field_mul_distributes_over_sub_right(a, b, d);
    }

    // (ac - bc) - (ad - bd) = (ac + bd) - (ad + bc)
    // Both sides ≡ ac - bc - ad + bd (mod p).
    // We prove this by showing both sides equal the same nat value.
    let lhs = math_field_sub(math_field_sub(ac, bc), math_field_sub(ad, bd));
    let rhs = math_field_sub(math_field_add(ac, bd), math_field_add(ad, bc));

    // Show LHS = (ac - bc - ad + bd) mod p (as int then cast to nat)
    assert(lhs as int == ((ac as int - bc as int) - (ad as int - bd as int)) % (p() as int)) by {
        let p = p();
        let p_int = p as int;
        p_gt_2();
        lemma_small_mod(ac, p);
        lemma_small_mod(bc, p);
        lemma_small_mod(ad, p);
        lemma_small_mod(bd, p);
        // math_field_sub(ac, bc) = (ac + p - bc) % p
        // = (ac - bc + p) % p = (ac - bc) % p
        lemma_mod_add_multiples_vanish(ac as int - bc as int, p_int);
        lemma_mod_add_multiples_vanish(ad as int - bd as int, p_int);
        // Now sub the results
        let s1 = math_field_sub(ac, bc);
        let s2 = math_field_sub(ad, bd);
        // s1 = (ac - bc) % p as nat, s2 = (ad - bd) % p as nat
        // math_field_sub(s1, s2) = (s1%p + p - s2%p) % p
        // Since s1 < p and s2 < p, s1%p=s1 and s2%p=s2
        lemma_small_mod(s1, p);
        lemma_small_mod(s2, p);
        // = (s1 + p - s2) % p = (s1 - s2 + p) % p = (s1 - s2) % p
        lemma_mod_add_multiples_vanish(s1 as int - s2 as int, p_int);
        // = ((ac-bc)%p - (ad-bd)%p) % p = (ac-bc-ad+bd) % p
        lemma_sub_mod_noop(ac as int - bc as int, ad as int - bd as int, p_int);
    }

    // Show RHS = (ac + bd - ad - bc) mod p
    assert(rhs as int == ((ac as int + bd as int) - (ad as int + bc as int)) % (p() as int)) by {
        let p = p();
        let p_int = p as int;
        p_gt_2();
        lemma_small_mod(ac, p);
        lemma_small_mod(bc, p);
        lemma_small_mod(ad, p);
        lemma_small_mod(bd, p);
        let a1 = math_field_add(ac, bd);
        let a2 = math_field_add(ad, bc);
        lemma_small_mod(a1, p);
        lemma_small_mod(a2, p);
        lemma_mod_add_multiples_vanish(a1 as int - a2 as int, p_int);
        lemma_add_mod_noop(ac as int, bd as int, p_int);
        lemma_add_mod_noop(ad as int, bc as int, p_int);
        lemma_sub_mod_noop(ac as int + bd as int, ad as int + bc as int, p_int);
    }

    // The integer expressions are equal
    assert((ac as int - bc as int) - (ad as int - bd as int) ==
           (ac as int + bd as int) - (ad as int + bc as int));

    // Therefore LHS == RHS
    assert(lhs == rhs);
}

// =============================================================================
// PP/MM decomposition lemmas
// =============================================================================

/// PP - MM = 2·(y1·x2 + x1·y2) when PP = (y1+x1)(y2+x2) and MM = (y1-x1)(y2-x2)
/// More precisely, using field elements a = y1, b = x1, c = y2, d = x2:
///   (a+b)(c+d) - (a-b)(c-d) = 2·(a·d + b·c)
pub proof fn lemma_pp_minus_mm(a: nat, b: nat, c: nat, d: nat)
    ensures
        math_field_sub(
            math_field_mul(math_field_add(a, b), math_field_add(c, d)),
            math_field_mul(math_field_sub(a, b), math_field_sub(c, d)),
        ) == math_field_mul(2, math_field_add(math_field_mul(a, d), math_field_mul(b, c))),
{
    let ad = math_field_mul(a, d);
    let bc = math_field_mul(b, c);
    let ac = math_field_mul(a, c);
    let bd = math_field_mul(b, d);

    // PP = (a+b)(c+d) = (ac + ad) + (bc + bd)  by FOIL
    lemma_foil_add(a, b, c, d);
    let pp = math_field_mul(math_field_add(a, b), math_field_add(c, d));
    assert(pp == math_field_add(math_field_add(ac, ad), math_field_add(bc, bd)));

    // MM = (a-b)(c-d) = (ac + bd) - (ad + bc)  by FOIL for sub
    lemma_foil_sub(a, b, c, d);
    let mm = math_field_mul(math_field_sub(a, b), math_field_sub(c, d));
    assert(mm == math_field_sub(math_field_add(ac, bd), math_field_add(ad, bc)));

    // PP - MM = [(ac+ad)+(bc+bd)] - [(ac+bd)-(ad+bc)]
    // = (ac+ad+bc+bd) - (ac+bd-ad-bc)
    // = 2·(ad+bc)
    // Use lemma: (A+B) - (A-B) = 2B where A = ac+bd, B = ad+bc
    let big_a = math_field_add(ac, bd);
    let big_b = math_field_add(ad, bc);

    // Show PP = big_a + big_b
    // We already showed PP = (ac+ad) + (bc+bd)
    // big_a + big_b = (ac+bd) + (ad+bc)
    // Need: (ac+ad)+(bc+bd) == (ac+bd)+(ad+bc)  [by commutativity/associativity]
    assert(pp == math_field_add(big_a, big_b)) by {
        let p = p();
        p_gt_2();
        lemma_add_mod_noop((ac + ad) as int, (bc + bd) as int, p as int);
        lemma_add_mod_noop(ac as int, ad as int, p as int);
        lemma_add_mod_noop(bc as int, bd as int, p as int);
        lemma_add_mod_noop((ac + bd) as int, (ad + bc) as int, p as int);
        lemma_add_mod_noop(ac as int, bd as int, p as int);
        lemma_add_mod_noop(ad as int, bc as int, p as int);
        assert((ac + ad + bc + bd) == (ac + bd + ad + bc));
    }

    // Show MM = big_a - big_b (already proven by foil_sub)
    assert(mm == math_field_sub(big_a, big_b));

    // Apply: (A+B) - (A-B) = 2B
    lemma_field_add_sub_recover_double(big_a, big_b);
}

/// PP + MM = 2·(y1·y2 + x1·x2)
pub proof fn lemma_pp_plus_mm(a: nat, b: nat, c: nat, d: nat)
    ensures
        math_field_add(
            math_field_mul(math_field_add(a, b), math_field_add(c, d)),
            math_field_mul(math_field_sub(a, b), math_field_sub(c, d)),
        ) == math_field_mul(2, math_field_add(math_field_mul(a, c), math_field_mul(b, d))),
{
    let ad = math_field_mul(a, d);
    let bc = math_field_mul(b, c);
    let ac = math_field_mul(a, c);
    let bd = math_field_mul(b, d);

    lemma_foil_add(a, b, c, d);
    let pp = math_field_mul(math_field_add(a, b), math_field_add(c, d));
    assert(pp == math_field_add(math_field_add(ac, ad), math_field_add(bc, bd)));

    lemma_foil_sub(a, b, c, d);
    let mm = math_field_mul(math_field_sub(a, b), math_field_sub(c, d));
    assert(mm == math_field_sub(math_field_add(ac, bd), math_field_add(ad, bc)));

    let big_a = math_field_add(ac, bd);
    let big_b = math_field_add(ad, bc);

    assert(pp == math_field_add(big_a, big_b)) by {
        let p = p();
        p_gt_2();
        lemma_add_mod_noop((ac + ad) as int, (bc + bd) as int, p as int);
        lemma_add_mod_noop(ac as int, ad as int, p as int);
        lemma_add_mod_noop(bc as int, bd as int, p as int);
        lemma_add_mod_noop((ac + bd) as int, (ad + bc) as int, p as int);
        lemma_add_mod_noop(ac as int, bd as int, p as int);
        lemma_add_mod_noop(ad as int, bc as int, p as int);
        assert((ac + ad + bc + bd) == (ac + bd + ad + bc));
    }

    assert(mm == math_field_sub(big_a, big_b));

    // Apply: (A+B) + (A-B) = 2A
    lemma_field_add_add_recover_double(big_a, big_b);
}

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
            let d = spec_field_element(&EDWARDS_D);
            let t = math_field_mul(d, math_field_mul(
                math_field_mul(x1, x2), math_field_mul(y1, y2)));
            math_field_add(1, t) != 0 && math_field_sub(1, t) != 0
        }),
        math_on_edwards_curve(
            edwards_add(x1, y1, x2, y2).0,
            edwards_add(x1, y1, x2, y2).1,
        ),
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
        math_on_edwards_curve(math_field_neg(x), y),
{
    let neg_x = math_field_neg(x);
    let pp = p();
    p_gt_2();

    // Step 1: square(neg(x)) == square(x % p) by lemma_neg_square_eq
    lemma_neg_square_eq(x);

    // Step 2: square(x % p) == square(x) by modular arithmetic
    assert(math_field_square(x % p()) == math_field_square(x)) by {
        // (x*x)%p == (x*(x%p))%p
        lemma_mul_mod_noop_right(x as int, x as int, pp as int);
        // ((x%p)*x)%p == ((x%p)*(x%p))%p
        lemma_mul_mod_noop_right((x % pp) as int, x as int, pp as int);
        // x*(x%p) == (x%p)*x by integer commutativity (automatic)
    };

    // Step 3: square(neg(x)) == square(x)
    let neg_x_sq = math_field_square(neg_x);
    let x_sq = math_field_square(x);
    let y_sq = math_field_square(y);
    let d = spec_field_element(&EDWARDS_D);

    // Since neg(x)² = x², all derived curve equation terms are identical
    assert(neg_x_sq == x_sq);
    assert(math_field_mul(neg_x_sq, y_sq) == math_field_mul(x_sq, y_sq));
    assert(math_field_sub(y_sq, neg_x_sq) == math_field_sub(y_sq, x_sq));
    assert(math_field_mul(d, math_field_mul(neg_x_sq, y_sq))
        == math_field_mul(d, math_field_mul(x_sq, y_sq)));
}

/// Given abstract CompletedPoint values that are 2x the edwards_add numerators
/// and denominators, the ratios X/Z and Y/T equal the edwards_add result.
///
/// This bridges the factor-of-2 representation used in the P1xP1 formulas
/// (PP-MM, PP+MM, 2ZZ+TT2d, 2ZZ-TT2d) to the affine edwards_add formula.
/// Proven from axiom_edwards_add_complete (denominator non-zero) and
/// lemma_cancel_common_factor (to cancel the common factor of 2).
pub proof fn lemma_completed_point_ratios(
    x1: nat, y1: nat, x2: nat, y2: nat,
    result_x: nat, result_y: nat, result_z: nat, result_t: nat,
)
    requires
        math_on_edwards_curve(x1, y1),
        math_on_edwards_curve(x2, y2),
        result_x == math_field_mul(2, math_field_add(
            math_field_mul(x1, y2), math_field_mul(y1, x2))),
        result_y == math_field_mul(2, math_field_add(
            math_field_mul(y1, y2), math_field_mul(x1, x2))),
        result_z == math_field_mul(2, math_field_add(1,
            math_field_mul(spec_field_element(&EDWARDS_D),
                math_field_mul(math_field_mul(x1, x2), math_field_mul(y1, y2))))),
        result_t == math_field_mul(2, math_field_sub(1,
            math_field_mul(spec_field_element(&EDWARDS_D),
                math_field_mul(math_field_mul(x1, x2), math_field_mul(y1, y2))))),
    ensures
        result_z != 0,
        result_t != 0,
        math_field_mul(result_x, math_field_inv(result_z))
            == edwards_add(x1, y1, x2, y2).0,
        math_field_mul(result_y, math_field_inv(result_t))
            == edwards_add(x1, y1, x2, y2).1,
        math_on_edwards_curve(
            math_field_mul(result_x, math_field_inv(result_z)),
            math_field_mul(result_y, math_field_inv(result_t)),
        ),
{
    let d = spec_field_element(&EDWARDS_D);
    let x1y2 = math_field_mul(x1, y2);
    let y1x2 = math_field_mul(y1, x2);
    let y1y2 = math_field_mul(y1, y2);
    let x1x2 = math_field_mul(x1, x2);
    let t = math_field_mul(d, math_field_mul(x1x2, y1y2));
    let denom_x = math_field_add(1, t);
    let denom_y = math_field_sub(1, t);
    let num_x = math_field_add(x1y2, y1x2);
    let num_y = math_field_add(y1y2, x1x2);
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
pub proof fn axiom_add_projective_niels_completed_valid(
    self_point: crate::edwards::EdwardsPoint,
    other: crate::backend::serial::curve_models::ProjectiveNielsPoint,
    result: crate::backend::serial::curve_models::CompletedPoint,
    pp_val: nat, mm_val: nat, tt2d_val: nat, zz_val: nat,
)
    requires
        is_well_formed_edwards_point(self_point),
        is_valid_edwards_point(self_point),
        pp_val == math_field_mul(
            math_field_add(spec_field_element(&self_point.Y), spec_field_element(&self_point.X)),
            spec_field_element(&other.Y_plus_X),
        ),
        mm_val == math_field_mul(
            math_field_sub(spec_field_element(&self_point.Y), spec_field_element(&self_point.X)),
            spec_field_element(&other.Y_minus_X),
        ),
        tt2d_val == math_field_mul(spec_field_element(&self_point.T), spec_field_element(&other.T2d)),
        zz_val == math_field_mul(spec_field_element(&self_point.Z), spec_field_element(&other.Z)),
        spec_field_element(&result.X) == math_field_sub(pp_val, mm_val),
        spec_field_element(&result.Y) == math_field_add(pp_val, mm_val),
        spec_field_element(&result.Z) == math_field_add(math_field_add(zz_val, zz_val), tt2d_val),
        spec_field_element(&result.T) == math_field_sub(math_field_add(zz_val, zz_val), tt2d_val),
    ensures
        is_valid_completed_point(result),
        completed_point_as_affine_edwards(result) == spec_edwards_add_projective_niels(
            self_point, other,
        ),
{
    // TODO: Prove from axiom_edwards_add_complete + FOIL + extended coordinate algebra.
    // Proof sketch:
    //   1. Let (x1,y1) = affine(self_point), (x2,y2) = affine(other)
    //   2. By FOIL (lemma_pp_minus_mm/plus_mm): PP-MM = 2·(Y1·X2'+X1·Y2'), etc.
    //   3. By extended invariant T·Z=X·Y and Niels form: factor out Z1·Z2
    //   4. Apply lemma_completed_point_ratios for formula match and Z/T != 0
    admit();
}

/// Exec bridge: EdwardsPoint - ProjectiveNielsPoint -> valid CompletedPoint.
/// Derivable from add variant: subtraction swaps Y_plus_X/Y_minus_X (negating x2)
/// and swaps Z/T (reflecting sign change in 1 +/- d*x1*x2*y1*y2).
pub proof fn axiom_sub_projective_niels_completed_valid(
    self_point: crate::edwards::EdwardsPoint,
    other: crate::backend::serial::curve_models::ProjectiveNielsPoint,
    result: crate::backend::serial::curve_models::CompletedPoint,
    pm_val: nat, mp_val: nat, tt2d_val: nat, zz_val: nat,
)
    requires
        is_well_formed_edwards_point(self_point),
        is_valid_edwards_point(self_point),
        pm_val == math_field_mul(
            math_field_add(spec_field_element(&self_point.Y), spec_field_element(&self_point.X)),
            spec_field_element(&other.Y_minus_X),
        ),
        mp_val == math_field_mul(
            math_field_sub(spec_field_element(&self_point.Y), spec_field_element(&self_point.X)),
            spec_field_element(&other.Y_plus_X),
        ),
        tt2d_val == math_field_mul(spec_field_element(&self_point.T), spec_field_element(&other.T2d)),
        zz_val == math_field_mul(spec_field_element(&self_point.Z), spec_field_element(&other.Z)),
        spec_field_element(&result.X) == math_field_sub(pm_val, mp_val),
        spec_field_element(&result.Y) == math_field_add(pm_val, mp_val),
        spec_field_element(&result.Z) == math_field_sub(math_field_add(zz_val, zz_val), tt2d_val),
        spec_field_element(&result.T) == math_field_add(math_field_add(zz_val, zz_val), tt2d_val),
    ensures
        is_valid_completed_point(result),
        completed_point_as_affine_edwards(result) == ({
            let self_affine = edwards_point_as_affine(self_point);
            let other_affine = projective_niels_point_as_affine_edwards(other);
            edwards_sub(self_affine.0, self_affine.1, other_affine.0, other_affine.1)
        }),
{
    // TODO: Derive from axiom_add_projective_niels_completed_valid.
    // The sub computation = add with negated Niels point:
    //   - Swapping Y_plus_X/Y_minus_X negates x2 in the affine point
    //   - Swapping Z/T reflects neg(T2d) = -T2d in the denominator
    //   - edwards_sub(x1,y1,x2,y2) = edwards_add(x1,y1,-x2,y2) by definition
    //   - lemma_neg_preserves_curve ensures (-x2,y2) is on curve
    admit();
}

/// Exec bridge: EdwardsPoint + AffineNielsPoint -> valid CompletedPoint.
/// Same structure as ProjectiveNiels but uses Z2 = 2*Z1 (affine Niels has Z=1).
pub proof fn axiom_add_affine_niels_completed_valid(
    self_point: crate::edwards::EdwardsPoint,
    other: crate::backend::serial::curve_models::AffineNielsPoint,
    result: crate::backend::serial::curve_models::CompletedPoint,
    pp_val: nat, mm_val: nat, txy2d_val: nat, z2_val: nat,
)
    requires
        is_well_formed_edwards_point(self_point),
        is_valid_edwards_point(self_point),
        pp_val == math_field_mul(
            math_field_add(spec_field_element(&self_point.Y), spec_field_element(&self_point.X)),
            spec_field_element(&other.y_plus_x),
        ),
        mm_val == math_field_mul(
            math_field_sub(spec_field_element(&self_point.Y), spec_field_element(&self_point.X)),
            spec_field_element(&other.y_minus_x),
        ),
        txy2d_val == math_field_mul(spec_field_element(&self_point.T), spec_field_element(&other.xy2d)),
        z2_val == math_field_add(spec_field_element(&self_point.Z), spec_field_element(&self_point.Z)),
        spec_field_element(&result.X) == math_field_sub(pp_val, mm_val),
        spec_field_element(&result.Y) == math_field_add(pp_val, mm_val),
        spec_field_element(&result.Z) == math_field_add(z2_val, txy2d_val),
        spec_field_element(&result.T) == math_field_sub(z2_val, txy2d_val),
    ensures
        is_valid_completed_point(result),
        completed_point_as_affine_edwards(result) == spec_edwards_add_affine_niels(
            self_point, other,
        ),
{
    // TODO: Prove from axiom_edwards_add_complete + FOIL + extended coordinate algebra.
    // Similar to ProjectiveNiels case but Z2 = 2·Z1 instead of ZZ = Z1·Z2.
    admit();
}

/// Exec bridge: EdwardsPoint - AffineNielsPoint -> valid CompletedPoint.
/// Derivable from add variant via edwards_sub = edwards_add with negated point.
pub proof fn axiom_sub_affine_niels_completed_valid(
    self_point: crate::edwards::EdwardsPoint,
    other: crate::backend::serial::curve_models::AffineNielsPoint,
    result: crate::backend::serial::curve_models::CompletedPoint,
    pm_val: nat, mp_val: nat, txy2d_val: nat, z2_val: nat,
)
    requires
        is_well_formed_edwards_point(self_point),
        is_valid_edwards_point(self_point),
        pm_val == math_field_mul(
            math_field_add(spec_field_element(&self_point.Y), spec_field_element(&self_point.X)),
            spec_field_element(&other.y_minus_x),
        ),
        mp_val == math_field_mul(
            math_field_sub(spec_field_element(&self_point.Y), spec_field_element(&self_point.X)),
            spec_field_element(&other.y_plus_x),
        ),
        txy2d_val == math_field_mul(spec_field_element(&self_point.T), spec_field_element(&other.xy2d)),
        z2_val == math_field_add(spec_field_element(&self_point.Z), spec_field_element(&self_point.Z)),
        spec_field_element(&result.X) == math_field_sub(pm_val, mp_val),
        spec_field_element(&result.Y) == math_field_add(pm_val, mp_val),
        spec_field_element(&result.Z) == math_field_sub(z2_val, txy2d_val),
        spec_field_element(&result.T) == math_field_add(z2_val, txy2d_val),
    ensures
        is_valid_completed_point(result),
        completed_point_as_affine_edwards(result) == ({
            let self_affine = edwards_point_as_affine(self_point);
            let other_affine = affine_niels_point_as_affine_edwards(other);
            edwards_sub(self_affine.0, self_affine.1, other_affine.0, other_affine.1)
        }),
{
    // TODO: Derive from axiom_add_affine_niels_completed_valid + lemma_neg_preserves_curve.
    admit();
}

} // verus!
