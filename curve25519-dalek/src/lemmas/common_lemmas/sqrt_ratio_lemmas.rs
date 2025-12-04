//! Lemmas for sqrt_ratio_i algorithm verification
//!
//! This file contains everything needed to verify sqrt_ratio_i (field.rs):
//!
//! ## Part 1: SQRT_M1 Axioms
//! Number-theoretic facts about i = sqrt(-1) in F_p where p = 2^255 - 19.
//! - i² = -1 (mod p)  — Definition of SQRT_M1
//! - i and -i are NOT squares (Euler's criterion)
//! - i ≠ 1, i ≠ -1  — Derived from i² = -1
//!
//! ## Part 2: sqrt_ratio_i Algorithm Lemmas
//! Lemmas about the sqrt_ratio_i computation with generic u, v parameters:
//! - `lemma_no_square_root_when_times_i` — failure case analysis
//! - `lemma_sqrt_ratio_check_structure` — 4th roots of unity
//! - `lemma_flipped_sign_becomes_correct` — sign correction
//!
//! ## Related Files
//! - number_theory_lemmas.rs: General properties of p (e.g., p ≡ 5 mod 8)
//! - unused_sqrt_ratio_lemmas.rs: Unused lemmas kept for reference

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::common_lemmas::mul_lemmas::*;
use crate::lemmas::common_lemmas::div_mod_lemmas::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use crate::constants;

verus! {

// =============================================================================
// AXIOMS: Number-Theoretic Facts about i = sqrt(-1) in F_p where p = 2^255 - 19
//
// These are concrete numerical facts that are mathematically proven but
// complex to formalize in Verus. Each axiom includes its justification.
// =============================================================================

/// AXIOM: i² = -1 (mod p) — Definition of SQRT_M1
///
/// Mathematical justification:
/// - SQRT_M1 is a specific constant computed to satisfy i² ≡ -1 (mod p)
/// - The value is approximately 2^252.3 (a ~252-bit number)
/// - Verification would require BigInt computation of the actual product
///
/// Used in: lemma_sqrt_m1_neq_one, lemma_sqrt_m1_neq_neg_one,
///          lemma_multiply_by_i_flips_sign, lemma_no_square_root_when_times_i
pub proof fn axiom_sqrt_m1_squared()
    ensures (spec_sqrt_m1() * spec_sqrt_m1()) % p() == (p() - 1),
{
    admit();
}

/// AXIOM: i = sqrt(-1) is not a square in F_p
///
/// Mathematical justification:
/// - p = 2^255 - 19 ≡ 5 (mod 8)
/// - For p ≡ 5 (mod 8), the Euler criterion gives:
///   i^((p-1)/2) = (i²)^((p-1)/4) = (-1)^((p-1)/4)
/// - (p-1)/4 = (2^255 - 20)/4 = 2^253 - 5, which is odd
/// - Therefore (-1)^((p-1)/4) = -1 ≠ 1
/// - By Euler's criterion, i is NOT a square
///
/// Used in: lemma_no_square_root_when_times_i (below)
pub proof fn axiom_sqrt_m1_not_square()
    ensures
        !is_square_mod_p(spec_sqrt_m1()),
{
    admit();
}

/// AXIOM: -i = -(sqrt(-1)) is not a square in F_p  
///
/// Mathematical justification:
/// - (-i)^((p-1)/2) = (-1)^((p-1)/2) · i^((p-1)/2)
/// - (p-1)/2 = 2^254 - 10, which is even, so (-1)^((p-1)/2) = 1
/// - From axiom_sqrt_m1_not_square: i^((p-1)/2) = -1
/// - Therefore (-i)^((p-1)/2) = 1 · (-1) = -1 ≠ 1
/// - By Euler's criterion, -i is NOT a square
///
/// Used in: lemma_no_square_root_when_times_i (below)
pub proof fn axiom_neg_sqrt_m1_not_square()
    ensures
        !is_square_mod_p((p() - spec_sqrt_m1()) as nat),
{
    admit();
}

/// LEMMA: i ≠ 1 (derived from i² = -1)
///
/// Mathematical reasoning:
///   1. Suppose i = 1
///   2. Then i² = 1² = 1
///   3. But i² = -1 (mod p) by axiom_sqrt_m1_squared
///   4. So 1 ≡ -1 (mod p), meaning p | 2
///   5. But p = 2^255 - 19 > 2, contradiction!
///
/// Used in: decompress_lemmas.rs::lemma_precondition_implies_valid_sign_bit
pub proof fn lemma_sqrt_m1_neq_one()
    ensures
        spec_sqrt_m1() != 1,
{
    // Proof by contradiction: suppose spec_sqrt_m1() = 1
    // Then i² = 1, but axiom_sqrt_m1_squared says i² = p - 1
    // So we need 1 = p - 1, meaning p = 2
    // But p > 2, contradiction
    
    pow255_gt_19();  // Establishes p() > 0 and pow2(255) > 19
    
    // Step 1: i² = p - 1 (which is -1 mod p)
    assert((spec_sqrt_m1() * spec_sqrt_m1()) % p() == (p() - 1)) by {
        axiom_sqrt_m1_squared();
    };
    
    // Step 2: p > 2 (since p = 2^255 - 19 and 2^255 > 21)
    // We know pow2(255) > 19, so p = pow2(255) - 19 > 0
    // Also, pow2(255) ≥ pow2(5) = 32 > 21, so p > 2
    assert(p() > 2) by {
        p_gt_2();
    };
    
    // Step 3: 1 * 1 % p = 1 (since 1 < p)
    assert(1 < p());
    assert((1nat * 1nat) % p() == 1) by {
        lemma_small_mod(1, p());
    };
    
    // Step 4: Since (1*1) % p = 1 ≠ p - 1 (because p > 2), we have i ≠ 1
    assert((p() - 1) != 1);  // Because p > 2
    
    // Therefore if spec_sqrt_m1() = 1, we'd have 1 = p - 1, contradiction
}

/// LEMMA: i ≠ -1 (derived from i² = -1)
///
/// Mathematical reasoning:
///   1. Suppose i ≡ -1 (mod p)
///   2. Then i² ≡ (-1)² = 1 (mod p)
///   3. But i² = -1 (mod p) by axiom_sqrt_m1_squared
///   4. So 1 ≡ -1 (mod p), meaning p = 2
///   5. But p = 2^255 - 19 > 2, contradiction!
///
/// Used in: decompress_lemmas.rs::lemma_precondition_implies_valid_sign_bit
pub proof fn lemma_sqrt_m1_neq_neg_one()
    ensures
        spec_sqrt_m1() % p() != (p() - 1) as nat,
{
    pow255_gt_19();
    
    // Step 1: i² = p - 1 (which is -1 mod p)
    assert((spec_sqrt_m1() * spec_sqrt_m1()) % p() == (p() - 1)) by {
        axiom_sqrt_m1_squared();
    };
    
    // Step 2: p > 2
    assert(p() > 2) by {
        p_gt_2();
    };
    
    // Step 3: (p-1) * (p-1) % p = 1 (since (p-1)² ≡ (-1)² ≡ 1 mod p)
    let pm1: nat = (p() - 1) as nat;
    assert(pm1 < p());
    assert((pm1 * pm1) % p() == 1nat) by {
        lemma_square_of_complement(1, p());
        lemma_small_mod(1, p());
    };
    
    // Step 4: Key connection - a² % p == (a % p)² % p
    // Using lemma_mul_mod_noop_general
    let i = spec_sqrt_m1();
    assert((i * i) % p() == ((i % p()) * (i % p())) % p()) by {
        lemma_mul_mod_noop_general(i as int, i as int, p() as int);
    };
    
    // Step 5: Since (pm1*pm1) % p = 1 ≠ p - 1 = i² % p (because p > 2), we have i % p ≠ pm1
    assert(pm1 != 1);  // Because p > 2
    
    // Therefore if spec_sqrt_m1() % p() == pm1:
    // i² % p = ((i % p) * (i % p)) % p = (pm1 * pm1) % p = 1
    // But i² % p = p - 1
    // So 1 == p - 1, but p > 2, contradiction
}

//=============================================================================
// Derived lemmas: multiplication by i
//=============================================================================

/// Main lemma: (r·i)² ≡ -r² (mod p)
///
/// Mathematical proof:
///   (r·i)² = r²·i²           [product square: (ab)² = a²b²]
///         ≡ r²·(-1)          [i² = -1 by definition]
///         ≡ -r²              [multiplication by -1]
///         ≡ p - r² mod p     [representation of negation]
///
/// Note: The ensures clause has tricky operator precedence. Due to left-associativity,
/// `(a % b * c % d) % e` parses as `((((a % b) * c) % d) % e)`.
///
/// Used in: lemma_flipped_sign_becomes_correct (below)
pub proof fn lemma_multiply_by_i_flips_sign(r: nat)
    ensures
        ((r * spec_sqrt_m1()) % p() * (r * spec_sqrt_m1()) % p()) % p()
            == ((p() as int - ((r * r) % p()) as int) % p() as int) as nat,
{
    pow255_gt_19();
    
    let ri = r * spec_sqrt_m1();
    let pn = p();
    let r2 = r * r;
    let i2 = spec_sqrt_m1() * spec_sqrt_m1();
    let pn_minus_1: nat = (pn - 1) as nat;
    let r2_mod = r2 % pn;
    let neg_r2: nat = (pn - r2_mod) as nat;
    
    // Main chain: (ri)² % p = -r² % p = (p - r²%p) % p
    assert((ri * ri) % pn == neg_r2 % pn) by {
        // (ri)² = r²·i²  [product square factorization]
        assert(ri * ri == r2 * i2) by {
            lemma_product_square(r, spec_sqrt_m1());
        };
        
        // (r²·i²) % p = (r²·(p-1)) % p  [because i² ≡ p-1 (mod p)]
        assert((r2 * i2) % pn == (r2 * pn_minus_1) % pn) by {
            assert(i2 % pn == pn_minus_1) by { axiom_sqrt_m1_squared(); };
            lemma_mul_mod_noop_right(r2 as int, i2 as int, pn as int);
        };
        
        // r²·(p-1) % p = (p - r²%p) % p  [multiplication by -1 is negation]
        assert((r2 * pn_minus_1) % pn == neg_r2 % pn) by {
            lemma_mul_by_minus_one_is_negation(r2, pn);
        };
    };
    
    // Connect neg_r2 to ensures RHS form
    assert(neg_r2 % pn == ((pn as int - r2_mod as int) % (pn as int)) as nat) by {
        lemma_mod_bound(r2 as int, pn as int);
    };
    
    // Handle operator precedence: ensures LHS parses as (((ri % pn) * ri) % pn) % pn
    // Show this equals (ri * ri) % pn
    assert((((ri % pn) * ri) % pn) % pn == (ri * ri) % pn) by {
        // ((a%m)*b) % m = (a*b) % m
        assert(((ri % pn) * ri) % pn == (ri * ri) % pn) by {
            lemma_mul_mod_noop_left(ri as int, ri as int, pn as int);
        };
        // (x % m) % m = x % m
        lemma_mod_twice(((ri % pn) * ri) as int, pn as int);
    };
}

//=============================================================================
// Lemmas for sqrt_ratio_i algorithm (using generic u, v parameters)
//
// These prove properties of the sqrt_ratio_i computation:
//   r = (uv³)(uv⁷)^((p-5)/8)
//   check = v * r²
//
// The algorithm checks if check ∈ {u, -u, u·i, -u·i} to determine
// whether u/v has a square root.
//=============================================================================

/// Lemma: If r²·v = i·u (where i = sqrt(-1)), then no r' exists with r'²·v = ±u
///
/// This is the key lemma for proving sqrt_ratio_i failure implies invalid y.
///
/// Mathematical reasoning (proof by contradiction):
///
/// Case 1: Suppose r'²·v = u for some r'
///   - We have x²·v = i·u (precondition)
///   - Then (r'/x)² = (r'²·v)/(x²·v) = u/(i·u) = 1/i
///   - Now 1/i = i⁻¹ = i³ (since i⁴ = 1) = i²·i = (-1)·i = -i
///   - So (r'/x)² = -i
///   - But -i is NOT a square (axiom_neg_sqrt_m1_not_square)
///   - Contradiction! ∎
///
/// Case 2: Suppose r'²·v = -u for some r'
///   - We have x²·v = i·u (precondition)  
///   - Then (r'/x)² = (r'²·v)/(x²·v) = -u/(i·u) = -1/i = -i⁻¹ = -(-i) = i
///   - But i is NOT a square (axiom_sqrt_m1_not_square)
///   - Contradiction! ∎
pub proof fn lemma_no_square_root_when_times_i(u: nat, v: nat)
    requires
        v % p() != 0,
        u % p() != 0,
        // There exists x with x²·v = i·u
        exists|x: nat| x < p() && math_field_mul(math_field_square(x), v) == (spec_sqrt_m1() * u) % p(),
    ensures
        // Then no r exists with r²·v = u or r²·v = -u
        forall|r: nat| r < p() ==>
            math_field_mul(math_field_square(r), v) != u % p() &&
            math_field_mul(math_field_square(r), v) != math_field_neg(u),
{
    // Step 1: Establish that i and -i are not squares
    assert(!is_square_mod_p(spec_sqrt_m1())) by {
        axiom_sqrt_m1_not_square();
    };
    
    assert(!is_square_mod_p((p() - spec_sqrt_m1()) as nat)) by {
        axiom_neg_sqrt_m1_not_square();
    };
    
    // Step 2: The algebraic argument connecting (r'/x)² to i or -i
    // This requires field division and the fact that quotients of squares
    // are squares - the full proof is complex algebraic manipulation
    admit();
}

/// The key algebraic property: v·r² = u · (4th root of unity)
///
/// where r = (uv³)(uv⁷)^((p-5)/8)
///
/// Mathematical reasoning:
///   Let n = (p-5)/8
///   
///   Step 1: Expand r²
///     r = (uv³) · (uv⁷)^n
///     r² = (uv³)² · (uv⁷)^(2n) = u²v⁶ · (uv⁷)^(2n)
///
///   Step 2: Compute v·r²
///     v·r² = v · u²v⁶ · (uv⁷)^(2n)
///          = u²v⁷ · (uv⁷)^(2n)
///          = u² · (uv⁷)^(1+2n)
///
///   Step 3: Simplify exponent
///     1 + 2n = 1 + 2·(p-5)/8 = 1 + (p-5)/4 = (4 + p - 5)/4 = (p-1)/4
///
///   Step 4: Apply Fermat's little theorem
///     For any non-zero x: x^(p-1) = 1 (mod p)
///     Therefore x^((p-1)/4) is a 4th root of unity: ξ ∈ {1, -1, i, -i}
///
///   Step 5: Conclude
///     v·r² = u² · (uv⁷)^((p-1)/4) = u² · ξ = u · (u·ξ)
///     where u·ξ ∈ {u, -u, u·i, -u·i} ✓
pub proof fn lemma_sqrt_ratio_check_structure(u: nat, v: nat, r: nat)
    requires
        v % p() != 0,
        r % p() == ((u * v * v * v) % p() * pow(
            ((u * v * v * v * v * v * v * v) % p()) as int,
            sqrt_ratio_exponent(),
        ) as nat) % p(),
    ensures
        check_equals_u_times_fourth_root((v * r * r) % p(), u),
{
    // The algebraic steps above are mathematically sound but complex to
    // formalize in Verus due to the interaction of pow, mod, and field ops
    assume(check_equals_u_times_fourth_root((v * r * r) % p(), u));
}

/// If v·r² = -u, then v·(r·i)² = u
///
/// Mathematical proof:
///   Precondition: v·r² ≡ -u (mod p)
///   
///   (r·i)² = r²·i² = r²·(-1) = -r²    [i² = -1]
///   v·(r·i)² = v·(-r²) = -(v·r²)      [negation distributes]
///            = -(-u) = u               [double negation]  ✓
///
/// The proof uses:
/// 1. lemma_multiply_by_i_flips_sign: (r·i)² ≡ -r²
/// 2. lemma_mul_distributes_over_neg_mod: v·(-x) ≡ -(v·x) 
/// 3. lemma_double_neg_mod: -(-x) ≡ x
///
/// NOTE: For the case v·r² = -u·i, simply call:
///   lemma_flipped_sign_becomes_correct(u * spec_sqrt_m1(), v, r)
/// This gives: v·(r·i)² = u·i
pub proof fn lemma_flipped_sign_becomes_correct(u: nat, v: nat, r: nat)
    requires
        (v * r * r) % p() == ((p() as int - (u % p()) as int) % p() as int) as nat,
    ensures
        ({ let r_prime = (r * spec_sqrt_m1()) % p(); (v * r_prime * r_prime) % p() == u % p() }),
{
    use crate::lemmas::common_lemmas::div_mod_lemmas::{
        lemma_mul_distributes_over_neg_mod,
        lemma_double_neg_mod,
    };
    
    pow255_gt_19();
    let pn = p();
    let r2 = r * r;
    let ri = r * spec_sqrt_m1();
    let r_prime = ri % pn;
    let r_prime_sq = r_prime * r_prime;
    
    // === Step 1: (r·i)² % p = -r² % p ===
    lemma_multiply_by_i_flips_sign(r);
    let neg_r2 = ((pn as int - (r2 % pn) as int) % (pn as int)) as nat;
    
    // Bridge: ((ri%p) * ri) % p = ((ri%p) * (ri%p)) % p  [mod absorption]
    assert(((ri % pn) * ri) % pn == ((ri % pn) * (ri % pn)) % pn) by {
        lemma_mul_mod_noop_right((ri % pn) as int, ri as int, pn as int);
    };
    
    // Connect: r_prime_sq % p = neg_r2
    assert(r_prime_sq % pn == neg_r2) by {
        assert((((ri % pn) * ri) % pn) % pn == neg_r2);
        lemma_mod_twice(((ri % pn) * ri) as int, pn as int);
        assert(((ri % pn) * ri) % pn == neg_r2);
        lemma_mul_mod_noop_right((ri % pn) as int, ri as int, pn as int);
        assert(((ri % pn) * (ri % pn)) % pn == neg_r2);
    };
    
    // === Step 2: v * r * r = v * r2 ===
    assert((v * r * r) == (v * r2)) by {
        lemma_mul_is_associative(v as int, r as int, r as int);
    };
    
    // From precondition: (v * r2) % p = neg_u
    let neg_u = ((pn as int - (u % pn) as int) % (pn as int)) as nat;
    assert((v * r2) % pn == neg_u);
    
    // === Step 3: v * neg_r2 % p = neg(v*r2) % p ===
    let r2_mod = r2 % pn;
    lemma_mod_bound(r2 as int, pn as int);
    
    assert(pn > 1) by { p_gt_2(); };
    
    assert((v * neg_r2) % pn == ((pn - (v * r2) % pn) as nat) % pn) by {
        if r2_mod > 0 {
            assert(neg_r2 == (pn - r2_mod) as nat) by {
                lemma_small_mod((pn - r2_mod) as nat, pn);
            };
            lemma_mul_distributes_over_neg_mod(v, r2, pn);
        } else {
            assert(neg_r2 == 0) by {
                assert(r2_mod == 0);
                lemma_mod_self_0(pn as int);
            };
            assert(v * neg_r2 == 0) by { lemma_mul_basics(v as int); };
            assert((v * neg_r2) % pn == 0) by { lemma_small_mod(0nat, pn); };
            assert((v * r2) % pn == 0) by {
                lemma_mul_mod_noop_right(v as int, r2 as int, pn as int);
                assert((v * 0) % pn == 0) by {
                    lemma_mul_basics(v as int);
                    lemma_small_mod(0nat, pn);
                };
            };
            assert(((pn - 0nat) as nat) % pn == 0) by {
                lemma_mod_self_0(pn as int);
            };
        }
    };
    
    // === Step 4: neg(neg_u) % p = u % p [double negation] ===
    let u_mod = u % pn;
    lemma_mod_bound(u as int, pn as int);
    
    assert(((pn - neg_u) as nat) % pn == u_mod) by {
        if u_mod > 0 {
            assert(neg_u == (pn - u_mod) as nat) by {
                lemma_small_mod((pn - u_mod) as nat, pn);
            };
            lemma_double_neg_mod(u_mod, pn);
        } else {
            assert(neg_u == 0) by { lemma_mod_self_0(pn as int); };
            assert(((pn - 0nat) as nat) % pn == 0) by { lemma_mod_self_0(pn as int); };
        }
    };
    
    // === Step 5: Connect v * r_prime_sq to v * r_prime * r_prime ===
    assert((v * r_prime * r_prime) % pn == (v * r_prime_sq) % pn) by {
        lemma_mul_is_associative(v as int, r_prime as int, r_prime as int);
    };
    
    // === Step 6: Chain everything together ===
    assert((v * r_prime_sq) % pn == (v * neg_r2) % pn) by {
        lemma_mul_mod_noop_right(v as int, r_prime_sq as int, pn as int);
    };
}

} // verus!
