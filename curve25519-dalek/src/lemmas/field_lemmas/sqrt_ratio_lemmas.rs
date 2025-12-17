//! This file contains lemmas needed to verify sqrt_ratio_i (field.rs) and
//! related decompress proofs.
//!
//! ## Main Lemmas (Public API)
//!
//! - `lemma_is_sqrt_ratio_to_math_field` — converts is_sqrt_ratio to math_field form
//! - `lemma_no_square_root_when_times_i` — failure case: x²·v = i·u implies no r with r²·v = ±u
//! - `lemma_flipped_sign_becomes_correct` — if v·r² = -u, then v·(r·i)² = u
//! - `lemma_algebraic_chain_base` — proves q² = r_squared_v · inv(i·u)
//!
//! ## Dependencies
//!
//! This module uses lemmas from `sqrt_m1_lemmas` for properties of i = sqrt(-1).
//!
//! ## Lemma Dependency Graph
//!
//! ```text
//! sqrt_m1_lemmas::axiom_sqrt_m1_squared ──► sqrt_m1_lemmas::lemma_multiply_by_i_flips_sign
//!                                                           │
//!                                                           ▼
//! sqrt_m1_lemmas::axiom_sqrt_m1_not_square ──┐    lemma_flipped_sign_becomes_correct ◄── field.rs
//!                                            │
//! sqrt_m1_lemmas::axiom_neg_sqrt_m1_not_square ──► lemma_no_square_root_when_times_i ◄── step1_lemmas.rs
//!
//! ```
#![allow(unused_imports)]
use crate::constants;
use crate::lemmas::common_lemmas::div_mod_lemmas::*;
use crate::lemmas::common_lemmas::mul_lemmas::*;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::lemmas::field_lemmas::sqrt_m1_lemmas::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use crate::specs::primality_specs::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

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
/// Prove: is_sqrt_ratio implies the math_field form
///
/// When sqrt_ratio_i returns true and v ≠ 0:
///   is_sqrt_ratio(u, v, X) holds
///   which means: (x * x * v) % p == u
///   which equals: math_field_mul(math_field_square(x), v) == u
pub proof fn lemma_is_sqrt_ratio_to_math_field(
    x: nat,  // spec_field_element(&X)
    u: nat,  // spec_field_element(&u_field_elem)
    v: nat,  // spec_field_element(&v_field_elem)
)
    requires
        math_is_sqrt_ratio(u, v, x),
    ensures
        math_field_mul(math_field_square(x), v) == u % p(),
{
    let p = p();
    p_gt_2();

    // math_field_square(x) = (x * x) % p
    let x2 = math_field_square(x);

    // From requires: (x*x*v) % p == u, so u < p (it's a mod result)
    // Therefore u % p == u
    assert(u % p == u) by {
        lemma_mod_bound(((x * x) * v) as int, p as int);
        lemma_small_mod(u, p);
    };

    // Apply mod absorption: (x*x * v) % p == ((x*x % p) * (v % p)) % p
    // This gives us math_field_mul((x*x) % p, v % p) == u % p
    assert(((x * x) * v) % p == (((x * x) % p) * (v % p)) % p) by {
        lemma_mul_mod_noop_general((x * x) as int, v as int, p as int);
    };

    // Since x2 = (x*x) % p, we have math_field_mul(x2, v % p) == u % p
    // And math_field_mul(x2, v % p) == math_field_mul(x2, v) by mod absorption
    assert(math_field_mul(x2, v) == u % p) by {
        lemma_mul_mod_noop_right(x2 as int, v as int, p as int);
    };
}

/// Unified algebraic chain: proves q² = r_squared_v · inv(i·u)
///
/// This is the geometric/structural part shared by both Case 1 and Case 2.
/// The v terms cancel out, leaving q² = r_squared_v · inv(i·u).
///
/// Given:
///   - r²·v = r_squared_v (could be u or -u)
///   - x²·v = i·u
///   - q = r/x
///
/// Proves: q² = r_squared_v · inv(i·u)
///
/// The caller then uses:
/// - lemma_u_times_inv_iu_is_neg_i (when r_squared_v = u) to get q² = -i
/// - lemma_neg_u_times_inv_iu_is_i (when r_squared_v = -u) to get q² = i
proof fn lemma_algebraic_chain_base(
    r_squared_v: nat,  // The value r²·v evaluates to
    u: nat,
    v: nat,
    x: nat,
    r: nat,
    i: nat,
)
    requires
        v % p() != 0,
        u % p() != 0,
        x % p() != 0,
        x < p(),
        r < p(),
        i == spec_sqrt_m1(),
        i % p() != 0,
        r_squared_v < p(),  // r_squared_v is a field element
        math_field_mul(math_field_square(r), v) == r_squared_v,
        math_field_mul(math_field_square(x), v) == (i * u) % p(),
    ensures
        ({
            let q = math_field_mul(r, math_field_inv(x));
            let iu = math_field_mul(i, u);
            let inv_iu = math_field_inv(iu);
            math_field_square(q) == math_field_mul(r_squared_v, inv_iu)
        }),
{
    let p = p();
    p_gt_2();

    // Define key values
    let r2 = math_field_square(r);
    let x2 = math_field_square(x);
    let inv_v = math_field_inv(v);
    let inv_x = math_field_inv(x);
    let q = math_field_mul(r, inv_x);
    let q2 = math_field_square(q);
    let iu = math_field_mul(i, u);

    // --- Step 1: q² = r² · inv(x²) ---
    let inv_x2 = math_field_inv(x2);
    assert(q2 == math_field_mul(r2, inv_x2)) by {
        lemma_quotient_of_squares(r, x);
    };

    // --- Step 2: Derive r² = r_squared_v · inv(v) from r²·v = r_squared_v ---
    assert(r2 % p == math_field_mul(r_squared_v, inv_v)) by {
        // r_squared_v < p, so r_squared_v % p == r_squared_v
        lemma_small_mod(r_squared_v, p);
        assert(math_field_mul(r2, v) == r_squared_v % p);
        lemma_solve_for_left_factor(r2, v, r_squared_v);
    };

    // --- Step 3: Derive x² = (i·u) · inv(v) from x²·v = i·u ---
    assert(x2 % p == math_field_mul(iu, inv_v)) by {
        lemma_mod_twice((i * u) as int, p as int);
        assert(iu % p == (i * u) % p);
        lemma_solve_for_left_factor(x2, v, iu);
        lemma_mul_mod_noop_left((i * u) as int, inv_v as int, p as int);
    };

    // --- Step 4: Compute inv(x²) = inv(i·u) · v ---

    // First show (i·u) % p != 0
    assert(iu % p != 0) by {
        lemma_mod_bound((i * u) as int, p as int);
        lemma_mod_twice((i * u) as int, p as int);
        if (i * u) % p == 0 {
            axiom_p_is_prime();
            lemma_euclid_prime(i, u, p);
            assert(false);
        }
    };

    // Show inv_v % p != 0
    assert(inv_v % p != 0) by {
        field_inv_property(v);
        lemma_small_mod(inv_v, p);
        if inv_v == 0 {
            assert(((v % p) * 0) % p == 0);
            lemma_small_mod(0, p);
            assert(false);
        }
    };

    let iu_times_inv_v = math_field_mul(iu, inv_v);

    // x2 = iu_times_inv_v (both are < p field elements)
    assert(x2 == iu_times_inv_v) by {
        lemma_mod_bound((x * x) as int, p as int);
        lemma_small_mod(x2, p);
        lemma_mod_bound((iu * inv_v) as int, p as int);
        lemma_small_mod(iu_times_inv_v, p);
    };

    let inv_iu = math_field_inv(iu);

    // inv_x2 = inv(iu) · v
    assert(inv_x2 == math_field_mul(inv_iu, v)) by {
        lemma_inv_of_product(iu, inv_v);
        lemma_inv_of_inv(v);
        lemma_mod_bound(v as int, p as int);
        lemma_mul_mod_noop_right(inv_iu as int, v as int, p as int);
    };

    // --- Step 5: Compute r2 as field element ---
    let r_squared_v_times_inv_v = math_field_mul(r_squared_v, inv_v);
    assert(r2 == r_squared_v_times_inv_v) by {
        lemma_mod_bound((r * r) as int, p as int);
        lemma_small_mod(r2, p);
        lemma_mod_bound((r_squared_v * inv_v) as int, p as int);
        lemma_small_mod(r_squared_v_times_inv_v, p);
    };

    // --- Step 6: q² = r_squared_v · inv(i·u) (v terms cancel) ---
    let r_squared_v_times_inv_iu = math_field_mul(r_squared_v, inv_iu);

    assert(q2 == r_squared_v_times_inv_iu) by {
        // q² = r² · inv_x2 = (r_squared_v · inv_v) · (inv_iu · v)
        // The v terms cancel: inv_v · v = 1
        assert(math_field_mul(inv_v, v) == 1) by {
            field_inv_property(v);
            lemma_mul_mod_noop_left(v as int, inv_v as int, p as int);
            lemma_field_mul_comm(inv_v, v);
        };

        lemma_mul_mod_noop((r_squared_v * inv_v) as int, (inv_iu * v) as int, p as int);

        // (r_squared_v * inv_v) * (inv_iu * v) = r_squared_v * inv_iu * (inv_v * v)
        assert((r_squared_v * inv_v) * (inv_iu * v) == r_squared_v * inv_iu * (inv_v * v)) by {
            lemma_mul_is_associative(r_squared_v as int, inv_v as int, (inv_iu * v) as int);
            lemma_mul_is_associative(inv_v as int, inv_iu as int, v as int);
            lemma_mul_is_commutative(inv_v as int, inv_iu as int);
            lemma_mul_is_associative(inv_iu as int, inv_v as int, v as int);
            lemma_mul_is_associative(r_squared_v as int, inv_iu as int, (inv_v * v) as int);
        };

        assert((inv_v * v) % p == 1) by {
            field_inv_property(v);
            lemma_mul_mod_noop_left(v as int, inv_v as int, p as int);
            lemma_mul_is_commutative(inv_v as int, v as int);
        };

        assert((r_squared_v * inv_iu * (inv_v * v)) % p == (r_squared_v * inv_iu) % p) by {
            lemma_mul_mod_noop_right((r_squared_v * inv_iu) as int, (inv_v * v) as int, p as int);
            lemma_mul_basics((r_squared_v * inv_iu) as int);
        };
    };
}

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
///   - But -i is not a square (axiom_neg_sqrt_m1_not_square)
///   - Contradiction! ∎
///
/// Case 2: Suppose r'²·v = -u for some r'
///   - We have x²·v = i·u (precondition)
///   - Then (r'/x)² = (r'²·v)/(x²·v) = -u/(i·u) = -1/i = -i⁻¹ = -(-i) = i
///   - But i is not a square (axiom_sqrt_m1_not_square)
///   - Contradiction! ∎
pub proof fn lemma_no_square_root_when_times_i(u: nat, v: nat, r: nat)
    requires
        v % p() != 0,
        u % p() != 0,
        r < p(),
        // There exists x with x²·v = i·u
        exists|x: nat|
            x < p() && #[trigger] math_field_mul(math_field_square(x), v) == (spec_sqrt_m1() * u)
                % p(),
    ensures
// r²·v ≠ u and r²·v ≠ -u

        math_field_mul(math_field_square(r), v) != u % p() && math_field_mul(
            math_field_square(r),
            v,
        ) != math_field_neg(u),
{
    let the_p = p();
    let i = spec_sqrt_m1();

    // Get the witness x with x²·v = i·u
    let x = choose|x: nat|
        x < p() && #[trigger] math_field_mul(math_field_square(x), v) == (spec_sqrt_m1() * u) % p();

    // ========== Common Setup ==========
    // These facts are needed by both cases

    // x ≠ 0 (if x = 0, then 0 = i·u, but u ≠ 0 and i ≠ 0)
    assert(x != 0) by {
        if x == 0 {
            assert(math_field_square(0) == 0) by {
                lemma_small_mod(0, the_p);
            };
            assert(math_field_mul(0, v) == 0) by {
                assert(0 * v == 0);  // 0 * anything = 0
                lemma_small_mod(0, the_p);  // 0 % p = 0
            };
            assert(i != 0) by {
                if i == 0 {
                    assert((i * i) % the_p == 0);
                    axiom_sqrt_m1_squared();
                    assert((i * i) % the_p == (the_p - 1) as nat);
                    // Contradiction: (i*i) % p is both 0 and p-1
                    assert(false);
                }
            };
            assert((i * u) % the_p != 0) by {
                if (i * u) % the_p == 0 {
                    axiom_p_is_prime();
                    lemma_euclid_prime(i, u, the_p);
                    assert(i % the_p != 0) by {
                        lemma_small_mod(i, the_p);
                    };
                    // Contradiction: Euclid says i % p == 0 or u % p == 0,
                    // but i % p != 0 (above) and u % p != 0 (from requires)
                    assert(false);
                }
            };
            // Contradiction: x=0 implies LHS=0, but (i*u) % p != 0 means RHS != 0
            assert(false);
        }
    };

    // x % p != 0
    assert(x % the_p != 0) by {
        lemma_small_mod(x, the_p);
    };

    // i ≠ 0
    assert(i != 0) by {
        if i == 0 {
            axiom_sqrt_m1_squared();
            assert(math_field_square(0) == 0);
            assert(math_field_neg(1nat) != 0);
            assert(false);
        }
    };

    // i < p and i % p != 0
    assert(i < the_p) by {
        lemma_mod_bound(spec_field_element_as_nat(&constants::SQRT_M1) as int, the_p as int);
    };
    assert(i % the_p != 0) by {
        lemma_small_mod(i, the_p);
    };

    // Define q = r/x (used in both cases)
    let x_inv = math_field_inv(x);
    let q = math_field_mul(r, x_inv);

    // q < p (since q is a field element)
    assert(q < the_p) by {
        lemma_mod_bound((r * x_inv) as int, the_p as int);
    };

    // ========== Case 1: r²·v = u ==========
    // If true, then q² = -i, but -i is not a square → contradiction
    if math_field_mul(math_field_square(r), v) == u % the_p {
        let r_squared_v = u % the_p;
        let iu = math_field_mul(i, u);
        let inv_iu = math_field_inv(iu);
        let q2 = math_field_square(q);
        let neg_i = (the_p - i) as nat;

        // Step 1: r_squared_v < p
        assert(r_squared_v < the_p) by {
            lemma_mod_bound(u as int, the_p as int);
        };

        // Step 2: q² = r_squared_v · inv(i·u) (from algebraic chain)
        assert(q2 == math_field_mul(r_squared_v, inv_iu)) by {
            lemma_algebraic_chain_base(r_squared_v, u, v, x, r, i);
        };

        // Step 3: u · inv(i·u) = -i
        assert(math_field_mul(u, inv_iu) == math_field_neg(i)) by {
            lemma_u_times_inv_iu_is_neg_i(u, i);
        };

        // Step 4: Connect r_squared_v to u for field multiplication
        assert(math_field_mul(r_squared_v, inv_iu) == math_field_mul(u, inv_iu)) by {
            lemma_mul_mod_noop_left(u as int, inv_iu as int, the_p as int);
        };

        // Step 5: Therefore q² = -i
        assert(q2 == math_field_neg(i));

        // Step 6: Connect math_field_neg(i) to (p - i)
        assert(math_field_neg(i) == neg_i) by {
            lemma_small_mod(i, the_p);
            lemma_small_mod((the_p - i) as nat, the_p);
        };

        // Step 7: -i is not a square (axiom) — CONTRADICTION
        assert(!is_square_mod_p(neg_i)) by {
            axiom_neg_sqrt_m1_not_square();
        };

        // But q² = -i means -i IS a square (q is the witness)
        assert((q * q) % the_p == neg_i % the_p) by {
            lemma_small_mod(q2, the_p);
            lemma_small_mod(neg_i, the_p);
        };
        assert(is_square_mod_p(neg_i));

        // Contradiction: -i is both a square and not a square
        assert(false);
    }
    // ========== Case 2: r²·v = -u ==========
    // If true, then q² = i, but i is not a square → contradiction

    if math_field_mul(math_field_square(r), v) == math_field_neg(u) {
        let r_squared_v = math_field_neg(u);
        let iu = math_field_mul(i, u);
        let inv_iu = math_field_inv(iu);
        let q2 = math_field_square(q);

        // Step 1: r_squared_v < p
        assert(r_squared_v < the_p) by {
            lemma_mod_bound((the_p - (u % the_p)) as int, the_p as int);
        };

        // Step 2: q² = (-u) · inv(i·u) (from algebraic chain)
        assert(q2 == math_field_mul(r_squared_v, inv_iu)) by {
            lemma_algebraic_chain_base(r_squared_v, u, v, x, r, i);
        };

        // Step 3: (-u) · inv(i·u) = i
        assert(math_field_mul(math_field_neg(u), inv_iu) == i % the_p) by {
            lemma_neg_u_times_inv_iu_is_i(u, i);
        };

        // Step 4: Therefore q² = i % p
        assert(q2 == i % the_p);

        // Step 5: i is not a square (axiom) — CONTRADICTION
        assert(!is_square_mod_p(i)) by {
            axiom_sqrt_m1_not_square();
        };

        // But q² = i means i IS a square (q is the witness)
        assert((q * q) % the_p == i % the_p) by {
            lemma_small_mod(q2, the_p);
            lemma_small_mod(i, the_p);
        };
        assert(is_square_mod_p(i));

        // Contradiction: i is both a square and not a square
        assert(false);
    }
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
        ({
            let r_prime = math_field_mul(r, spec_sqrt_m1());
            math_field_mul(v, math_field_square(r_prime)) == u % p()
        }),
{
    pow255_gt_19();
    let pn = p();
    let r2 = r * r;
    let ri = r * spec_sqrt_m1();
    let r_prime = ri % pn;
    let r_prime_sq = r_prime * r_prime;

    // === Step 1: (r·i)² % p = -r² % p ===
    let neg_r2 = ((pn as int - (r2 % pn) as int) % (pn as int)) as nat;
    // lemma_multiply_by_i_flips_sign establishes: (ri)² % p == neg_r2
    lemma_multiply_by_i_flips_sign(r);

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
    assert(r2_mod < pn) by {
        lemma_mod_bound(r2 as int, pn as int);
    };
    assert(pn > 1) by {
        p_gt_2();
    };

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
            assert(v * neg_r2 == 0) by {
                lemma_mul_basics(v as int);
            };
            assert((v * neg_r2) % pn == 0) by {
                lemma_small_mod(0, pn);
            };
            assert((v * r2) % pn == 0) by {
                lemma_mul_mod_noop_right(v as int, r2 as int, pn as int);
                assert((v * 0) % pn == 0) by {
                    lemma_mul_basics(v as int);
                    lemma_small_mod(0, pn);
                };
            };
            assert(((pn - 0) as nat) % pn == 0) by {
                lemma_mod_self_0(pn as int);
            };
        }
    };

    // === Step 4: neg(neg_u) % p = u % p [double negation] ===
    let u_mod = u % pn;
    assert(u_mod < pn) by {
        lemma_mod_bound(u as int, pn as int);
    };

    assert(((pn - neg_u) as nat) % pn == u_mod) by {
        if u_mod > 0 {
            assert(neg_u == (pn - u_mod) as nat) by {
                lemma_small_mod((pn - u_mod) as nat, pn);
            };
            lemma_double_neg_mod(u_mod, pn);
        } else {
            assert(neg_u == 0) by {
                lemma_mod_self_0(pn as int);
            };
            assert(((pn - 0) as nat) % pn == 0) by {
                lemma_mod_self_0(pn as int);
            };
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
