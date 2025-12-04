//! Abstract field algebra lemmas for GF(p) where p = 2^255 - 19
//!
//! This module contains spec-level proofs about field operations that are
//! independent of the specific limb representation. These lemmas work with
//! the `math_field_*` functions defined in `field_specs.rs`.
//!
//! ## Key Properties
//!
//! - `lemma_field_inv_one`: inv(1) = 1
//! - `lemma_mul_by_inv_one`: x * inv(1) = x
//! - `lemma_neg_square_eq`: (-x)² = x²

#![allow(unused_imports)]
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// Multiplicative Identity Lemmas
// =============================================================================

/// Lemma: inv(1) = 1
///
/// Uses field_inv_property: ((a % p) * inv(a)) % p = 1
pub proof fn lemma_field_inv_one()
    ensures math_field_inv(1) == 1,
{
    // Goal: inv(1) = 1
    //
    // From field_inv_property: 1 * inv(1) ≡ 1 (mod p)
    // So inv(1) ≡ 1 (mod p)
    // Since inv(1) < p, we have inv(1) = 1
    
    p_gt_2();
    
    // 1 % p = 1 (since 1 < p)
    lemma_small_mod(1nat, p());
    
    // field_inv_property gives: (1 * inv(1)) % p = 1 and inv(1) < p
    field_inv_property(1nat);
    let inv = math_field_inv(1);
    
    // inv % p = 1, and since inv < p: inv = 1
    lemma_small_mod(inv, p());
}

/// Lemma: x * inv(1) = x (mod p)
pub proof fn lemma_mul_by_inv_one(x: nat)
    ensures math_field_mul(x % p(), math_field_inv(1)) == x % p(),
{
    // inv(1) = 1, so x * inv(1) = x * 1 = x (mod p)
    lemma_field_inv_one();
    pow255_gt_19();
    lemma_mod_twice(x as int, p() as int);
}

// =============================================================================
// Negation and Square Lemmas
// =============================================================================

/// Lemma: (-x)² = x² (mod p)
///
/// Mathematical proof: (p-a)² = p² - 2pa + a² ≡ a² (mod p)
pub proof fn lemma_neg_square_eq(x: nat)
    ensures math_field_square(math_field_neg(x)) == math_field_square(x % p()),
{
    let a = x % p();
    let neg_x = math_field_neg(x);
    let p = p();
    p_gt_2();
    
    if a == 0 {
        // neg_x = (p - 0) % p = 0, so (-0)² = 0 = 0²
        lemma_mod_self_0(p as int);
        lemma_small_mod(0nat, p);
    } else {
        // a > 0: neg_x = p - a, use (p-a)² ≡ a² (mod p)
        lemma_small_mod((p - a) as nat, p);
        lemma_square_of_complement(a, p);
    }
}

// =============================================================================
// Field Distributivity Lemmas
// =============================================================================

/// Lemma: a · (b + c) = a·b + a·c (mod p)
pub proof fn lemma_field_mul_distributes_over_add(a: nat, b: nat, c: nat)
    ensures
        math_field_mul(a, math_field_add(b, c)) == math_field_add(math_field_mul(a, b), math_field_mul(a, c)),
{
    // Goal: a * ((b+c) % p) % p = ((a*b)%p + (a*c)%p) % p
    //
    // Chain: a * ((b+c) % p)  ≡  a * (b+c)  [mod p absorbs]
    //                         =  a*b + a*c  [integer distrib]
    //                         ≡  (a*b)%p + (a*c)%p  [mod p absorbs]
    
    let p = p();
    p_gt_2();
    
    // Step 1: a * ((b+c) % p) ≡ a * (b+c) (mod p)
    lemma_mul_mod_noop_right(a as int, (b + c) as int, p as int);
    
    // Step 2: a * (b+c) = a*b + a*c
    lemma_mul_is_distributive_add(a as int, b as int, c as int);
    
    // Step 3: (a*b + a*c) % p = ((a*b)%p + (a*c)%p) % p
    lemma_add_mod_noop((a * b) as int, (a * c) as int, p as int);
}

/// Lemma: a * (b % p) = a * b (mod p)
pub proof fn lemma_field_mul_mod_noop(a: nat, b: nat)
    ensures math_field_mul(a, b % p()) == math_field_mul(a, b),
{
    p_gt_2();
    lemma_mul_mod_noop_right(a as int, b as int, p() as int);
}

/// Lemma: (x % p)² = x² (mod p)
pub proof fn lemma_square_mod_noop(x: nat)
    ensures math_field_square(x % p()) == math_field_square(x),
{
    // ((x%p) * (x%p)) % p = (x * x) % p by mod absorption on both factors
    let p = p();
    p_gt_2();
    lemma_mul_mod_noop_left(x as int, x as int, p as int);
    lemma_mul_mod_noop_right((x % p) as int, x as int, p as int);
}

// =============================================================================
// Field Equation Rearrangement Lemmas
// =============================================================================

/// Lemma: If a + b ≡ c - 1, then a + 1 ≡ c - b (mod p)
///
/// Used in sqrt_ratio_implies_on_curve proof.
pub proof fn lemma_field_add_sub_rearrange(a: nat, b: nat, c: nat)
    requires
        a < p(), b < p(), c < p(),
        math_field_add(a, b) == math_field_sub(c, 1),
    ensures
        math_field_add(a, 1) == math_field_sub(c, b),
{
    // Goal: (a + 1) % p = (c + p - b) % p
    //
    // Given: (a + b) % p = (c + p - 1) % p
    // Step 1: Add 1 → (a + b + 1) % p = (c + p) % p = c
    // Step 2: Subtract b → (a + 1) % p = (c - b) % p = (c + p - b) % p
    
    let p = p();
    let (a_int, b_int, c_int, p_int) = (a as int, b as int, c as int, p as int);
    p_gt_2();
    
    // Expand definitions
    lemma_small_mod(c, p);
    lemma_small_mod(1nat, p);
    lemma_small_mod(b, p);
    
    // Step 1: (a + b + 1) % p = c
    lemma_add_mod_noop(a_int + b_int, 1, p_int);
    lemma_add_mod_noop(c_int + p_int - 1, 1, p_int);
    lemma_mod_add_multiples_vanish(c_int, p_int);
    assert((a_int + b_int + 1) % p_int == c_int);
    
    // Step 2: (a + 1) % p = (c - b) % p
    lemma_sub_mod_noop(a_int + b_int + 1, b_int, p_int);
    
    // Step 3: (c - b) % p = (c + p - b) % p
    lemma_mod_add_multiples_vanish(c_int - b_int, p_int);
}

} // verus!

