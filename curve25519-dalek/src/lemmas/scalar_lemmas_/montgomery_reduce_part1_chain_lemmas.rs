//! Lemmas for proving `lemma_part1_chain_divisibility`
//!
//! This module contains the proof that after 5 calls to `part1`, we have:
//!   `(T + N×L) ≡ 0 (mod 2^260)`
//!
//! ## Proof Structure
//!
//! The proof uses two helper lemmas:
//!
//! 1. **`lemma_part1_telescoping_expansion`**: Shows that when we weight each
//!    stage equation by its positional factor and sum, the intermediate carries
//!    cancel (telescope), leaving only `c4 × 2^260`.
//!
//! 2. **`lemma_n_times_l_expansion`**: Shows that `(N × L_low) mod 2^260` equals
//!    the weighted sum of polynomial coefficients at positions 0-4.
//!
//! ## Status: FULLY PROVEN ✅
//!
//! All assumes have been eliminated:
//! - **Polynomial multiplication**: Proven via `lemma_poly_mul_5x5_decomposition`
//! - **Final connection**: Proven using enhanced ensures from polynomial expansion
//!
//! See `docs/proofs_for_montgomery_reduce/montgomery_reduce_proofs.md` Part 1 for
//! the mathematical proof.

#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;

use crate::backend::serial::u64::constants;
use crate::specs::scalar52_specs::*;

verus! {

// =============================================================================
// Helper function for L[0] constant
// =============================================================================

/// Returns L[0] = constants::L.limbs[0] as nat
#[inline(always)]
pub(crate) open spec fn l0() -> nat {
    constants::L.limbs[0] as nat
}

/// Converts 5 u64 limbs to a single nat value in radix-2^52
#[inline(always)]
pub(crate) open spec fn five_u64_limbs_to_nat(n0: u64, n1: u64, n2: u64, n3: u64, n4: u64) -> nat {
    (n0 as nat) 
        + (n1 as nat) * pow2(52) 
        + (n2 as nat) * pow2(104) 
        + (n3 as nat) * pow2(156) 
        + (n4 as nat) * pow2(208)
}

// =============================================================================
// Core Polynomial Multiplication Decomposition
// =============================================================================

/// 5×5 polynomial multiplication decomposes into low (positions 0-4) and high (positions 5-8) parts.
///
/// # Mathematical Structure
///
/// Given two 5-term polynomials in radix 2^52:
///   A = a0 + a1×2^52 + a2×2^104 + a3×2^156 + a4×2^208
///   B = b0 + b1×2^52 + b2×2^104 + b3×2^156 + b4×2^208
///
/// Their product A×B has 9 coefficient positions (0-8), where position k
/// collects all cross-products aᵢ×bⱼ with i+j=k.
///
/// # Decomposition
///
/// low_coeffs  = coeff₀ + coeff₁×2^52 + coeff₂×2^104 + coeff₃×2^156 + coeff₄×2^208
/// high_coeffs = coeff₅ + coeff₆×2^52 + coeff₇×2^104 + coeff₈×2^156
///
/// A × B = low_coeffs + high_coeffs × 2^260
///
/// # Usage
///
/// This lemma is called from both `lemma_n_times_l_expansion` (Part 1) and
/// `lemma_part2_chain_quotient` (Part 2) to avoid duplicating the polynomial
/// multiplication proof.
pub(crate) proof fn lemma_poly_mul_5x5_decomposition(
    a0: nat, a1: nat, a2: nat, a3: nat, a4: nat,
    b0: nat, b1: nat, b2: nat, b3: nat, b4: nat,
)
    ensures
        ({
            let a = a0 + a1 * pow2(52) + a2 * pow2(104) + a3 * pow2(156) + a4 * pow2(208);
            let b = b0 + b1 * pow2(52) + b2 * pow2(104) + b3 * pow2(156) + b4 * pow2(208);
            
            // Position coefficients from polynomial multiplication
            let c0 = a0 * b0;
            let c1 = a0 * b1 + a1 * b0;
            let c2 = a0 * b2 + a1 * b1 + a2 * b0;
            let c3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0;
            let c4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0;
            let c5 = a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1;
            let c6 = a2 * b4 + a3 * b3 + a4 * b2;
            let c7 = a3 * b4 + a4 * b3;
            let c8 = a4 * b4;
            
            let low_coeffs = c0 + c1 * pow2(52) + c2 * pow2(104) + c3 * pow2(156) + c4 * pow2(208);
            let high_coeffs = c5 + c6 * pow2(52) + c7 * pow2(104) + c8 * pow2(156);
            
            a * b == low_coeffs + high_coeffs * pow2(260)
        }),
{
    // Power-of-2 relationships
    lemma_pow2_adds(52, 52);    // 2^104
    lemma_pow2_adds(52, 104);   // 2^156
    lemma_pow2_adds(52, 156);   // 2^208
    lemma_pow2_adds(52, 208);   // 2^260
    lemma_pow2_adds(104, 104);  // 2^208
    lemma_pow2_adds(104, 156);  // 2^260
    lemma_pow2_adds(156, 52);   // 2^208
    lemma_pow2_adds(156, 104);  // 2^260
    lemma_pow2_adds(208, 52);   // 2^260
    lemma_pow2_adds(260, 52);   // 2^312
    lemma_pow2_adds(260, 104);  // 2^364
    lemma_pow2_adds(260, 156);  // 2^416
    
    let a = a0 + a1 * pow2(52) + a2 * pow2(104) + a3 * pow2(156) + a4 * pow2(208);
    let b = b0 + b1 * pow2(52) + b2 * pow2(104) + b3 * pow2(156) + b4 * pow2(208);
    
    // Position coefficients
    let c0 = a0 * b0;
    let c1 = a0 * b1 + a1 * b0;
    let c2 = a0 * b2 + a1 * b1 + a2 * b0;
    let c3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0;
    let c4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0;
    let c5 = a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1;
    let c6 = a2 * b4 + a3 * b3 + a4 * b2;
    let c7 = a3 * b4 + a4 * b3;
    let c8 = a4 * b4;
    
    let low_coeffs = c0 + c1 * pow2(52) + c2 * pow2(104) + c3 * pow2(156) + c4 * pow2(208);
    let high_coeffs = c5 + c6 * pow2(52) + c7 * pow2(104) + c8 * pow2(156);
    
    // Full 9-position polynomial
    let full = c0 + c1 * pow2(52) + c2 * pow2(104) + c3 * pow2(156) + c4 * pow2(208)
        + c5 * pow2(260) + c6 * pow2(312) + c7 * pow2(364) + c8 * pow2(416);
    
    // Step 1: a * b == full (polynomial multiplication)
    assert(a * b == full) by {
        broadcast use group_mul_is_commutative_and_distributive;
        broadcast use lemma_mul_is_associative;
        // The broadcast axioms handle the 25-term FOIL expansion automatically
    }
    
    // Step 2: Factor 2^260 from high positions
    assert(c5 * pow2(260) + c6 * pow2(312) + c7 * pow2(364) + c8 * pow2(416) 
        == high_coeffs * pow2(260)) by {
        // c5*2^260 + c6*2^312 + c7*2^364 + c8*2^416
        // = c5*2^260 + c6*2^52*2^260 + c7*2^104*2^260 + c8*2^156*2^260
        // = (c5 + c6*2^52 + c7*2^104 + c8*2^156) * 2^260
        // = high_coeffs * 2^260
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, c5 as int, 
            (c6 * pow2(52) + c7 * pow2(104) + c8 * pow2(156)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, (c6 * pow2(52)) as int,
            (c7 * pow2(104) + c8 * pow2(156)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, (c7 * pow2(104)) as int,
            (c8 * pow2(156)) as int);
        // pow2(52) * pow2(260) = pow2(312), etc.
        assert(pow2(52) * pow2(260) == pow2(312)) by {
            lemma_mul_is_commutative(pow2(52) as int, pow2(260) as int);
        };
        assert(pow2(104) * pow2(260) == pow2(364)) by {
            lemma_mul_is_commutative(pow2(104) as int, pow2(260) as int);
        };
        assert(pow2(156) * pow2(260) == pow2(416)) by {
            lemma_mul_is_commutative(pow2(156) as int, pow2(260) as int);
        };
        // c_i * pow2(k) * pow2(260) = c_i * pow2(k+260)
        assert(c6 * pow2(52) * pow2(260) == c6 * pow2(312)) by {
            assert(c6 * pow2(52) * pow2(260) == c6 * (pow2(52) * pow2(260))) by {
                lemma_mul_is_associative(c6 as int, pow2(52) as int, pow2(260) as int);
            };
        };
        assert(c7 * pow2(104) * pow2(260) == c7 * pow2(364)) by {
            assert(c7 * pow2(104) * pow2(260) == c7 * (pow2(104) * pow2(260))) by {
                lemma_mul_is_associative(c7 as int, pow2(104) as int, pow2(260) as int);
            };
        };
        assert(c8 * pow2(156) * pow2(260) == c8 * pow2(416)) by {
            assert(c8 * pow2(156) * pow2(260) == c8 * (pow2(156) * pow2(260))) by {
                lemma_mul_is_associative(c8 as int, pow2(156) as int, pow2(260) as int);
            };
        };
    };
    
    // Step 3: Combine
    assert(a * b == low_coeffs + high_coeffs * pow2(260));
}

// =============================================================================
// Helper: Polynomial expansion of N × L_low
// =============================================================================

/// Expands N × L_low and shows the coefficient at each position matches
/// what appears in the stage equations.
///
/// # Polynomial Structure
///
/// N = n0 + n1×2^52 + n2×2^104 + n3×2^156 + n4×2^208
/// L_low = l0 + l1×2^52 + l2×2^104 + l3×2^156 + l4×2^208  (with l3 = 0)
///
/// The product N × L_low has coefficients:
/// - Position 0: n0×l0
/// - Position 1: n0×l1 + n1×l0
/// - Position 2: n0×l2 + n1×l1 + n2×l0
/// - Position 3: n1×l2 + n2×l1 + n3×l0  (since l3=0)
/// - Position 4: n0×l4 + n2×l2 + n3×l1 + n4×l0  (since l3=0)
/// - Position ≥5: contribute multiples of 2^260
///
/// # Ensures
///
/// `(n * l_low) % pow2(260) == (low_part) % pow2(260)`
///
/// where `low_part` is the weighted sum of coefficients at positions 0-4.
pub(crate) proof fn lemma_n_times_l_expansion(
    n0: nat, n1: nat, n2: nat, n3: nat, n4: nat,
    l0: nat, l1: nat, l2: nat, l3: nat, l4: nat,
)
    requires
        l3 == 0,  // L[3] = 0 is a property of the group order
    ensures
        // Modular equality: (N × L_low) mod 2^260 == low_part mod 2^260
        ({
            let n = n0 + n1 * pow2(52) + n2 * pow2(104) + n3 * pow2(156) + n4 * pow2(208);
            let l_low = l0 + l1 * pow2(52) + l2 * pow2(104) + l3 * pow2(156) + l4 * pow2(208);
            
            let coeff0 = n0 * l0;
            let coeff1 = n0 * l1 + n1 * l0;
            let coeff2 = n0 * l2 + n1 * l1 + n2 * l0;
            let coeff3 = n1 * l2 + n2 * l1 + n3 * l0;
            let coeff4 = n0 * l4 + n2 * l2 + n3 * l1 + n4 * l0;
            
            (n * l_low) % pow2(260) == (coeff0 + coeff1 * pow2(52) + coeff2 * pow2(104) 
                + coeff3 * pow2(156) + coeff4 * pow2(208)) % pow2(260)
        }),
        // Full decomposition: N × L_low == low_part + high_part where high_part is a multiple of 2^260
        ({
            let n = n0 + n1 * pow2(52) + n2 * pow2(104) + n3 * pow2(156) + n4 * pow2(208);
            let l_low = l0 + l1 * pow2(52) + l2 * pow2(104) + l3 * pow2(156) + l4 * pow2(208);
            
            let coeff0 = n0 * l0;
            let coeff1 = n0 * l1 + n1 * l0;
            let coeff2 = n0 * l2 + n1 * l1 + n2 * l0;
            let coeff3 = n1 * l2 + n2 * l1 + n3 * l0;
            let coeff4 = n0 * l4 + n2 * l2 + n3 * l1 + n4 * l0;
            let low_part = coeff0 + coeff1 * pow2(52) + coeff2 * pow2(104) + coeff3 * pow2(156) + coeff4 * pow2(208);
            
            let coeff5 = n1 * l4 + n3 * l2 + n4 * l1;
            let coeff6 = n2 * l4 + n4 * l2;
            let coeff7 = n3 * l4;
            let coeff8 = n4 * l4;
            let high_part = coeff5 * pow2(260) + coeff6 * pow2(312) + coeff7 * pow2(364) + coeff8 * pow2(416);
            
            n * l_low == low_part + high_part && high_part % pow2(260) == 0
        }),
{
    lemma_pow2_adds(52, 52);    // 2^104
    lemma_pow2_adds(52, 104);   // 2^156
    lemma_pow2_adds(52, 156);   // 2^208
    lemma_pow2_adds(52, 208);   // 2^260
    lemma_pow2_adds(104, 104);  // 2^208
    lemma_pow2_adds(104, 156);  // 2^260
    lemma_pow2_adds(156, 52);   // 2^208
    lemma_pow2_adds(156, 104);  // 2^260
    lemma_pow2_adds(208, 52);   // 2^260
    
    let n = n0 + n1 * pow2(52) + n2 * pow2(104) + n3 * pow2(156) + n4 * pow2(208);
    let l_low = l0 + l1 * pow2(52) + l2 * pow2(104) + l4 * pow2(208);  // l3=0
    
    // Define coefficients at each position
    let coeff0 = n0 * l0;
    let coeff1 = n0 * l1 + n1 * l0;
    let coeff2 = n0 * l2 + n1 * l1 + n2 * l0;
    let coeff3 = n1 * l2 + n2 * l1 + n3 * l0;
    let coeff4 = n0 * l4 + n2 * l2 + n3 * l1 + n4 * l0;
    
    let low_part = coeff0 + coeff1 * pow2(52) + coeff2 * pow2(104) + coeff3 * pow2(156) + coeff4 * pow2(208);
    
    // Terms at positions ≥5 (these are multiples of 2^260):
    let coeff5 = n1 * l4 + n3 * l2 + n4 * l1;
    let coeff6 = n2 * l4 + n4 * l2;
    let coeff7 = n3 * l4;
    let coeff8 = n4 * l4;
    
    let high_part = coeff5 * pow2(260) + coeff6 * pow2(312) + coeff7 * pow2(364) + coeff8 * pow2(416);
    
    // =========================================================================
    // STEP 1: Prove n * l_low == low_part + high_part
    // =========================================================================
    // This is a polynomial multiplication with ~25 cross products.
    // Each cross product n_i * l_j contributes to position (i + j).
    
    // =========================================================================
    // STEP 1: Prove n * l_low == low_part + high_part
    // =========================================================================
    // This is polynomial multiplication in base 2^52.
    // We enable automatic distributivity reasoning with broadcast.
    
    // Power-of-2 relationships for high-part factoring
    lemma_pow2_adds(52, 260);   // 2^312
    lemma_pow2_adds(104, 260);  // 2^364
    lemma_pow2_adds(156, 260);  // 2^416
    
    // Call the general 5×5 polynomial decomposition lemma
    lemma_poly_mul_5x5_decomposition(n0, n1, n2, n3, n4, l0, l1, l2, l3, l4);
    
    // The general lemma proves:
    //   n * l_low == general_low_coeffs + general_high_coeffs * pow2(260)
    // where general coefficients include l3 terms. Since l3 = 0, these terms vanish
    // and our coeff definitions match the general case.
    
    // Extract the general coefficients (with l3 = 0, extra terms vanish)
    let gen_c0 = n0 * l0;
    let gen_c1 = n0 * l1 + n1 * l0;
    let gen_c2 = n0 * l2 + n1 * l1 + n2 * l0;
    let gen_c3 = n0 * l3 + n1 * l2 + n2 * l1 + n3 * l0;  // n0*l3 = 0 since l3 = 0
    let gen_c4 = n0 * l4 + n1 * l3 + n2 * l2 + n3 * l1 + n4 * l0;  // n1*l3 = 0
    let gen_c5 = n1 * l4 + n2 * l3 + n3 * l2 + n4 * l1;  // n2*l3 = 0
    let gen_c6 = n2 * l4 + n3 * l3 + n4 * l2;  // n3*l3 = 0
    let gen_c7 = n3 * l4 + n4 * l3;  // n4*l3 = 0
    let gen_c8 = n4 * l4;
    
    let gen_low = gen_c0 + gen_c1 * pow2(52) + gen_c2 * pow2(104) + gen_c3 * pow2(156) + gen_c4 * pow2(208);
    let gen_high = gen_c5 + gen_c6 * pow2(52) + gen_c7 * pow2(104) + gen_c8 * pow2(156);
    
    // Since l3 = 0, the general coefficients simplify to our coeff definitions
    assert(gen_c0 == coeff0);
    assert(gen_c1 == coeff1);
    assert(gen_c2 == coeff2);
    assert(gen_c3 == coeff3);  // n0*0 + n1*l2 + n2*l1 + n3*l0 = coeff3
    assert(gen_c4 == coeff4);  // n0*l4 + n1*0 + n2*l2 + n3*l1 + n4*l0 = coeff4
    assert(gen_c5 == coeff5);
    assert(gen_c6 == coeff6);
    assert(gen_c7 == coeff7);
    assert(gen_c8 == coeff8);
    
    assert(gen_low == low_part);
    assert(gen_high * pow2(260) == high_part) by {
        // gen_high * 2^260 = (c5 + c6*2^52 + c7*2^104 + c8*2^156) * 2^260
        //                  = c5*2^260 + c6*2^312 + c7*2^364 + c8*2^416 = high_part
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, coeff5 as int, 
            (coeff6 * pow2(52) + coeff7 * pow2(104) + coeff8 * pow2(156)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, (coeff6 * pow2(52)) as int,
            (coeff7 * pow2(104) + coeff8 * pow2(156)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, (coeff7 * pow2(104)) as int,
            (coeff8 * pow2(156)) as int);
        assert(pow2(52) * pow2(260) == pow2(312)) by {
            lemma_mul_is_commutative(pow2(52) as int, pow2(260) as int);
        };
        assert(pow2(104) * pow2(260) == pow2(364)) by {
            lemma_mul_is_commutative(pow2(104) as int, pow2(260) as int);
        };
        assert(pow2(156) * pow2(260) == pow2(416)) by {
            lemma_mul_is_commutative(pow2(156) as int, pow2(260) as int);
        };
        assert(coeff6 * pow2(52) * pow2(260) == coeff6 * pow2(312)) by {
            assert(coeff6 * pow2(52) * pow2(260) == coeff6 * (pow2(52) * pow2(260))) by {
                lemma_mul_is_associative(coeff6 as int, pow2(52) as int, pow2(260) as int);
            };
        };
        assert(coeff7 * pow2(104) * pow2(260) == coeff7 * pow2(364)) by {
            assert(coeff7 * pow2(104) * pow2(260) == coeff7 * (pow2(104) * pow2(260))) by {
                lemma_mul_is_associative(coeff7 as int, pow2(104) as int, pow2(260) as int);
            };
        };
        assert(coeff8 * pow2(156) * pow2(260) == coeff8 * pow2(416)) by {
            assert(coeff8 * pow2(156) * pow2(260) == coeff8 * (pow2(156) * pow2(260))) by {
                lemma_mul_is_associative(coeff8 as int, pow2(156) as int, pow2(260) as int);
            };
        };
    };
    
    // From step 1: n * l_low == low_part + high_part
    assert(n * l_low == low_part + high_part);
    
    // =========================================================================
    // STEP 2: Prove high_part is a multiple of pow2(260)
    // =========================================================================
    
    let k = coeff5 + coeff6 * pow2(52) + coeff7 * pow2(104) + coeff8 * pow2(156);
    
    lemma_pow2_pos(260);
    lemma_pow2_adds(260, 52);   // pow2(312)
    lemma_pow2_adds(260, 104);  // pow2(364)
    lemma_pow2_adds(260, 156);  // pow2(416)
    
    // Prove high_part == k * pow2(260)
    assert(high_part == k * pow2(260)) by {
        // high_part = coeff5*2^260 + coeff6*2^312 + coeff7*2^364 + coeff8*2^416
        // k = coeff5 + coeff6*2^52 + coeff7*2^104 + coeff8*2^156
        // k * 2^260 = (coeff5 + coeff6*2^52 + coeff7*2^104 + coeff8*2^156) * 2^260
        //           = coeff5*2^260 + coeff6*2^52*2^260 + coeff7*2^104*2^260 + coeff8*2^156*2^260
        //           = coeff5*2^260 + coeff6*2^312 + coeff7*2^364 + coeff8*2^416
        //           = high_part
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, coeff5 as int, 
            (coeff6 * pow2(52) + coeff7 * pow2(104) + coeff8 * pow2(156)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, (coeff6 * pow2(52)) as int,
            (coeff7 * pow2(104) + coeff8 * pow2(156)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, (coeff7 * pow2(104)) as int,
            (coeff8 * pow2(156)) as int);
        assert(pow2(52) * pow2(260) == pow2(312)) by {
            lemma_mul_is_commutative(pow2(52) as int, pow2(260) as int);
        };
        assert(pow2(104) * pow2(260) == pow2(364)) by {
            lemma_mul_is_commutative(pow2(104) as int, pow2(260) as int);
        };
        assert(pow2(156) * pow2(260) == pow2(416)) by {
            lemma_mul_is_commutative(pow2(156) as int, pow2(260) as int);
        };
        assert(coeff6 * pow2(52) * pow2(260) == coeff6 * pow2(312)) by {
            assert(coeff6 * pow2(52) * pow2(260) == coeff6 * (pow2(52) * pow2(260))) by {
                lemma_mul_is_associative(coeff6 as int, pow2(52) as int, pow2(260) as int);
            };
        };
        assert(coeff7 * pow2(104) * pow2(260) == coeff7 * pow2(364)) by {
            assert(coeff7 * pow2(104) * pow2(260) == coeff7 * (pow2(104) * pow2(260))) by {
                lemma_mul_is_associative(coeff7 as int, pow2(104) as int, pow2(260) as int);
            };
        };
        assert(coeff8 * pow2(156) * pow2(260) == coeff8 * pow2(416)) by {
            assert(coeff8 * pow2(156) * pow2(260) == coeff8 * (pow2(156) * pow2(260))) by {
                lemma_mul_is_associative(coeff8 as int, pow2(156) as int, pow2(260) as int);
            };
        };
    };
    
    // Now that we've proven high_part == k * pow2(260):
    // high_part % pow2(260) = (k * pow2(260)) % pow2(260) = 0
    //
    // Proof: lemma_mul_mod_noop_right gives:
    //   (k * pow2(260)) % pow2(260) == (k * (pow2(260) % pow2(260))) % pow2(260)
    // And lemma_mod_self_0 gives:
    //   pow2(260) % pow2(260) == 0
    // So: (k * pow2(260)) % pow2(260) == (k * 0) % pow2(260) == 0 % pow2(260) == 0
    lemma_mod_self_0(pow2(260) as int);
    assert(pow2(260) % pow2(260) == 0);
    
    lemma_mul_mod_noop_right(k as int, pow2(260) as int, pow2(260) as int);
    assert((k * pow2(260)) % pow2(260) == (k * (pow2(260) % pow2(260))) % pow2(260));
    assert(k * (pow2(260) % pow2(260)) == k * 0) by {
        lemma_mul_basics(k as int);
    };
    lemma_small_mod(0nat, pow2(260));
    assert((k * pow2(260)) % pow2(260) == 0);
    assert(high_part % pow2(260) == 0);
    
    // =========================================================================
    // STEP 3: Conclude (n * l_low) % pow2(260) == low_part % pow2(260)
    // =========================================================================
    //
    // From step 1: n * l_low == low_part + high_part
    // From step 2: high_part % pow2(260) == 0
    // Therefore: (n * l_low) % pow2(260) == (low_part + high_part) % pow2(260)
    //                                    == (low_part % pow2(260) + high_part % pow2(260)) % pow2(260)
    //                                    == (low_part % pow2(260) + 0) % pow2(260)
    //                                    == low_part % pow2(260)
    
    // (low_part + high_part) % pow2(260) == (low_part % pow2(260) + high_part % pow2(260)) % pow2(260)
    lemma_add_mod_noop(low_part as int, high_part as int, pow2(260) as int);
    
    // Since high_part % pow2(260) == 0:
    // (low_part % pow2(260) + 0) % pow2(260) == low_part % pow2(260)
    assert((low_part + high_part) % pow2(260) == low_part % pow2(260)) by {
        assert((low_part % pow2(260) + 0) % pow2(260) == low_part % pow2(260)) by {
            lemma_mod_twice(low_part as int, pow2(260) as int);
        };
    };
    
    // Since n * l_low == low_part + high_part:
    assert((n * l_low) % pow2(260) == low_part % pow2(260));
}

// =============================================================================
// Helper: Telescoping expansion for part1 chain
// =============================================================================

/// Shows that when we sum the weighted stage equations, the intermediate
/// carries cancel (telescope).
/// 
/// # Stage Equations
///
/// Given the stage equations (where each Sk is the LHS before adding n_k×L[0]):
/// - S0 + n0×L[0] = carry0 × 2^52
/// - S1 + n1×L[0] = carry1 × 2^52  (S1 includes carry0)
/// - S2 + n2×L[0] = carry2 × 2^52  (S2 includes carry1)
/// - S3 + n3×L[0] = carry3 × 2^52  (S3 includes carry2)
/// - S4 + n4×L[0] = carry4 × 2^52  (S4 includes carry3)
///
/// # Telescoping
///
/// When we multiply each equation by 2^(52k) and sum:
/// - c0 appears as: +c0×2^52 (in equation 0) and -c0×2^52 (in weighted equation 1)
/// - Similarly for c1, c2, c3
/// - Only c4 × 2^260 remains
///
/// # Status: FULLY PROVEN ✓
pub(crate) proof fn lemma_part1_telescoping_expansion(
    s0: nat, s1: nat, s2: nat, s3: nat, s4: nat,
    n0: nat, n1: nat, n2: nat, n3: nat, n4: nat,
    c0: nat, c1: nat, c2: nat, c3: nat, c4: nat,
    l0: nat,
)
    requires
        s0 + n0 * l0 == c0 * pow2(52),
        s1 + n1 * l0 == c1 * pow2(52),
        s2 + n2 * l0 == c2 * pow2(52),
        s3 + n3 * l0 == c3 * pow2(52),
        s4 + n4 * l0 == c4 * pow2(52),
    ensures
        (s0 + n0 * l0)
        + (s1 - c0 + n1 * l0) * pow2(52)
        + (s2 - c1 + n2 * l0) * pow2(104)
        + (s3 - c2 + n3 * l0) * pow2(156)
        + (s4 - c3 + n4 * l0) * pow2(208)
        == c4 * pow2(260),
{
    // Establish power-of-2 relationships
    lemma_pow2_adds(52, 52);
    lemma_pow2_adds(52, 104);
    lemma_pow2_adds(52, 156);
    lemma_pow2_adds(52, 208);
    
    // From stage equations, derive adjusted terms
    assert(s0 + n0 * l0 == c0 * pow2(52));
    assert(s1 - c0 + n1 * l0 == c1 * pow2(52) - c0);
    assert(s2 - c1 + n2 * l0 == c2 * pow2(52) - c1);
    assert(s3 - c2 + n3 * l0 == c3 * pow2(52) - c2);
    assert(s4 - c3 + n4 * l0 == c4 * pow2(52) - c3);
    
    // Expand each weighted term using distributivity
    assert((c1 * pow2(52) - c0) * pow2(52) == c1 * pow2(104) - c0 * pow2(52)) by {
        lemma_mul_is_distributive_sub_other_way(pow2(52) as int, (c1 * pow2(52)) as int, c0 as int);
        assert(c1 * pow2(52) * pow2(52) == c1 * pow2(104)) by {
            lemma_mul_is_associative(c1 as int, pow2(52) as int, pow2(52) as int);
        }
    }
    
    assert((c2 * pow2(52) - c1) * pow2(104) == c2 * pow2(156) - c1 * pow2(104)) by {
        lemma_mul_is_distributive_sub_other_way(pow2(104) as int, (c2 * pow2(52)) as int, c1 as int);
        assert(c2 * pow2(52) * pow2(104) == c2 * pow2(156)) by {
            lemma_mul_is_associative(c2 as int, pow2(52) as int, pow2(104) as int);
        }
    }
    
    assert((c3 * pow2(52) - c2) * pow2(156) == c3 * pow2(208) - c2 * pow2(156)) by {
        lemma_mul_is_distributive_sub_other_way(pow2(156) as int, (c3 * pow2(52)) as int, c2 as int);
        assert(c3 * pow2(52) * pow2(156) == c3 * pow2(208)) by {
            lemma_mul_is_associative(c3 as int, pow2(52) as int, pow2(156) as int);
        }
    }
    
    assert((c4 * pow2(52) - c3) * pow2(208) == c4 * pow2(260) - c3 * pow2(208)) by {
        lemma_mul_is_distributive_sub_other_way(pow2(208) as int, (c4 * pow2(52)) as int, c3 as int);
        assert(c4 * pow2(52) * pow2(208) == c4 * pow2(260)) by {
            lemma_mul_is_associative(c4 as int, pow2(52) as int, pow2(208) as int);
        }
    }
    
    // The sum telescopes:
    // c0*2^52 + (c1*2^104 - c0*2^52) + (c2*2^156 - c1*2^104) + (c3*2^208 - c2*2^156) + (c4*2^260 - c3*2^208)
    // = c4 * 2^260
}

// =============================================================================
// Main Lemma: Chaining part1 postconditions
// =============================================================================

/// After all 5 part1 calls, T + N×L ≡ 0 (mod 2^260)
/// 
/// This chains the individual part1 divisibility postconditions to get
/// the global divisibility property.
///
/// # Mathematical Argument
///
/// 1. Each part1 call ensures: `sum_k + n_k × L[0] = carry_k × 2^52`
/// 2. Telescoping: When we weight by positional factors and sum, carries cancel
/// 3. Result: `t_low + nl_low_coeffs = c4 × 2^260`
/// 4. Polynomial expansion: `(n × l_low) mod 2^260 = nl_low_coeffs mod 2^260`
/// 5. Conclusion: `(t_low + n × l_low) mod 2^260 = 0`
///
/// # Status: FULLY PROVEN ✅
///
/// All steps are now proven using:
/// - `lemma_part1_telescoping_expansion` for carry cancellation
/// - `lemma_poly_mul_5x5_decomposition` for polynomial multiplication
/// - `lemma_n_times_l_expansion` for the final connection
pub(crate) proof fn lemma_part1_chain_divisibility(
    limbs: &[u128; 9],
    n0: u64, n1: u64, n2: u64, n3: u64, n4: u64,
    carry0: u128, carry1: u128, carry2: u128, carry3: u128, carry4: u128,
)
    requires
        montgomery_reduce_input_bounds(limbs),
        n0 < pow2(52), n1 < pow2(52), n2 < pow2(52), n3 < pow2(52), n4 < pow2(52),
        
        // Stage equations from part1 postconditions
        limbs[0] as nat + (n0 as nat) * l0() == (carry0 as nat) * pow2(52),
        
        (carry0 as nat + limbs[1] as nat + (n0 as nat) * (constants::L.limbs[1] as nat))
            + (n1 as nat) * l0() == (carry1 as nat) * pow2(52),
            
        (carry1 as nat + limbs[2] as nat 
            + (n0 as nat) * (constants::L.limbs[2] as nat)
            + (n1 as nat) * (constants::L.limbs[1] as nat))
            + (n2 as nat) * l0() == (carry2 as nat) * pow2(52),
            
        (carry2 as nat + limbs[3] as nat 
            + (n1 as nat) * (constants::L.limbs[2] as nat)
            + (n2 as nat) * (constants::L.limbs[1] as nat))
            + (n3 as nat) * l0() == (carry3 as nat) * pow2(52),
            
        (carry3 as nat + limbs[4] as nat 
            + (n0 as nat) * (constants::L.limbs[4] as nat)
            + (n2 as nat) * (constants::L.limbs[2] as nat)
            + (n3 as nat) * (constants::L.limbs[1] as nat))
            + (n4 as nat) * l0() == (carry4 as nat) * pow2(52),
    ensures
        // Divisibility: (t_low + n * l_low) % 2^260 == 0
        ({
            let t_low = limbs[0] as nat 
                + limbs[1] as nat * pow2(52) 
                + limbs[2] as nat * pow2(104) 
                + limbs[3] as nat * pow2(156) 
                + limbs[4] as nat * pow2(208);
            let n = five_u64_limbs_to_nat(n0, n1, n2, n3, n4);
            let l_low = constants::L.limbs[0] as nat
                + constants::L.limbs[1] as nat * pow2(52)
                + constants::L.limbs[2] as nat * pow2(104)
                + constants::L.limbs[3] as nat * pow2(156)
                + constants::L.limbs[4] as nat * pow2(208);
            (t_low + n * l_low) % pow2(260) == 0
        }),
        // Quotient relationship: t_low + nl_low_coeffs == carry4 * 2^260
        // This is the exact form Part 2 needs
        ({
            let t_low = limbs[0] as nat 
                + limbs[1] as nat * pow2(52) 
                + limbs[2] as nat * pow2(104) 
                + limbs[3] as nat * pow2(156) 
                + limbs[4] as nat * pow2(208);
            let l0_val = constants::L.limbs[0] as nat;
            let l1 = constants::L.limbs[1] as nat;
            let l2 = constants::L.limbs[2] as nat;
            let l4 = constants::L.limbs[4] as nat;
            // Polynomial coefficients at positions 0-4
            let coeff0 = (n0 as nat) * l0_val;
            let coeff1 = (n0 as nat) * l1 + (n1 as nat) * l0_val;
            let coeff2 = (n0 as nat) * l2 + (n1 as nat) * l1 + (n2 as nat) * l0_val;
            let coeff3 = (n1 as nat) * l2 + (n2 as nat) * l1 + (n3 as nat) * l0_val;
            let coeff4 = (n0 as nat) * l4 + (n2 as nat) * l2 + (n3 as nat) * l1 + (n4 as nat) * l0_val;
            let nl_low_coeffs = coeff0 + coeff1 * pow2(52) + coeff2 * pow2(104) 
                + coeff3 * pow2(156) + coeff4 * pow2(208);
            t_low + nl_low_coeffs == (carry4 as nat) * pow2(260)
        }),
{
    // =========================================================================
    // Setup
    // =========================================================================
    
    lemma_pow2_adds(52, 52);
    lemma_pow2_adds(52, 104);
    lemma_pow2_adds(52, 156);
    lemma_pow2_adds(52, 208);
    
    let l0_val = constants::L.limbs[0] as nat;
    let l1 = constants::L.limbs[1] as nat;
    let l2 = constants::L.limbs[2] as nat;
    let l3 = constants::L.limbs[3] as nat;  // = 0
    let l4 = constants::L.limbs[4] as nat;
    
    // Extract sums from stage equations
    let s0 = limbs[0] as nat;
    let s1 = carry0 as nat + limbs[1] as nat + (n0 as nat) * l1;
    let s2 = carry1 as nat + limbs[2] as nat + (n0 as nat) * l2 + (n1 as nat) * l1;
    let s3 = carry2 as nat + limbs[3] as nat + (n1 as nat) * l2 + (n2 as nat) * l1;
    let s4 = carry3 as nat + limbs[4] as nat + (n0 as nat) * l4 + (n2 as nat) * l2 + (n3 as nat) * l1;
    
    // =========================================================================
    // Step 1: Call telescoping lemma
    // =========================================================================
    
    lemma_part1_telescoping_expansion(
        s0, s1, s2, s3, s4,
        n0 as nat, n1 as nat, n2 as nat, n3 as nat, n4 as nat,
        carry0 as nat, carry1 as nat, carry2 as nat, carry3 as nat, carry4 as nat,
        l0_val,
    );
    
    // =========================================================================
    // Step 2: Define components
    // =========================================================================
    
    let t_low = limbs[0] as nat 
        + limbs[1] as nat * pow2(52) 
        + limbs[2] as nat * pow2(104) 
        + limbs[3] as nat * pow2(156) 
        + limbs[4] as nat * pow2(208);
    
    let n = five_u64_limbs_to_nat(n0, n1, n2, n3, n4);
    
    let l_low = l0_val + l1 * pow2(52) + l2 * pow2(104) + l3 * pow2(156) + l4 * pow2(208);
    
    // Polynomial coefficients at positions 0-4
    let coeff0 = (n0 as nat) * l0_val;
    let coeff1 = (n0 as nat) * l1 + (n1 as nat) * l0_val;
    let coeff2 = (n0 as nat) * l2 + (n1 as nat) * l1 + (n2 as nat) * l0_val;
    let coeff3 = (n1 as nat) * l2 + (n2 as nat) * l1 + (n3 as nat) * l0_val;
    let coeff4 = (n0 as nat) * l4 + (n2 as nat) * l2 + (n3 as nat) * l1 + (n4 as nat) * l0_val;
    
    let nl_low_coeffs = coeff0 + coeff1 * pow2(52) + coeff2 * pow2(104) 
        + coeff3 * pow2(156) + coeff4 * pow2(208);
    
    // =========================================================================
    // Step 3: Expand (s_k - c_{k-1}) terms
    // =========================================================================
    
    assert(s1 - (carry0 as nat) == limbs[1] as nat + (n0 as nat) * l1);
    assert(s2 - (carry1 as nat) == limbs[2] as nat + (n0 as nat) * l2 + (n1 as nat) * l1);
    assert(s3 - (carry2 as nat) == limbs[3] as nat + (n1 as nat) * l2 + (n2 as nat) * l1);
    assert(s4 - (carry3 as nat) == limbs[4] as nat + (n0 as nat) * l4 + (n2 as nat) * l2 + (n3 as nat) * l1);
    
    // =========================================================================
    // Step 4: Define and expand terms
    // =========================================================================
    
    let term0 = s0 + (n0 as nat) * l0_val;
    let term1 = (s1 - (carry0 as nat) + (n1 as nat) * l0_val) * pow2(52);
    let term2 = (s2 - (carry1 as nat) + (n2 as nat) * l0_val) * pow2(104);
    let term3 = (s3 - (carry2 as nat) + (n3 as nat) * l0_val) * pow2(156);
    let term4 = (s4 - (carry3 as nat) + (n4 as nat) * l0_val) * pow2(208);
    
    assert(term0 == limbs[0] as nat + (n0 as nat) * l0_val);
    assert(term1 == (limbs[1] as nat + (n0 as nat) * l1 + (n1 as nat) * l0_val) * pow2(52));
    assert(term2 == (limbs[2] as nat + (n0 as nat) * l2 + (n1 as nat) * l1 + (n2 as nat) * l0_val) * pow2(104));
    assert(term3 == (limbs[3] as nat + (n1 as nat) * l2 + (n2 as nat) * l1 + (n3 as nat) * l0_val) * pow2(156));
    assert(term4 == (limbs[4] as nat + (n0 as nat) * l4 + (n2 as nat) * l2 + (n3 as nat) * l1 + (n4 as nat) * l0_val) * pow2(208));
    
    // =========================================================================
    // Step 5: Use distributivity to separate limbs from N×L coefficients
    // =========================================================================
    
    assert(term1 == (limbs[1] as nat) * pow2(52) + coeff1 * pow2(52)) by {
        lemma_mul_is_distributive_add_other_way(pow2(52) as int,
            (limbs[1] as nat) as int, ((n0 as nat) * l1 + (n1 as nat) * l0_val) as int);
    }
    
    assert(term2 == (limbs[2] as nat) * pow2(104) + coeff2 * pow2(104)) by {
        lemma_mul_is_distributive_add_other_way(pow2(104) as int,
            (limbs[2] as nat) as int, ((n0 as nat) * l2 + (n1 as nat) * l1 + (n2 as nat) * l0_val) as int);
    }
    
    assert(term3 == (limbs[3] as nat) * pow2(156) + coeff3 * pow2(156)) by {
        lemma_mul_is_distributive_add_other_way(pow2(156) as int,
            (limbs[3] as nat) as int, ((n1 as nat) * l2 + (n2 as nat) * l1 + (n3 as nat) * l0_val) as int);
    }
    
    assert(term4 == (limbs[4] as nat) * pow2(208) + coeff4 * pow2(208)) by {
        lemma_mul_is_distributive_add_other_way(pow2(208) as int,
            (limbs[4] as nat) as int, ((n0 as nat) * l4 + (n2 as nat) * l2 + (n3 as nat) * l1 + (n4 as nat) * l0_val) as int);
    }
    
    // =========================================================================
    // Step 6: Conclude telescoping_sum == t_low + nl_low_coeffs
    // =========================================================================
    
    let telescoping_sum = term0 + term1 + term2 + term3 + term4;
    assert(telescoping_sum == t_low + nl_low_coeffs);
    assert(t_low + nl_low_coeffs == (carry4 as nat) * pow2(260));
    
    // =========================================================================
    // Step 7: Prove (t_low + nl_low_coeffs) % pow2(260) == 0
    // =========================================================================
    
    lemma_pow2_pos(260);
    let val = t_low + nl_low_coeffs;
    let c4_nat = carry4 as nat;
    
    assert(val == c4_nat * pow2(260));
    
    assert((c4_nat * pow2(260)) % pow2(260) == 0) by {
        lemma_mod_self_0(pow2(260) as int);
        lemma_mul_mod_noop_right(c4_nat as int, pow2(260) as int, pow2(260) as int);
        assert(c4_nat * (pow2(260) % pow2(260)) == c4_nat * 0nat);
        assert(c4_nat * 0nat == 0nat);
        assert(0nat % pow2(260) == 0nat) by { lemma_small_mod(0nat, pow2(260)); }
    }
    
    assert(val % pow2(260) == 0);
    
    // =========================================================================
    // Step 8: Call polynomial expansion and conclude
    // =========================================================================
    
    lemma_n_times_l_expansion(
        n0 as nat, n1 as nat, n2 as nat, n3 as nat, n4 as nat,
        l0_val, l1, l2, l3, l4,
    );
    
    assert((n * l_low) % pow2(260) == nl_low_coeffs % pow2(260));
    
    // Final step: combine to get (t_low + n * l_low) % pow2(260) == 0
    //
    // From the enhanced ensures of lemma_n_times_l_expansion:
    // - n * l_low == low_part + high_part
    // - high_part % pow2(260) == 0
    //
    // Since nl_low_coeffs == low_part (same coefficients at positions 0-4):
    // t_low + n * l_low = t_low + low_part + high_part
    //                   = (t_low + nl_low_coeffs) + high_part
    //                   = val + high_part
    //
    // And since both val % pow2(260) == 0 and high_part % pow2(260) == 0:
    // (val + high_part) % pow2(260) == 0
    
    // Define the high-order terms (positions 5-8)
    let coeff5 = (n1 as nat) * l4 + (n3 as nat) * l2 + (n4 as nat) * l1;
    let coeff6 = (n2 as nat) * l4 + (n4 as nat) * l2;
    let coeff7 = (n3 as nat) * l4;
    let coeff8 = (n4 as nat) * l4;
    
    // From polynomial expansion: high_part = terms at positions 5-8
    lemma_pow2_adds(52, 260);   // 2^312
    lemma_pow2_adds(104, 260);  // 2^364
    lemma_pow2_adds(156, 260);  // 2^416
    
    let high_part = coeff5 * pow2(260) + coeff6 * pow2(312) + coeff7 * pow2(364) + coeff8 * pow2(416);
    
    // From the enhanced ensures: n * l_low == nl_low_coeffs + high_part
    // Note: nl_low_coeffs == low_part as defined in the ensures
    assert(n * l_low == nl_low_coeffs + high_part);
    
    // From the enhanced ensures: high_part % pow2(260) == 0
    assert(high_part % pow2(260) == 0);
    
    // Now prove (t_low + n * l_low) % pow2(260) == 0
    assert((t_low + n * l_low) % pow2(260) == 0) by {
        // t_low + n * l_low = t_low + nl_low_coeffs + high_part = val + high_part
        assert(t_low + n * l_low == val + high_part);
        
        // Both summands are divisible by pow2(260)
        // val % pow2(260) == 0 (from Step 7 above)
        // high_part % pow2(260) == 0 (from polynomial expansion)
        
        // (val + high_part) % pow2(260) = ((val % pow2(260)) + (high_part % pow2(260))) % pow2(260)
        lemma_add_mod_noop(val as int, high_part as int, pow2(260) as int);
        assert((val + high_part) % pow2(260) == ((val % pow2(260)) + (high_part % pow2(260))) % pow2(260));
        
        // = (0 + 0) % pow2(260) = 0
        lemma_small_mod(0nat, pow2(260));
    };
}

} // verus!
