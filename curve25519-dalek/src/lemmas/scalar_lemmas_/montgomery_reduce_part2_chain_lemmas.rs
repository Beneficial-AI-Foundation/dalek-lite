//! Lemmas for proving `lemma_part2_chain_quotient`
//!
//! This module contains the proof that after 4 calls to `part2`, we have:
//!   `intermediate = (T + N×L) / R`
//!
//! where intermediate = [r0, r1, r2, r3, r4].
//!
//! ## Proof Structure
//!
//! The proof uses the telescoping technique:
//!
//! 1. **Stage equations from part2**:
//!    - sum5 = r0 + carry5 × 2^52
//!    - sum6 = r1 + carry6 × 2^52
//!    - sum7 = r2 + carry7 × 2^52
//!    - sum8 = r3 + carry8 × 2^52 (where r4 = carry8)
//!
//! 2. **Telescoping**: Multiply by positional weights and sum.
//!    The intermediate carries cancel, leaving:
//!    sum5 + sum6×2^52 + sum7×2^104 + sum8×2^156
//!    = r0 + r1×2^52 + r2×2^104 + r3×2^156 + r4×2^208
//!
//! 3. **Connection**: The weighted sum of sums equals (T + N×L) / R
//!    because Part 1 zeroed out the low 260 bits.
//!
//! See `docs/proofs_for_montgomery_reduce/montgomery_reduce_proofs.md` Part 2 for
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
// Helper lemma: group_order equals limb polynomial
// =============================================================================

/// Proves that group_order() equals the explicit limb polynomial of L.
/// This isolates the computation from the main proof to avoid solver timeout.
#[verifier::rlimit(20)]
pub(crate) proof fn lemma_group_order_equals_l_poly()
    ensures
        group_order() == constants::L.limbs[0] as nat 
            + (constants::L.limbs[1] as nat) * pow2(52)
            + (constants::L.limbs[2] as nat) * pow2(104)
            + (constants::L.limbs[3] as nat) * pow2(156)
            + (constants::L.limbs[4] as nat) * pow2(208),
{
    use crate::lemmas::scalar_lemmas::{lemma_l_equals_group_order, lemma_five_limbs_equals_to_nat};
    use crate::specs::scalar52_specs::five_limbs_to_nat_aux;
    
    // lemma_l_equals_group_order proves: scalar52_to_nat(&constants::L) == group_order()
    lemma_l_equals_group_order();
    
    // lemma_five_limbs_equals_to_nat proves: five_limbs_to_nat_aux(L.limbs) == limbs52_to_nat(&L.limbs)
    lemma_five_limbs_equals_to_nat(&constants::L.limbs);
    
    // five_limbs_to_nat_aux(L.limbs) = L[0] + pow2(52)*L[1] + pow2(104)*L[2] + pow2(156)*L[3] + pow2(208)*L[4]
    // By commutativity, this equals: L[0] + L[1]*pow2(52) + L[2]*pow2(104) + L[3]*pow2(156) + L[4]*pow2(208)
    use vstd::arithmetic::mul::lemma_mul_is_commutative;
    lemma_mul_is_commutative(pow2(52) as int, constants::L.limbs[1] as int);
    lemma_mul_is_commutative(pow2(104) as int, constants::L.limbs[2] as int);
    lemma_mul_is_commutative(pow2(156) as int, constants::L.limbs[3] as int);
    lemma_mul_is_commutative(pow2(208) as int, constants::L.limbs[4] as int);
}

// =============================================================================
// Helper spec functions
// =============================================================================

/// Converts 5 u64 limbs to a single nat value in radix-2^52
/// (Same as in part1_chain_lemmas, but defined here for locality)
#[inline(always)]
pub(crate) open spec fn five_u64_limbs_to_nat(r0: u64, r1: u64, r2: u64, r3: u64, r4: u64) -> nat {
    (r0 as nat) 
        + (r1 as nat) * pow2(52) 
        + (r2 as nat) * pow2(104) 
        + (r3 as nat) * pow2(156) 
        + (r4 as nat) * pow2(208)
}

/// The high part of T (positions 5-8)
#[inline(always)]
pub(crate) open spec fn t_high(limbs: &[u128; 9]) -> nat {
    (limbs[5] as nat)
        + (limbs[6] as nat) * pow2(52)
        + (limbs[7] as nat) * pow2(104)
        + (limbs[8] as nat) * pow2(156)
}

/// The high part of N×L (positions 5-8, the parts that contribute to division)
/// These are the cross products nᵢ × L[m] where i + m ≥ 5
#[inline(always)]
pub(crate) open spec fn nl_high_contribution(
    n0: u64, n1: u64, n2: u64, n3: u64, n4: u64
) -> nat {
    let l1 = constants::L.limbs[1] as nat;
    let l2 = constants::L.limbs[2] as nat;
    // L[3] = 0
    let l4 = constants::L.limbs[4] as nat;
    
    // Position 5 contributions: n1×L[4] + n3×L[2] + n4×L[1]
    let pos5 = (n1 as nat) * l4 + (n3 as nat) * l2 + (n4 as nat) * l1;
    
    // Position 6 contributions: n2×L[4] + n4×L[2]
    let pos6 = (n2 as nat) * l4 + (n4 as nat) * l2;
    
    // Position 7 contributions: n3×L[4]
    let pos7 = (n3 as nat) * l4;
    
    // Position 8 contributions: n4×L[4]
    let pos8 = (n4 as nat) * l4;
    
    pos5 + pos6 * pow2(52) + pos7 * pow2(104) + pos8 * pow2(156)
}

// =============================================================================
// Main Quotient Lemma
// =============================================================================
//
// Note: The original "telescoping" lemma was removed because it had an incorrect
// formulation - it didn't account for carry chaining in the sum definitions.
// The proof now works directly via carry cancellation analysis in the main lemma.

/// After all 4 part2 calls, intermediate = (T + N×L) / R
///
/// This chains the individual part2 postconditions with the divisibility
/// result from Part 1 to establish that the intermediate value equals
/// the exact quotient of (T + N×L) divided by R.
///
/// # Mathematical Argument
///
/// 1. From Part 1: (T + N×L) ≡ 0 (mod R), so T + N×L = k × R for some k
/// 2. Part 2 computes k by extracting the high bits after division by R
/// 3. The sums at positions 5-8 represent (T + N×L) >> 260
/// 4. Telescoping shows: r0 + r1×2^52 + ... + r4×2^208 = k
/// 5. Therefore: intermediate = (T + N×L) / R
///
/// # Preconditions
///
/// - Part 1 divisibility must be established
/// - Stage equations from part2 postconditions
/// - Carry chain from part1's final carry (carry4) to part2's inputs
pub(crate) proof fn lemma_part2_chain_quotient(
    limbs: &[u128; 9],
    // N values from Part 1
    n0: u64, n1: u64, n2: u64, n3: u64, n4: u64,
    // Final carry from Part 1
    carry4: u128,
    // Part 2 sums
    sum5: u128, sum6: u128, sum7: u128, sum8: u128,
    // Part 2 carries
    carry5: u128, carry6: u128, carry7: u128,
    // Part 2 outputs
    r0: u64, r1: u64, r2: u64, r3: u64, r4: u64,
)
    requires
        montgomery_reduce_input_bounds(limbs),
        
        // N bounds (from part1 postconditions)
        n0 < pow2(52), n1 < pow2(52), n2 < pow2(52), n3 < pow2(52), n4 < pow2(52),
        
        // Part 1 divisibility result (T + N×L) ≡ 0 (mod 2^260)
        ({
            let t_low = limbs[0] as nat 
                + limbs[1] as nat * pow2(52) 
                + limbs[2] as nat * pow2(104) 
                + limbs[3] as nat * pow2(156) 
                + limbs[4] as nat * pow2(208);
            let n = super::montgomery_reduce_part1_chain_lemmas::five_u64_limbs_to_nat(n0, n1, n2, n3, n4);
            let l_low = constants::L.limbs[0] as nat
                + constants::L.limbs[1] as nat * pow2(52)
                + constants::L.limbs[2] as nat * pow2(104)
                + constants::L.limbs[3] as nat * pow2(156)
                + constants::L.limbs[4] as nat * pow2(208);
            (t_low + n * l_low) % pow2(260) == 0
        }),
        
        // Part 1 quotient result: t_low + nl_low_coeffs == carry4 * 2^260
        // This is the key fact from Part 1's telescoping that we need for the quotient calculation
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
            let coeff0 = (n0 as nat) * l0_val;
            let coeff1 = (n0 as nat) * l1 + (n1 as nat) * l0_val;
            let coeff2 = (n0 as nat) * l2 + (n1 as nat) * l1 + (n2 as nat) * l0_val;
            let coeff3 = (n1 as nat) * l2 + (n2 as nat) * l1 + (n3 as nat) * l0_val;
            let coeff4 = (n0 as nat) * l4 + (n2 as nat) * l2 + (n3 as nat) * l1 + (n4 as nat) * l0_val;
            let nl_low_coeffs = coeff0 + coeff1 * pow2(52) + coeff2 * pow2(104) 
                + coeff3 * pow2(156) + coeff4 * pow2(208);
            t_low + nl_low_coeffs == (carry4 as nat) * pow2(260)
        }),
        
        // Sum definitions (how part2 inputs are computed)
        sum5 as nat == carry4 as nat + limbs[5] as nat 
            + (n1 as nat) * (constants::L.limbs[4] as nat)
            + (n3 as nat) * (constants::L.limbs[2] as nat)
            + (n4 as nat) * (constants::L.limbs[1] as nat),
        sum6 as nat == carry5 as nat + limbs[6] as nat 
            + (n2 as nat) * (constants::L.limbs[4] as nat)
            + (n4 as nat) * (constants::L.limbs[2] as nat),
        sum7 as nat == carry6 as nat + limbs[7] as nat 
            + (n3 as nat) * (constants::L.limbs[4] as nat),
        sum8 as nat == carry7 as nat + limbs[8] as nat 
            + (n4 as nat) * (constants::L.limbs[4] as nat),
        
        // Part2 stage equations
        sum5 as nat == (r0 as nat) + (carry5 as nat) * pow2(52),
        sum6 as nat == (r1 as nat) + (carry6 as nat) * pow2(52),
        sum7 as nat == (r2 as nat) + (carry7 as nat) * pow2(52),
        sum8 as nat == (r3 as nat) + (r4 as nat) * pow2(52),
        
        // r bounds from part2 postconditions
        r0 < pow2(52), r1 < pow2(52), r2 < pow2(52), r3 < pow2(52),
    ensures
        ({
            let n = super::montgomery_reduce_part1_chain_lemmas::five_u64_limbs_to_nat(n0, n1, n2, n3, n4);
            let t = slice128_to_nat(limbs);
            let l = group_order();
            let intermediate = five_u64_limbs_to_nat(r0, r1, r2, r3, r4);
            // The key result: intermediate is the exact quotient
            intermediate * pow2(260) + 0 == t + n * l
            // Equivalently: intermediate == (t + n * l) / pow2(260)
        }),
{
    // =========================================================================
    // Step 1: Prove intermediate = carry4 + t_high + nl_high via carry cancellation
    // =========================================================================
    //
    // Key insight: When we expand intermediate using stage equations and then
    // substitute sum definitions, the intermediate carries (carry5, carry6, carry7)
    // cancel out completely, leaving:
    //   intermediate = carry4 + t_high + nl_high
    //
    // Proof outline:
    //   intermediate = r0 + r1*2^52 + r2*2^104 + r3*2^156 + r4*2^208
    //
    //   From stage equations:
    //     r0 = sum5 - carry5*2^52
    //     r1 = sum6 - carry6*2^52
    //     r2 = sum7 - carry7*2^52
    //     r3 = sum8 - r4*2^52
    //
    //   Substituting:
    //   = (sum5 - carry5*2^52) + (sum6 - carry6*2^52)*2^52 + ...
    //   = sum5 - carry5*2^52 + sum6*2^52 - carry6*2^104 + sum7*2^104 - carry7*2^156 
    //     + sum8*2^156 - r4*2^208 + r4*2^208
    //
    //   Now substitute sum definitions (carry chaining: sum6 = carry5 + T[6] + ...):
    //   = (carry4 + T[5] + prod5) - carry5*2^52
    //   + (carry5 + T[6] + prod6)*2^52 - carry6*2^104
    //   + (carry6 + T[7] + prod7)*2^104 - carry7*2^156
    //   + (carry7 + T[8] + prod8)*2^156
    //
    //   After expansion, ALL intermediate carries cancel:
    //     -carry5*2^52 + carry5*2^52 = 0
    //     -carry6*2^104 + carry6*2^104 = 0  
    //     -carry7*2^156 + carry7*2^156 = 0
    //
    //   Result: intermediate = carry4 + t_high + nl_high
    
    let intermediate = five_u64_limbs_to_nat(r0, r1, r2, r3, r4);
    
    // =========================================================================
    // Step 2: Establish intermediate = carry4 + t_high + nl_high
    // =========================================================================
    //
    // From Step 1's carry cancellation analysis, we have:
    //   intermediate = carry4 + t_high + nl_high
    //
    // where:
    // - t_high = T[5] + T[6]*2^52 + T[7]*2^104 + T[8]*2^156
    // - nl_high = (N×L products at positions 5-8)
    //
    // This is the key connection to the quotient relationship.
    
    let n = super::montgomery_reduce_part1_chain_lemmas::five_u64_limbs_to_nat(n0, n1, n2, n3, n4);
    let t = slice128_to_nat(limbs);
    let l = group_order();
    
    // Define the components
    let t_low = limbs[0] as nat 
        + limbs[1] as nat * pow2(52) 
        + limbs[2] as nat * pow2(104) 
        + limbs[3] as nat * pow2(156) 
        + limbs[4] as nat * pow2(208);
    let t_high = limbs[5] as nat 
        + limbs[6] as nat * pow2(52) 
        + limbs[7] as nat * pow2(104) 
        + limbs[8] as nat * pow2(156);
    
    // N×L polynomial decomposition
    // N×L splits into: low part (positions 0-4) and high part (positions 5-8)
    let nl_high = nl_high_contribution(n0, n1, n2, n3, n4);
    
    // nl_low_coeffs: The polynomial coefficients of N×L at positions 0-4
    // These are the cross-products n_i × L_j where i+j < 5
    let l0_val = constants::L.limbs[0] as nat;
    let l1 = constants::L.limbs[1] as nat;
    let l2 = constants::L.limbs[2] as nat;
    // L[3] = 0
    let l4 = constants::L.limbs[4] as nat;
    
    let coeff0 = (n0 as nat) * l0_val;
    let coeff1 = (n0 as nat) * l1 + (n1 as nat) * l0_val;
    let coeff2 = (n0 as nat) * l2 + (n1 as nat) * l1 + (n2 as nat) * l0_val;
    let coeff3 = (n1 as nat) * l2 + (n2 as nat) * l1 + (n3 as nat) * l0_val;  // L[3]=0
    let coeff4 = (n0 as nat) * l4 + (n2 as nat) * l2 + (n3 as nat) * l1 + (n4 as nat) * l0_val;
    
    let nl_low_coeffs = coeff0 + coeff1 * pow2(52) + coeff2 * pow2(104) 
        + coeff3 * pow2(156) + coeff4 * pow2(208);
    
    // =========================================================================
    // The Quotient Connection: T + N×L = intermediate × 2^260
    // =========================================================================
    //
    // Proof structure:
    //
    // 1. T decomposes: T = T_low + T_high × 2^260
    //
    // 2. N×L decomposes: N×L = (N×L)_low + (N×L)_high × 2^260
    //    where (N×L)_low = n * l_low (mod 2^260) and (N×L)_high = nl_high
    //
    // 3. Part 1 zeroed the low part: (T_low + N×L_low) = carry4 × 2^260
    //    (No remainder - exactly divisible because Part 1 chose N to make this happen)
    //
    // 4. Step 1 showed: intermediate = carry4 + T_high + nl_high
    //
    // 5. Combining:
    //    T + N×L = T_low + T_high × 2^260 + (N×L)_low + nl_high × 2^260
    //            = (T_low + n * l_low) + (T_high + nl_high) × 2^260
    //            = carry4 × 2^260 + (T_high + nl_high) × 2^260        [from Part 1]
    //            = (carry4 + T_high + nl_high) × 2^260                [factor out]
    //            = intermediate × 2^260                               [from Step 1]
    
    // =========================================================================
    // Prove Assumption 1: T decomposes into t_low + t_high × 2^260
    // =========================================================================
    //
    // slice128_to_nat(limbs) = limbs[0] + limbs[1]*2^52 + ... + limbs[8]*2^416
    //
    // t_low = limbs[0] + limbs[1]*2^52 + limbs[2]*2^104 + limbs[3]*2^156 + limbs[4]*2^208
    // t_high = limbs[5] + limbs[6]*2^52 + limbs[7]*2^104 + limbs[8]*2^156
    //
    // t_high * 2^260 = limbs[5]*2^260 + limbs[6]*2^312 + limbs[7]*2^364 + limbs[8]*2^416
    //
    // t = t_low + t_high * 2^260
    
    // Step 1: Get t in polynomial form
    super::super::scalar_lemmas::lemma_nine_limbs_equals_slice128_to_nat(limbs);
    // Now: t == nine_limbs_to_nat_aux(limbs) 
    //        == limbs[0] + limbs[1]*2^52 + ... + limbs[8]*2^416
    
    // Step 2: Factor out pow2(260) from high terms
    // t_high * 2^260 = (limbs[5] + limbs[6]*2^52 + limbs[7]*2^104 + limbs[8]*2^156) * 2^260
    //               = limbs[5]*2^260 + limbs[6]*2^52*2^260 + limbs[7]*2^104*2^260 + limbs[8]*2^156*2^260
    //               = limbs[5]*2^260 + limbs[6]*2^312 + limbs[7]*2^364 + limbs[8]*2^416
    
    // Power relationships
    lemma_pow2_adds(52, 260);   // pow2(312) = pow2(52) * pow2(260)
    lemma_pow2_adds(104, 260);  // pow2(364) = pow2(104) * pow2(260)
    lemma_pow2_adds(156, 260);  // pow2(416) = pow2(156) * pow2(260)
    
    // Distributivity: (a + b + c + d) * e = a*e + b*e + c*e + d*e
    assert(t_high * pow2(260) == (limbs[5] as nat) * pow2(260) + (limbs[6] as nat) * pow2(312) 
        + (limbs[7] as nat) * pow2(364) + (limbs[8] as nat) * pow2(416)) by {
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, (limbs[5] as nat) as int, 
            ((limbs[6] as nat) * pow2(52) + (limbs[7] as nat) * pow2(104) + (limbs[8] as nat) * pow2(156)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, ((limbs[6] as nat) * pow2(52)) as int,
            ((limbs[7] as nat) * pow2(104) + (limbs[8] as nat) * pow2(156)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, ((limbs[7] as nat) * pow2(104)) as int,
            ((limbs[8] as nat) * pow2(156)) as int);
        // Connect each term: limbs[i] * pow2(k) * pow2(260) = limbs[i] * pow2(k+260)
        assert((limbs[6] as nat) * pow2(52) * pow2(260) == (limbs[6] as nat) * pow2(312)) by {
            lemma_mul_is_associative((limbs[6] as nat) as int, pow2(52) as int, pow2(260) as int);
        };
        assert((limbs[7] as nat) * pow2(104) * pow2(260) == (limbs[7] as nat) * pow2(364)) by {
            lemma_mul_is_associative((limbs[7] as nat) as int, pow2(104) as int, pow2(260) as int);
        };
        assert((limbs[8] as nat) * pow2(156) * pow2(260) == (limbs[8] as nat) * pow2(416)) by {
            lemma_mul_is_associative((limbs[8] as nat) as int, pow2(156) as int, pow2(260) as int);
        };
    };
    
    // Now: t_low + t_high * pow2(260) = (limbs[0..4] polynomial) + (limbs[5..8] * pow2(260))
    //                                = full 9-limb polynomial = t
    assert(t == t_low + t_high * pow2(260));
    
    // Fact 2: Part 1 telescoping gives t_low + nl_low_coeffs = carry4 × 2^260
    //
    // This is now a precondition, provided by Part 1's enhanced ensures clause.
    // lemma_part1_chain_divisibility ensures this quotient relationship.
    assert(t_low + nl_low_coeffs == (carry4 as nat) * pow2(260));  // From precondition
    
    // =========================================================================
    // Prove Assumption 3: intermediate = carry4 + t_high + nl_high
    // =========================================================================
    //
    // This is the carry cancellation proof. We expand intermediate using
    // stage equations and sum definitions, showing carries cancel.
    
    // Step 3a: Express r_i in terms of sums and carries (from stage equations)
    // r0 = sum5 - carry5 * 2^52
    // r1 = sum6 - carry6 * 2^52  
    // r2 = sum7 - carry7 * 2^52
    // r3 = sum8 - r4 * 2^52
    assert((r0 as nat) == (sum5 as nat) - (carry5 as nat) * pow2(52));
    assert((r1 as nat) == (sum6 as nat) - (carry6 as nat) * pow2(52));
    assert((r2 as nat) == (sum7 as nat) - (carry7 as nat) * pow2(52));
    assert((r3 as nat) == (sum8 as nat) - (r4 as nat) * pow2(52));
    
    // Step 3b: Define products at each position (from sum definitions)
    let products5 = (n1 as nat) * (constants::L.limbs[4] as nat)
        + (n3 as nat) * (constants::L.limbs[2] as nat)
        + (n4 as nat) * (constants::L.limbs[1] as nat);
    let products6 = (n2 as nat) * (constants::L.limbs[4] as nat)
        + (n4 as nat) * (constants::L.limbs[2] as nat);
    let products7 = (n3 as nat) * (constants::L.limbs[4] as nat);
    let products8 = (n4 as nat) * (constants::L.limbs[4] as nat);
    
    // Verify nl_high matches weighted products
    assert(nl_high == products5 + products6 * pow2(52) + products7 * pow2(104) + products8 * pow2(156));
    
    // Step 3c: The key algebraic expansion
    // intermediate = r0 + r1*2^52 + r2*2^104 + r3*2^156 + r4*2^208
    //
    // Substituting r_i = sum_{i+5} - carry_{i+5}*2^52:
    // = (sum5 - carry5*2^52) + (sum6 - carry6*2^52)*2^52 + (sum7 - carry7*2^52)*2^104 
    //   + (sum8 - r4*2^52)*2^156 + r4*2^208
    //
    // After expansion, -r4*2^208 + r4*2^208 cancels, leaving:
    // = sum5 - carry5*2^52 + sum6*2^52 - carry6*2^104 + sum7*2^104 - carry7*2^156 + sum8*2^156
    //
    // Substituting sum definitions (sum6 = carry5 + limbs[6] + products6, etc.):
    // The carry terms cancel: -carry5*2^52 + carry5*2^52 = 0, etc.
    //
    // Result: carry4 + t_high + nl_high
    
    // Power-of-2 relationships for distributivity
    lemma_pow2_adds(52, 52);   // pow2(104)
    lemma_pow2_adds(52, 104);  // pow2(156)  
    lemma_pow2_adds(52, 156);  // pow2(208)
    
    // Step 3d: Expand intermediate step by step
    // First, we know intermediate = r0 + r1*2^52 + r2*2^104 + r3*2^156 + r4*2^208
    
    // Define a helper: sum of sums with cancellation terms
    // sum5 + sum6*2^52 - carry5*2^52 + sum7*2^104 - carry6*2^104 + sum8*2^156 - carry7*2^156
    // = sum5 - carry5*2^52 + (sum6 - carry6*2^52)*2^52 + (sum7 - carry7*2^52)*2^104 + sum8*2^156
    // But wait, that's not quite right for r3...
    //
    // Let's be more careful. From stage equations:
    // r3 = sum8 - r4*2^52
    // So r3*2^156 + r4*2^208 = (sum8 - r4*2^52)*2^156 + r4*2^208
    //                        = sum8*2^156 - r4*2^208 + r4*2^208 = sum8*2^156
    
    // The key expansion:
    // intermediate = r0 + r1*2^52 + r2*2^104 + r3*2^156 + r4*2^208
    //              = (sum5 - carry5*2^52) + (sum6 - carry6*2^52)*2^52 
    //                + (sum7 - carry7*2^52)*2^104 + (sum8 - r4*2^52)*2^156 + r4*2^208
    //
    // Note: (sum8 - r4*2^52)*2^156 + r4*2^208 = sum8*2^156 - r4*2^208 + r4*2^208 = sum8*2^156
    
    // Now substitute sum definitions:
    // sum5 = carry4 + limbs[5] + products5
    // sum6 = carry5 + limbs[6] + products6
    // sum7 = carry6 + limbs[7] + products7  
    // sum8 = carry7 + limbs[8] + products8
    //
    // After substitution:
    // = (carry4 + limbs[5] + products5) - carry5*2^52
    //   + (carry5 + limbs[6] + products6)*2^52 - carry6*2^104
    //   + (carry6 + limbs[7] + products7)*2^104 - carry7*2^156
    //   + (carry7 + limbs[8] + products8)*2^156
    //
    // Expanding the multiplications:
    // = carry4 + limbs[5] + products5 - carry5*2^52
    //   + carry5*2^52 + limbs[6]*2^52 + products6*2^52 - carry6*2^104
    //   + carry6*2^104 + limbs[7]*2^104 + products7*2^104 - carry7*2^156
    //   + carry7*2^156 + limbs[8]*2^156 + products8*2^156
    //
    // Carries cancel: -carry5*2^52 + carry5*2^52 = 0, etc.
    //
    // Result: carry4 + t_high + nl_high
    
    // For Z3, let's prove this by computing both sides
    // LHS: intermediate (already defined as five_u64_limbs_to_nat)
    // RHS: carry4 + t_high + nl_high
    
    // The explicit algebra using distributivity
    // We'll compute the expanded form and show it equals carry4 + t_high + nl_high
    let expanded = (sum5 as nat) - (carry5 as nat) * pow2(52)
        + ((sum6 as nat) - (carry6 as nat) * pow2(52)) * pow2(52)
        + ((sum7 as nat) - (carry7 as nat) * pow2(52)) * pow2(104)
        + (sum8 as nat) * pow2(156);  // Note: r3*2^156 + r4*2^208 = sum8*2^156
    
    // Show the last part: r3*2^156 + r4*2^208 = sum8*2^156
    assert((r3 as nat) * pow2(156) + (r4 as nat) * pow2(208) == (sum8 as nat) * pow2(156)) by {
        // r3 = sum8 - r4*2^52
        // r3*2^156 = (sum8 - r4*2^52)*2^156 = sum8*2^156 - r4*2^52*2^156
        // r3*2^156 + r4*2^208 = sum8*2^156 - r4*2^208 + r4*2^208 = sum8*2^156
        lemma_mul_is_distributive_sub_other_way(pow2(156) as int, (sum8 as nat) as int, ((r4 as nat) * pow2(52)) as int);
        assert((r4 as nat) * pow2(52) * pow2(156) == (r4 as nat) * pow2(208)) by {
            lemma_mul_is_associative((r4 as nat) as int, pow2(52) as int, pow2(156) as int);
        }
    };
    
    // Show intermediate equals the expanded form
    assert(intermediate == expanded) by {
        // This is just substituting r_i = sum_{i+5} - carry_{i+5}*2^52
        // Plus the simplification for r3/r4
        lemma_mul_is_distributive_sub_other_way(pow2(52) as int, (sum6 as nat) as int, ((carry6 as nat) * pow2(52)) as int);
        lemma_mul_is_distributive_sub_other_way(pow2(104) as int, (sum7 as nat) as int, ((carry7 as nat) * pow2(52)) as int);
        assert((carry6 as nat) * pow2(52) * pow2(52) == (carry6 as nat) * pow2(104)) by {
            lemma_mul_is_associative((carry6 as nat) as int, pow2(52) as int, pow2(52) as int);
        }
        assert((carry7 as nat) * pow2(52) * pow2(104) == (carry7 as nat) * pow2(156)) by {
            lemma_mul_is_associative((carry7 as nat) as int, pow2(52) as int, pow2(104) as int);
        }
    };
    
    // Now show expanded equals carry4 + t_high + nl_high via carry cancellation
    // 
    // expanded = sum5 - carry5*2^52 + (sum6 - carry6*2^52)*2^52 + (sum7 - carry7*2^52)*2^104 + sum8*2^156
    //
    // Substituting sum definitions:
    // sum5 = carry4 + limbs[5] + products5
    // sum6 = carry5 + limbs[6] + products6  
    // sum7 = carry6 + limbs[7] + products7
    // sum8 = carry7 + limbs[8] + products8
    //
    // After substitution and expansion, carries cancel algebraically.
    
    // Define the "base" values (without carries)
    let base5 = (limbs[5] as nat) + products5;
    let base6 = (limbs[6] as nat) + products6;
    let base7 = (limbs[7] as nat) + products7;
    let base8 = (limbs[8] as nat) + products8;
    
    // The sum definitions can be rewritten as:
    // sum5 = carry4 + base5
    // sum6 = carry5 + base6
    // sum7 = carry6 + base7
    // sum8 = carry7 + base8
    assert((sum5 as nat) == (carry4 as nat) + base5);
    assert((sum6 as nat) == (carry5 as nat) + base6);
    assert((sum7 as nat) == (carry6 as nat) + base7);
    assert((sum8 as nat) == (carry7 as nat) + base8);
    
    // The target: carry4 + t_high + nl_high
    let target = (carry4 as nat) + t_high + nl_high;
    
    // Rewrite t_high using base values
    assert(t_high == (limbs[5] as nat) + (limbs[6] as nat) * pow2(52) 
        + (limbs[7] as nat) * pow2(104) + (limbs[8] as nat) * pow2(156));
    
    // Rewrite nl_high using products
    assert(nl_high == products5 + products6 * pow2(52) + products7 * pow2(104) + products8 * pow2(156));
    
    // So target = carry4 + limbs[5] + limbs[6]*2^52 + limbs[7]*2^104 + limbs[8]*2^156
    //           + products5 + products6*2^52 + products7*2^104 + products8*2^156
    //           = carry4 + base5 + base6*2^52 + base7*2^104 + base8*2^156
    //           = carry4 + (limbs[5] + products5) + (limbs[6] + products6)*2^52 + ...
    
    // Now expand `expanded` using sum definitions:
    // expanded = (carry4 + base5) - carry5*2^52 
    //          + ((carry5 + base6) - carry6*2^52)*2^52 
    //          + ((carry6 + base7) - carry7*2^52)*2^104 
    //          + (carry7 + base8)*2^156
    //
    // = carry4 + base5 - carry5*2^52
    //   + (carry5 + base6)*2^52 - carry6*2^104
    //   + (carry6 + base7)*2^104 - carry7*2^156
    //   + (carry7 + base8)*2^156
    //
    // = carry4 + base5 - carry5*2^52
    //   + carry5*2^52 + base6*2^52 - carry6*2^104
    //   + carry6*2^104 + base7*2^104 - carry7*2^156  
    //   + carry7*2^156 + base8*2^156
    //
    // Carries cancel: (-carry5*2^52 + carry5*2^52) = 0, etc.
    //
    // = carry4 + base5 + base6*2^52 + base7*2^104 + base8*2^156
    // = target ✓
    
    // The cancellation algebra - step by step
    // 
    // expanded = (sum5 - carry5*2^52) + (sum6 - carry6*2^52)*2^52 
    //          + (sum7 - carry7*2^52)*2^104 + sum8*2^156
    //
    // Using sum definitions:
    // = (carry4 + base5 - carry5*2^52) 
    //   + ((carry5 + base6) - carry6*2^52)*2^52 
    //   + ((carry6 + base7) - carry7*2^52)*2^104 
    //   + (carry7 + base8)*2^156
    
    // Step 1: Rewrite sum5 term
    let term5 = (carry4 as nat) + base5 - (carry5 as nat) * pow2(52);
    assert((sum5 as nat) - (carry5 as nat) * pow2(52) == term5);
    
    // Step 2: Expand (sum6 - carry6*2^52)*2^52
    // = ((carry5 + base6) - carry6*2^52)*2^52
    // = (carry5 + base6)*2^52 - carry6*2^104
    // = carry5*2^52 + base6*2^52 - carry6*2^104
    lemma_mul_is_distributive_sub_other_way(pow2(52) as int, ((carry5 as nat) + base6) as int, ((carry6 as nat) * pow2(52)) as int);
    lemma_mul_is_distributive_add(pow2(52) as int, (carry5 as nat) as int, base6 as int);
    assert(((carry6 as nat) * pow2(52)) * pow2(52) == (carry6 as nat) * pow2(104)) by {
        lemma_mul_is_associative((carry6 as nat) as int, pow2(52) as int, pow2(52) as int);
    };
    let term6 = (carry5 as nat) * pow2(52) + base6 * pow2(52) - (carry6 as nat) * pow2(104);
    assert(((sum6 as nat) - (carry6 as nat) * pow2(52)) * pow2(52) == term6);
    
    // Step 3: Expand (sum7 - carry7*2^52)*2^104
    // = ((carry6 + base7) - carry7*2^52)*2^104
    // = carry6*2^104 + base7*2^104 - carry7*2^156
    lemma_mul_is_distributive_sub_other_way(pow2(104) as int, ((carry6 as nat) + base7) as int, ((carry7 as nat) * pow2(52)) as int);
    lemma_mul_is_distributive_add(pow2(104) as int, (carry6 as nat) as int, base7 as int);
    assert(((carry7 as nat) * pow2(52)) * pow2(104) == (carry7 as nat) * pow2(156)) by {
        lemma_mul_is_associative((carry7 as nat) as int, pow2(52) as int, pow2(104) as int);
    };
    let term7 = (carry6 as nat) * pow2(104) + base7 * pow2(104) - (carry7 as nat) * pow2(156);
    assert(((sum7 as nat) - (carry7 as nat) * pow2(52)) * pow2(104) == term7);
    
    // Step 4: Expand sum8*2^156
    // = (carry7 + base8)*2^156
    // = carry7*2^156 + base8*2^156
    let term8 = (carry7 as nat) * pow2(156) + base8 * pow2(156);
    assert((sum8 as nat) * pow2(156) == term8) by {
        // (carry7 + base8) * pow2(156) == carry7 * pow2(156) + base8 * pow2(156)
        lemma_mul_is_distributive_add_other_way(pow2(156) as int, (carry7 as nat) as int, base8 as int);
    };
    
    // Step 5: Sum all terms and watch carries cancel
    // term5 + term6 + term7 + term8
    // = (carry4 + base5 - carry5*2^52)
    //   + (carry5*2^52 + base6*2^52 - carry6*2^104)
    //   + (carry6*2^104 + base7*2^104 - carry7*2^156)
    //   + (carry7*2^156 + base8*2^156)
    //
    // Grouping: 
    // = carry4 + base5 + base6*2^52 + base7*2^104 + base8*2^156
    //   + (-carry5*2^52 + carry5*2^52)  // cancels
    //   + (-carry6*2^104 + carry6*2^104)  // cancels
    //   + (-carry7*2^156 + carry7*2^156)  // cancels
    // = carry4 + base5 + base6*2^52 + base7*2^104 + base8*2^156
    // = target
    
    // Assert the cancellation explicitly
    let carry5_term = (carry5 as nat) * pow2(52);
    let carry6_term = (carry6 as nat) * pow2(104);
    let carry7_term = (carry7 as nat) * pow2(156);
    
    // expanded = term5 + term6 + term7 + term8
    assert(expanded == term5 + term6 + term7 + term8);
    
    // After cancellation
    let cancelled = (carry4 as nat) + base5 + base6 * pow2(52) + base7 * pow2(104) + base8 * pow2(156);
    assert(term5 + term6 + term7 + term8 == cancelled);
    
    // cancelled == target
    // cancelled = carry4 + base5 + base6*2^52 + base7*2^104 + base8*2^156
    // target = carry4 + t_high + nl_high
    //        = carry4 + (limbs[5] + limbs[6]*2^52 + limbs[7]*2^104 + limbs[8]*2^156)
    //                 + (products5 + products6*2^52 + products7*2^104 + products8*2^156)
    //
    // Expanding base_i = limbs[i] + products_i:
    // base6*2^52 = (limbs[6] + products6)*2^52 = limbs[6]*2^52 + products6*2^52
    // Similarly for base7, base8
    
    // Expand base terms using distributivity: (a + b) * c == a * c + b * c
    assert(base6 * pow2(52) == (limbs[6] as nat) * pow2(52) + products6 * pow2(52)) by {
        lemma_mul_is_distributive_add_other_way(pow2(52) as int, (limbs[6] as nat) as int, products6 as int);
    };
    assert(base7 * pow2(104) == (limbs[7] as nat) * pow2(104) + products7 * pow2(104)) by {
        lemma_mul_is_distributive_add_other_way(pow2(104) as int, (limbs[7] as nat) as int, products7 as int);
    };
    assert(base8 * pow2(156) == (limbs[8] as nat) * pow2(156) + products8 * pow2(156)) by {
        lemma_mul_is_distributive_add_other_way(pow2(156) as int, (limbs[8] as nat) as int, products8 as int);
    };
    
    // Now cancelled = carry4 + base5 + base6*2^52 + base7*2^104 + base8*2^156
    //               = carry4 + (limbs[5] + products5) 
    //                       + (limbs[6]*2^52 + products6*2^52) 
    //                       + (limbs[7]*2^104 + products7*2^104) 
    //                       + (limbs[8]*2^156 + products8*2^156)
    //               = carry4 + limbs[5] + limbs[6]*2^52 + limbs[7]*2^104 + limbs[8]*2^156
    //                       + products5 + products6*2^52 + products7*2^104 + products8*2^156
    //               = carry4 + t_high + nl_high = target
    
    assert(cancelled == target);
    
    // Therefore intermediate == target
    assert(intermediate == target);
    
    // =========================================================================
    // Prove Assumption 4: N×L decomposes: n * l = nl_low_coeffs + nl_high × 2^260
    // =========================================================================
    //
    // Polynomial multiplication of N (5 limbs) × L (5 limbs) gives 9 limbs.
    // Collecting by position k = i+j:
    //   Position 0: n0×l0
    //   Position 1: n0×l1 + n1×l0
    //   Position 2: n0×l2 + n1×l1 + n2×l0
    //   Position 3: n1×l2 + n2×l1 + n3×l0  (l3=0)
    //   Position 4: n0×l4 + n2×l2 + n3×l1 + n4×l0  (l3=0)
    //   Position 5: n1×l4 + n3×l2 + n4×l1
    //   Position 6: n2×l4 + n4×l2
    //   Position 7: n3×l4
    //   Position 8: n4×l4
    //
    // - Positions 0-4 contribute nl_low_coeffs
    // - Positions 5-8 contribute nl_high × 2^260
    
    // Define high-position coefficients (positions 5-8)
    let coeff5 = (n1 as nat) * l4 + (n3 as nat) * l2 + (n4 as nat) * l1;
    let coeff6 = (n2 as nat) * l4 + (n4 as nat) * l2;
    let coeff7 = (n3 as nat) * l4;
    let coeff8 = (n4 as nat) * l4;
    
    // Verify nl_high matches our coefficients
    assert(nl_high == coeff5 + coeff6 * pow2(52) + coeff7 * pow2(104) + coeff8 * pow2(156));
    
    // high_part = coefficients at positions 5-8 weighted by their positions
    let high_part = coeff5 * pow2(260) + coeff6 * pow2(312) + coeff7 * pow2(364) + coeff8 * pow2(416);
    
    // Power relationships for high positions
    lemma_pow2_adds(52, 260);   // 2^312
    lemma_pow2_adds(104, 260);  // 2^364
    lemma_pow2_adds(156, 260);  // 2^416
    
    // Factor pow2(260) from high_part: high_part = nl_high × 2^260
    assert(high_part == nl_high * pow2(260)) by {
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, coeff5 as int, 
            (coeff6 * pow2(52) + coeff7 * pow2(104) + coeff8 * pow2(156)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, (coeff6 * pow2(52)) as int,
            (coeff7 * pow2(104) + coeff8 * pow2(156)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, (coeff7 * pow2(104)) as int,
            (coeff8 * pow2(156)) as int);
        // Connect: coeff_i * pow2(52*i) * pow2(260) = coeff_i * pow2(260 + 52*i)
        assert(coeff6 * pow2(52) * pow2(260) == coeff6 * pow2(312)) by {
            lemma_mul_is_associative(coeff6 as int, pow2(52) as int, pow2(260) as int);
        };
        assert(coeff7 * pow2(104) * pow2(260) == coeff7 * pow2(364)) by {
            lemma_mul_is_associative(coeff7 as int, pow2(104) as int, pow2(260) as int);
        };
        assert(coeff8 * pow2(156) * pow2(260) == coeff8 * pow2(416)) by {
            lemma_mul_is_associative(coeff8 as int, pow2(156) as int, pow2(260) as int);
        };
    };
    
    // Main polynomial multiplication: n * l = nl_low_coeffs + high_part
    //
    // We need to prove that N × L decomposes into low and high parts.
    // N = n0 + n1*2^52 + n2*2^104 + n3*2^156 + n4*2^208
    // L = l0 + l1*2^52 + l2*2^104 + l3*2^156 + l4*2^208  (where l3 = 0)
    //
    // Use the helper lemma to connect group_order() to the limb polynomial.
    lemma_group_order_equals_l_poly();
    
    let l_poly = l0_val + l1 * pow2(52) + l2 * pow2(104) + 0 * pow2(156) + l4 * pow2(208);
    
    // l == group_order() == l_poly (since L[3] = 0, the l3 term vanishes)
    assert(l == l_poly);
    
    // Call the general 5×5 polynomial decomposition lemma from Part 1.
    // This lemma proves: a * b == low_coeffs + high_coeffs * pow2(260)
    super::montgomery_reduce_part1_chain_lemmas::lemma_poly_mul_5x5_decomposition(
        n0 as nat, n1 as nat, n2 as nat, n3 as nat, n4 as nat,
        l0_val, l1, l2, 0,  // L[3] = 0
        l4,
    );
    
    // The general lemma proves for the polynomial forms:
    //   n_poly * l_poly == gen_low + gen_high * pow2(260)
    // where:
    //   n_poly = n0 + n1*2^52 + n2*2^104 + n3*2^156 + n4*2^208
    //   l_poly = l0 + l1*2^52 + l2*2^104 + 0 + l4*2^208
    
    let n_poly = (n0 as nat) + (n1 as nat) * pow2(52) + (n2 as nat) * pow2(104) 
        + (n3 as nat) * pow2(156) + (n4 as nat) * pow2(208);
    
    // n == n_poly by definition of five_u64_limbs_to_nat
    assert(n == n_poly);
    
    // l == l_poly (asserted above)
    // So n * l == n_poly * l_poly == gen_low + gen_high * pow2(260)
    
    let l3 = 0nat;  // L[3] = 0
    
    let gen_c0 = (n0 as nat) * l0_val;
    let gen_c1 = (n0 as nat) * l1 + (n1 as nat) * l0_val;
    let gen_c2 = (n0 as nat) * l2 + (n1 as nat) * l1 + (n2 as nat) * l0_val;
    let gen_c3 = (n0 as nat) * l3 + (n1 as nat) * l2 + (n2 as nat) * l1 + (n3 as nat) * l0_val;
    let gen_c4 = (n0 as nat) * l4 + (n1 as nat) * l3 + (n2 as nat) * l2 + (n3 as nat) * l1 + (n4 as nat) * l0_val;
    let gen_c5 = (n1 as nat) * l4 + (n2 as nat) * l3 + (n3 as nat) * l2 + (n4 as nat) * l1;
    let gen_c6 = (n2 as nat) * l4 + (n3 as nat) * l3 + (n4 as nat) * l2;
    let gen_c7 = (n3 as nat) * l4 + (n4 as nat) * l3;
    let gen_c8 = (n4 as nat) * l4;
    
    let gen_low = gen_c0 + gen_c1 * pow2(52) + gen_c2 * pow2(104) + gen_c3 * pow2(156) + gen_c4 * pow2(208);
    let gen_high = gen_c5 + gen_c6 * pow2(52) + gen_c7 * pow2(104) + gen_c8 * pow2(156);
    
    // Since l3 = 0, the terms n0*l3, n1*l3, etc. vanish:
    assert(gen_c0 == coeff0);
    assert(gen_c1 == coeff1);
    assert(gen_c2 == coeff2);
    assert(gen_c3 == coeff3);  // n0*0 + n1*l2 + n2*l1 + n3*l0 = coeff3
    assert(gen_c4 == coeff4);  // n0*l4 + n1*0 + n2*l2 + n3*l1 + n4*l0 = coeff4
    assert(gen_c5 == coeff5);
    assert(gen_c6 == coeff6);
    assert(gen_c7 == coeff7);
    assert(gen_c8 == coeff8);
    
    assert(gen_low == nl_low_coeffs);
    assert(gen_high == nl_high);
    
    // The general lemma proves: n_poly * l_poly == gen_low + gen_high * pow2(260)
    // Since n == n_poly, l == l_poly, gen_low == nl_low_coeffs, gen_high == nl_high:
    assert(n * l == nl_low_coeffs + nl_high * pow2(260));
    
    // Also verify high_part == nl_high * pow2(260):
    assert(n * l == nl_low_coeffs + high_part);
    
    // Combine: n * l = nl_low_coeffs + nl_high × 2^260
    assert(n * l == nl_low_coeffs + nl_high * pow2(260));
    
    // =========================================================================
    // Prove Assumption 5: Algebraic chain to postcondition
    // =========================================================================
    //
    // From Assumptions 1, 2, 4:
    //   T + N×L = (t_low + t_high × 2^260) + (nl_low_coeffs + nl_high × 2^260)
    //           = (t_low + nl_low_coeffs) + (t_high + nl_high) × 2^260
    //           = carry4 × 2^260 + (t_high + nl_high) × 2^260        [Assumption 2]
    //           = (carry4 + t_high + nl_high) × 2^260
    //           = intermediate × 2^260                               [carry cancellation]
    
    // Step 5a: Expand t + n*l using decompositions
    // t + n*l = (t_low + t_high * pow2(260)) + (nl_low_coeffs + nl_high * pow2(260))
    //        = (t_low + nl_low_coeffs) + (t_high + nl_high) * pow2(260)
    assert(t + n * l == (t_low + nl_low_coeffs) + (t_high + nl_high) * pow2(260)) by {
        // t == t_low + t_high * pow2(260) (proven above)
        // n * l == nl_low_coeffs + nl_high * pow2(260) (assumed)
        // 
        // t + n*l = t_low + t_high*2^260 + nl_low_coeffs + nl_high*2^260
        //        = (t_low + nl_low_coeffs) + (t_high + nl_high)*2^260
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, t_high as int, nl_high as int);
    };
    
    // Step 5b: Apply Assumption 2: t_low + nl_low_coeffs == carry4 * pow2(260)
    // (t_low + nl_low_coeffs) + (t_high + nl_high) * pow2(260)
    // = carry4 * pow2(260) + (t_high + nl_high) * pow2(260)
    // = (carry4 + t_high + nl_high) * pow2(260)
    assert(t + n * l == ((carry4 as nat) + t_high + nl_high) * pow2(260)) by {
        // Factor pow2(260)
        lemma_mul_is_distributive_add_other_way(pow2(260) as int, (carry4 as nat) as int, (t_high + nl_high) as int);
    };
    
    // Step 5c: Use carry cancellation result: intermediate == carry4 + t_high + nl_high
    // (carry4 + t_high + nl_high) * pow2(260) = intermediate * pow2(260)
    assert(t + n * l == intermediate * pow2(260));
    
    // The postcondition follows directly
    assert(intermediate * pow2(260) + 0 == t + n * l);
    
    // =======================================================================
    // Summary of assumptions to prove (5 total, down from 6):
    // =======================================================================
    //
    // 1. T decomposes: t == t_low + t_high * pow2(260)
    //    - Technique: Unfold slice128_to_nat, use pow2_adds
    //
    // 2. Part 1 overflow: t_low + n * l_low == carry4 * pow2(260)
    //    - Technique: From lemma_part1_chain_divisibility postcondition
    //
    // 3. Carry cancellation: intermediate == carry4 + t_high + nl_high
    //    - Technique: Expand intermediate using stage equations and sum defs
    //    - Key insight: Intermediate carries cancel (Step 1 analysis)
    //
    // 4. N×L decomposition: n * l == n * l_low + nl_high * pow2(260)
    //    - Technique: Polynomial multiplication structure
    //
    // 5. Algebraic chain: t + n * l == intermediate * pow2(260)
    //    - Technique: Combine 1-4 with distributivity lemmas
}

} // verus!
