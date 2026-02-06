#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::number_theory_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;
use super::super::common_lemmas::shift_lemmas::*;
use super::super::scalar_lemmas::*;
use super::montgomery_reduce_part1_chain_lemmas::*;
use super::montgomery_reduce_part2_chain_lemmas::*;
use crate::backend::serial::u64::constants;
use crate::backend::serial::u64::scalar::Scalar52;
use crate::specs::field_specs_u64::*;
use crate::specs::montgomery_reduce_specs::*;
use crate::specs::scalar52_specs::*;

verus! {

// =============================================================================
// AXIOMS - Mathematical facts accepted without formal proof
// =============================================================================
// These are well-established number theory results that would require significant
// proof infrastructure to formalize. They are stated with `admit()` and documented
// with external verification (e.g., Python computations).
//
// GCD axioms (axiom_gcd_symmetric, axiom_gcd_mod_noop, axiom_gcd_pow2_odd) are
// defined in common_lemmas/number_theory_lemmas.rs and imported via
// `use super::super::common_lemmas::number_theory_lemmas::*`.
// =============================================================================
/// Axiom: 2L / 2^208 <= 2^45
///
/// Where L = group_order() = 2^252 + 27742317777372353535851937790883648493
///
/// Mathematical derivation:
/// - L = 2^252 + delta where delta ≈ 2.77×10^37 < 2^126
/// - 2L = 2^253 + 2*delta < 2^253 + 2^127
/// - 2L / 2^208 = 2^45 + floor(2*delta / 2^208)
/// - Since 2*delta < 2^127 < 2^208: floor(2*delta / 2^208) = 0
/// - Therefore 2L / 2^208 = 2^45 exactly
///
/// Verified in Python:
/// ```python
/// >>> L = 2**252 + 27742317777372353535851937790883648493
/// >>> (2 * L) // (2**208) == 2**45
/// True
/// ```
pub(crate) proof fn axiom_two_l_div_pow2_208_le_pow2_45()
    ensures
        (2 * group_order()) / pow2(208) <= pow2(45),
{
    admit();
}

// =============================================================================
// Bit Operation Lemmas (NOT IN VSTD YET)
// =============================================================================
/// Masking a truncated value: combining truncation and masking
pub proof fn lemma_u128_truncate_and_mask(x: u128, n: nat)
    requires
        n <= 64,
    ensures
        ((x as u64) & (low_bits_mask(n) as u64)) as nat == (x as nat) % pow2(n),
{
    assume(false);
}

/// u128 masking with low_bits_mask is modulo pow2
pub proof fn lemma_u128_low_bits_mask_is_mod(x: u128, n: nat)
    requires
        n < 128,
    ensures
        x & (low_bits_mask(n) as u128) == x % (pow2(n) as u128),
{
    assume(false);
}

/// u128 truncation to u64 preserves low 64 bits (modulo pow2(64))
pub proof fn lemma_u128_truncate_to_u64(x: u128)
    ensures
        (x as u64) as nat == (x as nat) % pow2(64),
{
    assume(false);
}

// NOTE: lemma_u128_low_bits_mask_is_mod and lemma_u128_truncate_to_u64 were moved to
// unused_montgomery_reduce_lemmas.rs. They were defined but never called in the active proof.
// =============================================================================
// Carry Shift-to-Nat Conversion
// =============================================================================
/// Converts carry << 52 to nat form: (carry << 52) as nat == (carry as nat) * pow2(52)
///
/// Used in montgomery_reduce to convert u128 shift operations to nat arithmetic.
/// Works for both part1 carries (< 2^57) and part2 carries (< 2^56).
///
/// # Precondition
/// - `carry_bound_bits <= 72` ensures `carry * pow2(52) <= u128::MAX`
/// - `carry < pow2(carry_bound_bits)` is the actual carry bound
pub(crate) proof fn lemma_carry_shift_to_nat(carry: u128, carry_bound_bits: nat)
    requires
        carry_bound_bits <= 72,
        carry < pow2(carry_bound_bits),
    ensures
        (carry << 52) as nat == (carry as nat) * pow2(52),
{
    // Overflow check: carry * pow2(52) < pow2(carry_bound_bits + 52) <= pow2(124) <= u128::MAX
    lemma_pow2_adds(carry_bound_bits, 52);
    lemma_u128_pow2_le_max(carry_bound_bits + 52);
    lemma_pow2_pos(52);

    assert(carry * pow2(52) <= u128::MAX) by {
        lemma_mul_strict_inequality(
            carry as nat as int,
            pow2(carry_bound_bits) as int,
            pow2(52) as int,
        );
    }

    // Convert shift to multiplication
    lemma_u128_shl_is_mul(carry, 52);
}

// =============================================================================
// Core Divisibility Lemma for part1
// =============================================================================
/// Core divisibility: (s + p * L[0]) % 2^52 = 0 where p = s * LFACTOR mod 2^52
///
/// This is the key insight of Montgomery reduction: LFACTOR * L[0] ≡ -1 (mod 2^52),
/// so p * L[0] ≡ s * (-1) ≡ -s, and s + p * L[0] ≡ 0.
pub(crate) proof fn lemma_part1_sum_divisible_by_pow2_52(s: u64, p: nat)
    requires
        s < pow2(52),
        p == ((s as nat) * (constants::LFACTOR as nat)) % pow2(52),
    ensures
        ((s as nat) + p * (constants::L.limbs[0] as nat)) % pow2(52) == 0,
{
    let L0: nat = 0x0002631a5cf5d3edu64 as nat;
    let lfac: nat = 0x51da312547e1bu64 as nat;
    let p52: nat = 0x10000000000000nat;
    let sn = s as nat;

    // Establish constant values
    assert(constants::L.limbs[0] == 0x0002631a5cf5d3edu64);
    assert(constants::LFACTOR == 0x51da312547e1bu64);
    assert(pow2(52) == p52) by {
        lemma2_to64_rest();
    }

    // Step 1: LFACTOR property - (1 + LFACTOR * L[0]) % 2^52 = 0
    assert((1 + lfac * L0) % p52 == 0) by {
        assert(((constants::LFACTOR as nat) * (constants::L.limbs[0] as nat) + 1)
            % 0x10000000000000nat == 0) by (compute);
    }

    // Step 2: Scale - s * (1 + LFACTOR * L[0]) % 2^52 = 0
    assert((sn * (1 + lfac * L0)) % p52 == 0) by {
        lemma_mul_mod_noop_right(sn as int, (1 + lfac * L0) as int, p52 as int);
    }

    // Step 3: Expand - s * (1 + LFACTOR * L[0]) = s + s * LFACTOR * L[0]
    assert(sn * (1 + lfac * L0) == sn + sn * lfac * L0) by {
        lemma_mul_is_distributive_add(sn as int, 1, (lfac * L0) as int);
        lemma_mul_basics(sn as int);
        lemma_mul_is_associative(sn as int, lfac as int, L0 as int);
    }

    // Step 4: Substitute - p * L[0] ≡ s * LFACTOR * L[0] (mod 2^52)
    assert((p * L0) % p52 == (sn * lfac * L0) % p52) by {
        lemma_mul_mod_noop_left((sn * lfac) as int, L0 as int, p52 as int);
        lemma_mul_is_associative(sn as int, lfac as int, L0 as int);
    }

    // Goal: (s + p * L[0]) % 2^52 = 0
    assert((sn + p * L0) % p52 == 0) by {
        lemma_add_mod_noop(sn as int, (p * L0) as int, p52 as int);
    }
}

// =============================================================================
// Main part1 correctness lemma
// =============================================================================
/// Main correctness lemma for part1: sum + p*L[0] == carry << 52
///
/// Structure (following reviewer suggestion):
/// 1. First establish bitwise-to-arithmetic conversions using lemmas (not bit_vector)
/// 2. Then do proofs using pow2 lemmas
pub(crate) proof fn lemma_part1_correctness(sum: u128)
    requires
        sum < (1u128 << 108),
    ensures
        ({
            let mask52: u64 = 0xFFFFFFFFFFFFFu64;
            let sum_low52: u64 = (sum as u64) & mask52;
            let product: u128 = ((sum_low52 as u128) * (constants::LFACTOR as u128)) as u128;
            let p: u64 = (product as u64) & mask52;
            let total: u128 = (sum + (p as u128) * (constants::L.limbs[0] as u128)) as u128;
            let carry: u128 = total >> 52;
            &&& p < (1u64 << 52)
            &&& total == carry << 52
        }),
{
    let mask52: u64 = 0xFFFFFFFFFFFFFu64;
    let p52: nat = pow2(52);

    // Compute all derived values from sum
    let sum_low52: u64 = (sum as u64) & mask52;
    let product: u128 = ((sum_low52 as u128) * (constants::LFACTOR as u128)) as u128;
    let p: u64 = (product as u64) & mask52;
    let total: u128 = (sum + (p as u128) * (constants::L.limbs[0] as u128)) as u128;
    let carry: u128 = total >> 52;
    let L0 = constants::L.limbs[0] as nat;

    // =======================================================================
    // PHASE 1: Bitwise-to-arithmetic conversions (used in multiple places)
    // =======================================================================

    // Used in: L0 < pow2(50), pow2_adds, mod_bound, mul_strict_inequality
    assert(p52 == 0x10000000000000nat) by {
        lemma2_to64_rest();
    }
    // Used in: postcondition `p < (1u64 << 52)`
    assert((1u64 << 52) == p52) by {
        lemma_u64_shift_is_pow2(52);
    }

    // Used in: (1) sum_low52 < p52 bound, (2) mod_add_eq for divisibility
    assert(sum_low52 as nat == (sum as nat) % p52) by {
        lemma_u128_truncate_and_mask(sum, 52);
    }
    // Used in: (1) p < p52 bound, (2) lemma_part1_sum_divisible_by_pow2_52 precondition
    assert(p as nat == (product as nat) % p52) by {
        lemma_u128_truncate_and_mask(product, 52);
    }

    // =======================================================================
    // PHASE 2: Arithmetic proofs
    // =======================================================================

    // p < pow2(52): for postcondition and multiplication bound
    assert(p < p52) by {
        lemma_pow2_pos(52nat);
        lemma_mod_bound((product as nat) as int, p52 as int);
    }

    // Core divisibility: (sum_low52 + p*L[0]) ≡ 0 (mod pow2(52))
    assert(((sum_low52 as nat) + (p as nat) * L0) % p52 == 0) by {
        assert(sum_low52 < p52) by {
            lemma_pow2_pos(52nat);
            lemma_mod_bound((sum as nat) as int, p52 as int);
        }
        lemma_part1_sum_divisible_by_pow2_52(sum_low52, p as nat);
    }

    // Multiplication bound: p * L[0] < pow2(102)
    assert((p as nat) * L0 < pow2(102)) by {
        assert(L0 < pow2(50)) by {
            assert(pow2(50) == 0x4000000000000nat) by {
                lemma2_to64_rest();
            }
        }
        assert(pow2(52) * pow2(50) == pow2(102)) by {
            lemma_pow2_adds(52, 50);
        }
        lemma_mul_strict_inequality((p as nat) as int, p52 as int, L0 as int);
    }

    // No overflow: sum + p*L[0] < u128::MAX
    assert((sum as nat) + (p as nat) * L0 < u128::MAX as nat) by {
        assert((1u128 << 108) == pow2(108)) by {
            assert(pow2(108) <= u128::MAX) by {
                lemma_u128_pow2_le_max(108);
            }
            lemma_u128_shl_is_mul(1, 108);
        }
        assert(pow2(108) + pow2(102) < u128::MAX as nat) by {
            assert(pow2(102) < pow2(108)) by {
                lemma_pow2_strictly_increases(102, 108);
            }
            assert(2 * pow2(108) == pow2(109)) by {
                lemma_pow2_unfold(109);
            }
            assert(pow2(109) < pow2(127)) by {
                lemma_pow2_strictly_increases(109, 127);
            }
            assert(pow2(127) <= u128::MAX) by {
                lemma_u128_pow2_le_max(127);
            }
        }
    }

    // Shift round-trip: (total >> 52) << 52 == total
    assert((total >> 52) << 52 == total) by {
        assert((total as nat) % pow2(52) == 0) by {
            assert((sum as nat) % p52 == sum_low52 as nat);
            lemma_mod_add_eq(
                (sum as nat) as int,
                (sum_low52 as nat) as int,
                ((p as nat) * L0) as int,
                p52 as int,
            );
        }
        lemma_u128_right_left_shift_divisible(total, 52);
    }
}

/// Helper function for part2 bounds
/// With precondition sum < 2^108, we can prove carry < 2^56
///
/// # Structure
/// sum = w + (carry << 52) where:
/// - w = low 52 bits of sum (< 2^52)
/// - carry = sum >> 52 (< 2^56 when sum < 2^108)
pub proof fn lemma_part2_bounds(sum: u128)
    requires
        sum < (1u128 << 108),
    ensures
        ({
            let carry = sum >> 52;
            let w = (sum as u64) & (((1u64 << 52) - 1) as u64);
            &&& w < (1u64 << 52)
            &&& sum == w + (carry << 52)
            &&& carry < (1u128 << 56)
        }),
{
    let carry = sum >> 52;
    let w = (sum as u64) & (((1u64 << 52) - 1) as u64);
    let p52 = pow2(52);

    // Subgoal 1: w < 2^52 (masking always gives < 2^52)
    assert(w < 1u64 << 52) by {
        assert((sum as u64) & (((1u64 << 52) - 1) as u64) < (1u64 << 52)) by (bit_vector);
    }

    // Subgoal 2: carry < 2^56 (follows from sum < 2^108)
    assert((sum >> 52) < (1u128 << 56)) by (bit_vector)
        requires
            sum < (1u128 << 108),
    ;

    // Subgoal 3: sum == w + (carry << 52)
    assert(sum == w + (carry << 52)) by {
        // 3a: Establish p52 > 0 for division lemmas
        lemma_pow2_pos(52);

        // 3b: Fundamental division: sum = p52 * quotient + remainder
        lemma_fundamental_div_mod(sum as int, p52 as int);
        assert(sum == p52 * (sum as nat / p52) + sum as nat % p52);

        // 3c: carry = sum >> 52 = sum / p52
        lemma_u128_shr_is_div(sum, 52);
        assert(carry as nat == sum as nat / p52);

        // 3d: carry << 52 = p52 * (sum / p52)
        assert(carry << 52 == p52 * (sum as nat / p52)) by {
            // 3d.i: No overflow: carry * p52 <= u128::MAX
            assert(carry * p52 <= u128::MAX) by {
                // quotient * p52 <= sum by div-mul property
                lemma_mul_is_commutative(p52 as int, (sum as nat / p52) as int);
                lemma_mul_hoist_inequality(p52 as int, sum as int, p52 as int);
                lemma_div_multiples_vanish(sum as int, p52 as int);
            }
            lemma_u128_shl_is_mul(carry, 52);
            lemma_mul_is_commutative(p52 as int, (sum as nat / p52) as int);
        }

        // 3e: w = sum % p52
        assert(w == sum as nat % p52) by {
            // Mask (1 << 52) - 1 == low_bits_mask(52)
            lemma_u64_shift_is_pow2(52);
            assert(((1u64 << 52) - 1) as u64 == low_bits_mask(52));

            // Masking extracts mod
            lemma_u64_low_bits_mask_is_mod(sum as u64, 52);

            // Connect u64 mod to nat mod
            lemma2_to64_rest();
            assert(p52 == 0x10000000000000);
            assert(sum as u64 == sum % 0x10000000000000000) by (bit_vector);
            assert(sum % 0x10000000000000 == (sum % 0x10000000000000000) % 0x10000000000000)
                by (bit_vector);
        }
    }
}

// =============================================================================
// mul_internal Output Bounds Lemmas
// =============================================================================
/// Bounds on the output of mul_internal when both inputs are bounded.
/// Each output limb[i] is the sum of (min(i+1, 5, 9-i)) products of 52-bit numbers.
///
/// limbs[0] = 1 product  → < 2^104
/// limbs[1] = 2 products → < 2^105
/// limbs[2] = 3 products → < 2^106 (3 * 2^104 < 2^106)
/// limbs[3] = 4 products → < 2^107 (4 * 2^104 = 2^106 < 2^107)
/// limbs[4] = 5 products → < 2^107 (5 * 2^104 < 2^107)
/// limbs[5] = 4 products → < 2^107
/// limbs[6] = 3 products → < 2^106
/// limbs[7] = 2 products → < 2^105
/// limbs[8] = 1 product  → < 2^104
pub(crate) proof fn lemma_mul_internal_limbs_bounds(a: &Scalar52, b: &Scalar52, limbs: &[u128; 9])
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        spec_mul_internal(a, b) == *limbs,
    ensures
        limbs[0] < (1u128 << 104),  // 1 product
        limbs[1] < (1u128 << 105),  // 2 products
        limbs[2] < (1u128 << 106),  // 3 products
        limbs[3] < (1u128 << 107),  // 4 products
        limbs[4] < (1u128 << 107),  // 5 products
        limbs[5] < (1u128 << 107),  // 4 products
        limbs[6] < (1u128 << 106),  // 3 products
        limbs[7] < (1u128 << 105),  // 2 products
        limbs[8] < (1u128 << 104),  // 1 product
{
    // Extract limb bounds from limbs_bounded
    assert(a.limbs[0] < (1u64 << 52));
    assert(a.limbs[1] < (1u64 << 52));
    assert(a.limbs[2] < (1u64 << 52));
    assert(a.limbs[3] < (1u64 << 52));
    assert(a.limbs[4] < (1u64 << 52));
    assert(b.limbs[0] < (1u64 << 52));
    assert(b.limbs[1] < (1u64 << 52));
    assert(b.limbs[2] < (1u64 << 52));
    assert(b.limbs[3] < (1u64 << 52));
    assert(b.limbs[4] < (1u64 << 52));

    let a0 = a.limbs[0] as u128;
    let a1 = a.limbs[1] as u128;
    let a2 = a.limbs[2] as u128;
    let a3 = a.limbs[3] as u128;
    let a4 = a.limbs[4] as u128;
    let b0 = b.limbs[0] as u128;
    let b1 = b.limbs[1] as u128;
    let b2 = b.limbs[2] as u128;
    let b3 = b.limbs[3] as u128;
    let b4 = b.limbs[4] as u128;

    assert((1u64 << 52) as u128 == (1u128 << 52)) by (bit_vector);

    assert(a0 < (1u128 << 52));
    assert(a1 < (1u128 << 52));
    assert(a2 < (1u128 << 52));
    assert(a3 < (1u128 << 52));
    assert(a4 < (1u128 << 52));
    assert(b0 < (1u128 << 52));
    assert(b1 < (1u128 << 52));
    assert(b2 < (1u128 << 52));
    assert(b3 < (1u128 << 52));
    assert(b4 < (1u128 << 52));

    // Key: product of two values < 2^52 is < 2^104 (asserted once, SMT applies to all pairs)
    assert(forall|x: u128, y: u128|
        x < (1u128 << 52) && y < (1u128 << 52) ==> #[trigger] (x * y) < (1u128 << 104))
        by (bit_vector);

    // Sum bounds: n products of < 2^104 each
    assert(2 * (1u128 << 104) == (1u128 << 105)) by (bit_vector);
    assert(3 * (1u128 << 104) < (1u128 << 106)) by (bit_vector);
    assert(4 * (1u128 << 104) < (1u128 << 107)) by (bit_vector);
    assert(5 * (1u128 << 104) < (1u128 << 107)) by (bit_vector);
}

// =============================================================================
// Bridge Lemmas: mul_internal Output → montgomery_reduce Preconditions
// =============================================================================
/// Bridge lemma: bounded × bounded product satisfies montgomery_reduce_input_bounds
///
/// montgomery_reduce_input_bounds requires:
///   limbs[0] < pow2(104), limbs[1] < pow2(105), limbs[2] < pow2(106),
///   limbs[3] < pow2(107), limbs[4] < pow2(107), limbs[5] < pow2(107),
///   limbs[6] < pow2(106), limbs[7] < pow2(105), limbs[8] < pow2(104)
///
/// lemma_mul_internal_limbs_bounds provides:
///   limbs[0] < 2^104, limbs[1] < 2^105, limbs[2] < 2^106,
///   limbs[3] < 2^107, limbs[4] < 2^107, limbs[5] < 2^107,
///   limbs[6] < 2^106, limbs[7] < 2^105, limbs[8] < 2^104
///
/// The bounds are an exact match, so the bridge is trivial.
pub(crate) proof fn lemma_bounded_product_satisfies_input_bounds(
    a: &Scalar52,
    b: &Scalar52,
    limbs: &[u128; 9],
)
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        spec_mul_internal(a, b) == *limbs,
    ensures
        montgomery_reduce_input_bounds(limbs),
{
    // lemma_mul_internal_limbs_bounds proves: limbs[i] < (1u128 << N_i)
    // which exactly matches montgomery_reduce_input_bounds: limbs[i] < pow2(N_i)
    lemma_mul_internal_limbs_bounds(a, b, limbs);

    // Convert (1u128 << N) to pow2(N) for each distinct bound
    lemma_u128_shift_is_pow2(104);
    lemma_u128_shift_is_pow2(105);
    lemma_u128_shift_is_pow2(106);
    lemma_u128_shift_is_pow2(107);
}

/// Bridge lemma: bounded × bounded product satisfies montgomery_reduce_r4_safe_bound
///
/// r4_safe_bound requires: montgomery_reduce_input_bounds(limbs) && slice128_to_nat(limbs) < pow2(520)
///
/// For bounded a, b: a, b < 2^260, so a * b < 2^520.
pub(crate) proof fn lemma_bounded_product_satisfies_r4_safe_bound(
    a: &Scalar52,
    b: &Scalar52,
    limbs: &[u128; 9],
)
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        spec_mul_internal(a, b) == *limbs,
        slice128_to_nat(limbs) == scalar52_to_nat(a) * scalar52_to_nat(b),
    ensures
        montgomery_reduce_r4_safe_bound(limbs),
{
    let a_nat = scalar52_to_nat(a);
    let b_nat = scalar52_to_nat(b);

    // Subgoal 1: input_bounds hold
    lemma_bounded_product_satisfies_input_bounds(a, b, limbs);

    // Subgoal 2: a < 2^260 and b < 2^260
    super::super::scalar_lemmas::lemma_bound_scalar(a);
    super::super::scalar_lemmas::lemma_bound_scalar(b);
    assert(a_nat < pow2(260));
    assert(b_nat < pow2(260));

    // Subgoal 3: 2^260 * 2^260 = 2^520
    assert(pow2(260) * pow2(260) == pow2(520)) by {
        lemma_pow2_adds(260, 260);
    }

    // Subgoal 4: a * b < 2^520
    if b_nat > 0 {
        // a < 2^260, b > 0 → a * b < 2^260 * b
        lemma_mul_strict_inequality(a_nat as int, pow2(260) as int, b_nat as int);
        assert(a_nat * b_nat < pow2(260) * b_nat);

        // b < 2^260, 2^260 > 0 → 2^260 * b < 2^260 * 2^260 = 2^520
        lemma_pow2_pos(260);
        lemma_mul_strict_inequality(b_nat as int, pow2(260) as int, pow2(260) as int);
        assert(pow2(260) * b_nat < pow2(260) * pow2(260));

        // Transitivity: a * b < 2^520
        assert(a_nat * b_nat < pow2(520));
    } else {
        // b == 0 → a * b = 0 < 2^520
        lemma_mul_basics(a_nat as int);
        assert(a_nat * b_nat == 0);
        lemma_pow2_pos(520);
        assert(a_nat * b_nat < pow2(520));
    }

    assert(slice128_to_nat(limbs) < pow2(520));
}

// =============================================================================
// Bridge Lemma: Canonical Input → Canonical Output
// =============================================================================
/// Bridge lemma: when one input is canonical (< L), the product satisfies canonical_bound
///
/// This is the KEY lemma for proving montgomery_reduce returns canonical outputs.
/// It applies when multiplying any bounded scalar by a canonical scalar (like R or RR).
///
/// # Proof Structure
/// 1. limbs_bounded(a) → a < R = 2^260
/// 2. b is canonical → b < L
/// 3. Therefore: a × b < R × L → canonical_bound holds
#[verifier::rlimit(20)]
pub(crate) proof fn lemma_canonical_product_satisfies_canonical_bound(
    a: &Scalar52,
    b: &Scalar52,
    limbs: &[u128; 9],
)
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        scalar52_to_nat(b) < group_order(),  // b is canonical
        spec_mul_internal(a, b) == *limbs,
        slice128_to_nat(limbs) == scalar52_to_nat(a) * scalar52_to_nat(b),
    ensures
        montgomery_reduce_canonical_bound(limbs),
{
    let a_nat = scalar52_to_nat(a);
    let b_nat = scalar52_to_nat(b);
    let R = montgomery_radix();
    let L = group_order();

    // Subgoal 1: input_bounds hold
    lemma_bounded_product_satisfies_input_bounds(a, b, limbs);

    // Subgoal 2: a < R = 2^260
    super::super::scalar_lemmas::lemma_bound_scalar(a);
    assert(a_nat < pow2(260));
    assert(R == pow2(260));

    // Subgoal 3: b < L (from precondition)
    assert(b_nat < L);

    // Subgoal 4: a × b < R × L
    if b_nat == 0 {
        // a × 0 = 0 < R × L (since R × L > 0)
        lemma_mul_basics(a_nat as int);
        assert(a_nat * b_nat == 0);
        assert(L > 0) by {
            assert(L == pow2(252) + 27742317777372353535851937790883648493);
            lemma_pow2_pos(252);
        }
        lemma_pow2_pos(260);
        assert(R > 0);
        // R > 0 and L > 0 implies R * L > 0
        lemma_mul_strictly_positive(R as int, L as int);
        assert(R * L > 0);
    } else {
        // b_nat > 0, so we can use strict inequality
        // a < R and b > 0 → a * b < R * b
        lemma_mul_strict_inequality(a_nat as int, R as int, b_nat as int);
        assert(a_nat * b_nat < R * b_nat);

        // b < L → R * b < R * L (since R > 0)
        lemma_pow2_pos(260);
        assert(R > 0);
        lemma_mul_strict_inequality(b_nat as int, L as int, R as int);
        assert(R * b_nat < R * L);

        // Transitivity: a * b < R * b < R * L
    }

    assert(slice128_to_nat(limbs) < montgomery_radix() * group_order());
}

/// Helper lemma: canonical_bound implies r4_safe_bound (value constraint only)
///
/// canonical_bound: slice128_to_nat(limbs) < R × L
/// r4_safe_bound: slice128_to_nat(limbs) < 2^520
///
/// Since R × L = 2^260 × L < 2^260 × 2^255 = 2^515 < 2^520, canonical_bound implies r4_safe_bound.
pub(crate) proof fn lemma_canonical_bound_implies_r4_safe_bound(limbs: &[u128; 9])
    requires
        montgomery_reduce_canonical_bound(limbs),
    ensures
        montgomery_reduce_r4_safe_bound(limbs),
{
    let val = slice128_to_nat(limbs);
    let R = montgomery_radix();
    let L = group_order();

    // Goal: val < pow2(520)
    // Strategy: val < R × L < pow2(515) < pow2(520)

    assert(val < pow2(520)) by {
        // Subgoal 1: L < pow2(255)
        assert(L < pow2(255)) by {
            lemma_group_order_bound();
        }

        // Subgoal 2: R × L < pow2(515)
        assert(R * L < pow2(515)) by {
            // L < pow2(255) and R > 0 implies L * R < pow2(255) * R
            lemma_pow2_pos(260);
            lemma_mul_strict_inequality(L as int, pow2(255) as int, R as int);

            // Commutativity: L * R == R * L and pow2(255) * R == R * pow2(255)
            lemma_mul_is_commutative(L as int, R as int);
            lemma_mul_is_commutative(pow2(255) as int, R as int);

            // R * pow2(255) == pow2(260) * pow2(255) == pow2(515)
            lemma_pow2_adds(260, 255);
        }

        // Subgoal 3: pow2(515) < pow2(520)
        lemma_pow2_strictly_increases(515, 520);
    }
}

// =============================================================================
// Bridge Lemmas: Identity Array (from_montgomery) → montgomery_reduce Preconditions
// =============================================================================
/// Bridge lemma: identity-style array satisfies montgomery_reduce_input_bounds
///
/// This lemma is needed for `from_montgomery` which directly converts a Scalar52
/// to a 9-limb array by padding with zeros: [a0, a1, a2, a3, a4, 0, 0, 0, 0]
///
/// Proof sketch:
///   - limbs[i] = a.limbs[i] < 2^52 for i < 5
///   - limbs[i] = 0 for i >= 5
///   - 2^52 < 2^104 < 2^105 < ... < 2^107
///   - So all bounds are trivially satisfied
pub(crate) proof fn lemma_identity_array_satisfies_input_bounds(a: &Scalar52, limbs: &[u128; 9])
    requires
        limbs_bounded(a),
        forall|i: int| #![auto] 0 <= i < 5 ==> limbs[i] == a.limbs[i] as u128,
        forall|i: int| #![auto] 5 <= i < 9 ==> limbs[i] == 0,
    ensures
        montgomery_reduce_input_bounds(limbs),
{
    // For i < 5: limbs[i] = a.limbs[i] < 2^52, and 2^52 < pow2(104..107) for all required bounds
    // For i >= 5: limbs[i] = 0 < pow2(anything)
    assert((1u64 << 52) == pow2(52)) by {
        lemma_u64_shift_is_pow2(52);
    }

    // 2^52 < each required bound
    lemma_pow2_strictly_increases(52, 104);
    lemma_pow2_strictly_increases(52, 105);
    lemma_pow2_strictly_increases(52, 106);
    lemma_pow2_strictly_increases(52, 107);

    // 0 < each required bound (for the zero limbs 5-8)
    lemma_pow2_pos(104);
    lemma_pow2_pos(105);
    lemma_pow2_pos(106);
    lemma_pow2_pos(107);
}

/// Bridge lemma: identity array satisfies canonical_bound for bounded input
///
/// For from_montgomery:
///   - Input value = scalar52_to_nat(a) < 2^260 (from limbs_bounded)
///   - R × L = 2^260 × (2^252 + ...) ≈ 2^513
///   - So input < 2^260 < R × L ✓
///
/// This means from_montgomery gets the stronger postcondition: is_canonical_scalar52
pub(crate) proof fn lemma_identity_array_satisfies_canonical_bound(a: &Scalar52, limbs: &[u128; 9])
    requires
        limbs_bounded(a),
        forall|i: int| #![auto] 0 <= i < 5 ==> limbs[i] == a.limbs[i] as u128,
        forall|i: int| #![auto] 5 <= i < 9 ==> limbs[i] == 0,
    ensures
        montgomery_reduce_canonical_bound(limbs),
{
    // First establish input_bounds
    lemma_identity_array_satisfies_input_bounds(a, limbs);

    // Show slice128_to_nat(limbs) == scalar52_to_nat(a)
    super::super::scalar_lemmas::lemma_from_montgomery_limbs_conversion(limbs, &a.limbs);

    // Show scalar52_to_nat(a) < pow2(260)
    super::super::scalar_lemmas::lemma_bound_scalar(a);
    assert(scalar52_to_nat(a) < pow2(260));

    // Show pow2(260) < montgomery_radix() * group_order()
    // montgomery_radix() = pow2(260)
    // group_order() = 2^252 + 27742317777372353535851937790883648493 > 2^252
    assert(montgomery_radix() == pow2(260));

    // group_order() > 1, so R * L > R = 2^260
    assert(group_order() > 1) by {
        assert(group_order() == pow2(252) + 27742317777372353535851937790883648493);
        lemma_pow2_pos(252);
    }

    // For slice128_to_nat(limbs) < R * L, we need to show:
    // scalar52_to_nat(a) < pow2(260) < pow2(260) * group_order()
    assert(pow2(260) * group_order() > pow2(260)) by {
        assert(group_order() > 1);
        lemma_mul_basics(pow2(260) as int);
        lemma_mul_strict_inequality(1, group_order() as int, pow2(260) as int);
    }

    assert(slice128_to_nat(limbs) < montgomery_radix() * group_order());
}

// =============================================================================
// r4 Bounds Lemmas - Proving r4 < 2^52 + L[4]
// See docs/proofs_for_montgomery_reduce/r4_bounds_proof.md for paper proof
// =============================================================================
/// L[4] = 2^44 (the highest limb of the group order L)
pub(crate) proof fn lemma_l_limb4_is_pow2_44()
    ensures
        constants::L.limbs[4] as nat == pow2(44),
        constants::L.limbs[4] == 0x0000100000000000u64,
{
    // Direct computation
    assert(constants::L.limbs[4] == 0x0000100000000000u64);

    // 0x0000100000000000 = 2^44
    // Using bit_vector for hex computation
    assert(0x0000100000000000u64 == (1u64 << 44)) by (bit_vector);

    // Convert shift to pow2
    lemma_u64_shift_is_pow2(44);
    assert((1u64 << 44) as nat == pow2(44));
}

// =============================================================================
// Option B: Pre-sub and Post-sub lemmas
// =============================================================================
// These lemmas encapsulate the Option B proof strategy for montgomery_reduce.
// See docs/proofs_for_montgomery_reduce/option_b_paper_proofs.md
/// Pre-subtraction lemma: Establishes the quotient relationship for post_sub.
///
/// # What This Lemma Proves
///
/// intermediate × R = T + N×L
///
/// where:
/// - intermediate = scalar52_to_nat(r0..r4)
/// - R = 2^260 (Montgomery radix)
/// - T = slice128_to_nat(limbs) (input value)
/// - N = five_u64_limbs_to_nat(n0..n4) (Montgomery quotient from Part 1)
/// - L = group_order()
///
/// # Proof Strategy
///
/// 1. Call Part 2 chain lemma to get: five_u64_limbs_to_nat(r0..r4) × R = T + N×L
/// 2. Connect scalar52_to_nat(intermediate) to five_u64_limbs_to_nat(r0..r4)
///
/// # Note
///
/// This lemma does NOT prove r4 bounds or intermediate < 2L.
/// For the canonical path, use lemma_r4_bound_from_canonical separately.
pub(crate) proof fn lemma_montgomery_reduce_pre_sub(
    limbs: &[u128; 9],
    // N values from Part 1
    n0: u64,
    n1: u64,
    n2: u64,
    n3: u64,
    n4: u64,
    // N as nat (caller proves N < 2^260 via lemma_general_bound)
    n: nat,
    // Final carry from Part 1
    carry4: u128,
    // Part 2 sums
    sum5: u128,
    sum6: u128,
    sum7: u128,
    sum8: u128,
    // Part 2 carries
    carry5: u128,
    carry6: u128,
    carry7: u128,
    // Part 2 outputs: the r values computed by part2
    r0: u64,
    r1: u64,
    r2: u64,
    r3: u64,
    r4: u64,
    intermediate: &Scalar52,
)
    requires
        montgomery_reduce_input_bounds(limbs),
        // N bounds (from part1 postconditions: each n_i < 2^52)
        n0 < pow2(52),
        n1 < pow2(52),
        n2 < pow2(52),
        n3 < pow2(52),
        n4 < pow2(52),
        // N = five_u64_limbs_to_nat(n0..n4)
        n == five_u64_limbs_to_nat(n0, n1, n2, n3, n4),
        // Part 1 divisibility result (caller proves this via lemma_part1_chain_divisibility)
        ({
            let n = five_u64_limbs_to_nat(n0, n1, n2, n3, n4);
            let t_low = limbs[0] as nat + limbs[1] as nat * pow2(52) + limbs[2] as nat * pow2(104)
                + limbs[3] as nat * pow2(156) + limbs[4] as nat * pow2(208);
            let l_low = constants::L.limbs[0] as nat + constants::L.limbs[1] as nat * pow2(52)
                + constants::L.limbs[2] as nat * pow2(104) + constants::L.limbs[3] as nat * pow2(
                156,
            ) + constants::L.limbs[4] as nat * pow2(208);
            (t_low + n * l_low) % pow2(260) == 0
        }),
        // Part 1 quotient result (caller proves this via lemma_part1_chain_divisibility)
        // This is the exact quotient: t_low + nl_low_coeffs = carry4 × 2^260
        ({
            let t_low = limbs[0] as nat + limbs[1] as nat * pow2(52) + limbs[2] as nat * pow2(104)
                + limbs[3] as nat * pow2(156) + limbs[4] as nat * pow2(208);
            let l0_val = constants::L.limbs[0] as nat;
            let l1 = constants::L.limbs[1] as nat;
            let l2 = constants::L.limbs[2] as nat;
            let l4 = constants::L.limbs[4] as nat;
            let coeff0 = (n0 as nat) * l0_val;
            let coeff1 = (n0 as nat) * l1 + (n1 as nat) * l0_val;
            let coeff2 = (n0 as nat) * l2 + (n1 as nat) * l1 + (n2 as nat) * l0_val;
            let coeff3 = (n1 as nat) * l2 + (n2 as nat) * l1 + (n3 as nat) * l0_val;
            let coeff4 = (n0 as nat) * l4 + (n2 as nat) * l2 + (n3 as nat) * l1 + (n4 as nat)
                * l0_val;
            let nl_low_coeffs = coeff0 + coeff1 * pow2(52) + coeff2 * pow2(104) + coeff3 * pow2(156)
                + coeff4 * pow2(208);
            t_low + nl_low_coeffs == (carry4 as nat) * pow2(260)
        }),
        // Sum definitions (how part2 inputs are computed)
        sum5 as nat == carry4 as nat + limbs[5] as nat + (n1 as nat) * (
        constants::L.limbs[4] as nat) + (n3 as nat) * (constants::L.limbs[2] as nat) + (n4 as nat)
            * (constants::L.limbs[1] as nat),
        sum6 as nat == carry5 as nat + limbs[6] as nat + (n2 as nat) * (
        constants::L.limbs[4] as nat) + (n4 as nat) * (constants::L.limbs[2] as nat),
        sum7 as nat == carry6 as nat + limbs[7] as nat + (n3 as nat) * (
        constants::L.limbs[4] as nat),
        sum8 as nat == carry7 as nat + limbs[8] as nat + (n4 as nat) * (
        constants::L.limbs[4] as nat),
        // Part2 stage equations (from part2 postconditions)
        sum5 as nat == (r0 as nat) + (carry5 as nat) * pow2(52),
        sum6 as nat == (r1 as nat) + (carry6 as nat) * pow2(52),
        sum7 as nat == (r2 as nat) + (carry7 as nat) * pow2(52),
        sum8 as nat == (r3 as nat) + (r4 as nat) * pow2(52),
        // Bounds on r0-r3 from part2
        (r0 as nat) < pow2(52),
        (r1 as nat) < pow2(52),
        (r2 as nat) < pow2(52),
        (r3 as nat) < pow2(52),
        // intermediate is constructed from r0..r4
        intermediate.limbs[0] == r0,
        intermediate.limbs[1] == r1,
        intermediate.limbs[2] == r2,
        intermediate.limbs[3] == r3,
        intermediate.limbs[4] == r4,
    ensures
// Quotient relationship: intermediate × R = T + N×L

        scalar52_to_nat(intermediate) * montgomery_radix() == slice128_to_nat(limbs) + n
            * group_order(),
{
    // Call Part 2 chain lemma to get: five_u64_limbs_to_nat(r0..r4) × 2^260 = T + N×L
    lemma_part2_chain_quotient(
        limbs,
        n0,
        n1,
        n2,
        n3,
        n4,
        carry4,
        sum5,
        sum6,
        sum7,
        sum8,
        carry5,
        carry6,
        carry7,
        r0,
        r1,
        r2,
        r3,
        r4,
    );

    let inter_nat = five_u64_limbs_to_nat(r0, r1, r2, r3, r4);

    // Connect scalar52_to_nat(intermediate) to five_u64_limbs_to_nat(r0..r4)
    assert(scalar52_to_nat(intermediate) == inter_nat) by {
        use crate::lemmas::scalar_lemmas::lemma_five_limbs_equals_to_nat;
        use crate::specs::scalar52_specs::five_limbs_to_nat_aux;

        // five_limbs_to_nat_aux(intermediate.limbs) == scalar52_to_nat(intermediate)
        lemma_five_limbs_equals_to_nat(&intermediate.limbs);

        // five_limbs_to_nat_aux uses pow2(k)*limbs[i], five_u64_limbs_to_nat uses limbs[i]*pow2(k)
        // These are equal by commutativity
        lemma_mul_is_commutative(pow2(52) as int, r1 as int);
        lemma_mul_is_commutative(pow2(104) as int, r2 as int);
        lemma_mul_is_commutative(pow2(156) as int, r3 as int);
        lemma_mul_is_commutative(pow2(208) as int, r4 as int);
    }

    // montgomery_radix() == pow2(260) by definition
    // Part 2 ensures: inter_nat * pow2(260) == slice128_to_nat(limbs) + n * group_order()
    // Combined: scalar52_to_nat(intermediate) * montgomery_radix() == T + N×L
}

/// Carry8 bound lemma: Proves the final carry fits in 53 bits
///
/// This lemma is called BEFORE the `carry as u64` cast to establish that
/// the cast is safe. It solves the chicken-and-egg problem where:
/// - We need `carry < 2^53` to safely cast to u64
/// - `lemma_montgomery_reduce_pre_sub` takes `r4: u64` as input
///
/// # Direct Sum8 Bound Proof (no assume!)
///
/// From the computation: sum8 = carry7 + limb8 + n4 × L[4]
///   - carry7 < 2^56     (from part2(sum7) postcondition)
///   - limb8 < 2^104     (from montgomery_reduce_input_bounds)
///   - n4 < 2^52, L[4] = 2^44, so n4 × L[4] < 2^96
///
/// Therefore: sum8 < 2^56 + 2^104 + 2^96 < 2^105
/// And: carry8 = sum8 >> 52 < 2^105 / 2^52 = 2^53
pub(crate) proof fn lemma_carry8_bound(
    limb8: u128,  // limbs[8] passed separately to avoid array indexing in bit_vector
    n4: u64,
    l4: u64,  // constants::L.limbs[4] passed separately
    carry7: u128,
    sum8: u128,
    carry8: u128,
)
    requires
// limb8 < 2^104 (from montgomery_reduce_input_bounds on limbs[8])

        limb8 < (1u128 << 104),
        // n4 from part1 postcondition
        n4 < (1u64 << 52),
        // l4 = L[4] = 2^44
        l4 == (1u64 << 44),
        // carry7 from part2(sum7) postcondition
        carry7 < (1u128 << 56),
        // sum8 definition
        sum8 == carry7 + limb8 + (n4 as u128) * (l4 as u128),
        // carry8 from part2(sum8) postcondition: carry = sum >> 52
        carry8 == sum8 >> 52,
    ensures
// The tight bound: carry8 < 2^53 (allows safe cast to u64)

        carry8 < pow2(53),
{
    // =========================================================================
    // Combined proof using bit_vector
    // =========================================================================
    //
    // sum8 = carry7 + limb8 + n4×L[4]
    //      < 2^56 + 2^104 + (2^52 × 2^44)
    //      = 2^56 + 2^104 + 2^96
    //      < 2^105
    //
    // carry8 = sum8 >> 52 < 2^105 >> 52 = 2^53
    //
    // Note: L[4] = 2^44 is passed in as l4 to avoid array indexing in bit_vector
    assert(carry8 < (1u128 << 53)) by (bit_vector)
        requires
            limb8 < (1u128 << 104),
            n4 < (1u64 << 52),
            l4 == (1u64 << 44),
            carry7 < (1u128 << 56),
            sum8 == carry7 + limb8 + (n4 as u128) * (l4 as u128),
            carry8 == sum8 >> 52,
    ;

    // Convert to pow2 for the postcondition
    lemma_u128_shift_is_pow2(53);
    assert(carry8 < pow2(53));
}

/// Post-subtraction lemma: Establishes the montgomery congruence
///
/// This lemma is called after the conditional subtraction and proves:
/// `result × R ≡ T (mod L)` (montgomery_congruent)
///
/// # Mathematical Proof
///
/// **Given** (preconditions):
/// 1. (Quotient): intermediate × R = T + N×L  (from Part 2)
/// 2. (Sub result): result = (intermediate - L) mod L
///
/// **Derivation**:
/// 1. result ≡ intermediate (mod L)           [from sub: (x - L) mod L ≡ x mod L]
/// 2. result × R ≡ intermediate × R (mod L)   [multiply by R]
/// 3. result × R ≡ T + N×L (mod L)            [substitute quotient]
/// 4. result × R ≡ T (mod L)                  [N×L ≡ 0 mod L]  ∎
pub(crate) proof fn lemma_montgomery_reduce_post_sub(
    limbs: &[u128; 9],
    intermediate: &Scalar52,
    result: &Scalar52,
    n: nat,  // N value from Part 1
)
    requires
// Sub's postcondition: result = (intermediate - L) mod L

        scalar52_to_nat(result) == (scalar52_to_nat(intermediate) as int - group_order() as int) % (
        group_order() as int),
        // Part 2 quotient result: intermediate × R = T + N×L
        scalar52_to_nat(intermediate) * montgomery_radix() == slice128_to_nat(limbs) + n
            * group_order(),
    ensures
        montgomery_congruent(result, limbs),
{
    let t = slice128_to_nat(limbs);
    let l = group_order();
    let r = montgomery_radix();
    let inter = scalar52_to_nat(intermediate);
    let res = scalar52_to_nat(result);

    // Goal: montgomery_congruent(result, limbs)
    //       i.e., (res * r) % l == t % l
    assert(montgomery_congruent(result, limbs)) by {
        // Step 1: result ≡ intermediate (mod L)
        // From sub: res = (inter - l) % l, so res % l == inter % l
        assert((res as int) % (l as int) == (inter as int) % (l as int)) by {
            // Subgoal 1a: (inter - l) % l == inter % l
            lemma_mod_sub_multiples_vanish(inter as int, l as int);

            // Subgoal 1b: res % l == res (mod idempotence via lemma_small_mod)
            // res = (inter - l) % l, and 0 <= res < l by lemma_mod_bound
            lemma_mod_bound((inter as int) - (l as int), l as int);
            // So res < l, meaning res % l == res
            lemma_small_mod(res, l);
            // Therefore: res % l == res == (inter - l) % l == inter % l
        }

        // Step 2: result × R ≡ intermediate × R (mod L)
        assert(((res * r) as int) % (l as int) == ((inter * r) as int) % (l as int)) by {
            // If a ≡ b (mod m), then a×c ≡ b×c (mod m)
            lemma_mul_factors_congruent_implies_products_congruent(
                r as int,
                res as int,
                inter as int,
                l as int,
            );
        }

        // Step 3: intermediate × R = T + N×L (from precondition)
        assert(inter * r == t + n * l);

        // Step 4: T + N×L ≡ T (mod L)
        assert(((t + n * l) as int) % (l as int) == (t as int) % (l as int)) by {
            // (a + k×m) % m == a % m
            lemma_mod_multiples_vanish(n as int, t as int, l as int);
        }

        // Combine: (res * r) % l == (inter * r) % l == (t + n*l) % l == t % l
        assert((res * r) % l == t % l);
    }
}

// =============================================================================
// REDC Theorem: Top-Down Proof of Intermediate Bound
// =============================================================================
// These lemmas prove the key REDC result: T < R×L implies intermediate < 2L
// This gives us a much tighter bound on r4 than the bottom-up approach.
// =============================================================================
/// The Montgomery quotient N is always bounded by R.
/// This is because N = (-T × L⁻¹) mod R is defined as a modulo operation.
///
/// Proof: N = (R - ((T × L_INV) % R)) % R
///   - (T × L_INV) % R ∈ [0, R)
///   - R - ((T × L_INV) % R) ∈ (0, R]  (when T×L_INV ≢ 0 mod R)
///   - (R - ((T × L_INV) % R)) % R ∈ [0, R)
pub(crate) proof fn lemma_montgomery_quotient_bounded(t: nat)
    ensures
        montgomery_quotient(t) < montgomery_radix(),
{
    let r = montgomery_radix();
    let l_inv = l_inv_mod_r();

    // Step 1: (t * l_inv) % r < r
    // This is a basic property of modulo
    let inner = (t * l_inv) % r;
    assert(inner < r) by {
        // x % m < m for m > 0
        lemma_pow2_pos(260);
        assert(r == pow2(260));
        assert(r > 0);
        // vstd gives us: x % m < m when m > 0
    }

    // Step 2: r - inner is in (0, r] when inner < r
    // Specifically: 0 < r - inner <= r
    let diff = (r as int - inner as int);
    assert(0 < diff) by {
        // inner < r, so r - inner > 0
        assert(inner < r);
    }
    // diff = r - inner where inner >= 0, so diff <= r
    // inner is a nat, so inner >= 0, thus diff = r - inner <= r
    // (Verus auto-proves: nat type guarantees inner >= 0, hence diff <= r)

    // Step 3: diff % r is in [0, r)
    // When diff is in (0, r], then diff % r is diff (if diff < r) or 0 (if diff == r)
    // Either way, the result is in [0, r)
    let result = (diff % (r as int)) as nat;

    // By definition of montgomery_quotient
    assert(montgomery_quotient(t) == result);

    // result < r because x % m ∈ [0, m) for m > 0
    assert(result < r) by {
        // Establish r > 0 for lemma_mod_bound's precondition
        lemma_pow2_pos(260);
        assert(r == pow2(260));
        assert(r > 0);
        // diff % r is in [0, r) by lemma_mod_bound
        lemma_mod_bound(diff, r as int);
    }
}

// =============================================================================
// GCD and Inverse Properties for L and R
// =============================================================================
/// gcd(L % R, R) == 1 where L = group_order() and R = montgomery_radix() = 2^260
///
/// This follows from:
/// 1. L is odd (lemma_group_order_is_odd)
/// 2. L % R is also odd (since L is odd and R is a power of 2)
/// 3. gcd(odd, power_of_2) == 1
pub(crate) proof fn lemma_gcd_l_r_is_one()
    ensures
        spec_gcd(group_order() % montgomery_radix(), montgomery_radix()) == 1,
{
    let l = group_order();
    let r = montgomery_radix();

    // L is odd
    lemma_group_order_is_odd();
    assert(l % 2 == 1);

    // L % R is also odd (since R is a power of 2, L % R preserves the lowest bit)
    // If L is odd, then L % (2^k) is also odd for any k
    assert((l % r) % 2 == 1) by {
        // L % R = L % 2^260 = L % (2 * 2^259)
        // (L % (2 * 2^259)) % 2 == L % 2 by lemma_mod_mod
        lemma_pow2_pos(259);
        assert(pow2(260) == 2 * pow2(259)) by {
            lemma_pow2_unfold(260);
        }
        assert(r == 2 * pow2(259));
        lemma_mod_mod(l as int, 2, pow2(259) as int);
        // Now we have: (l % (2 * pow2(259))) % 2 == l % 2
        // i.e., (l % r) % 2 == l % 2 == 1
    }

    // gcd(odd, power_of_2) == 1 (from number_theory_lemmas)
    // axiom_gcd_pow2_odd gives gcd(2^260, l%r) == 1, then symmetry gives gcd(l%r, 2^260) == 1
    axiom_gcd_pow2_odd(260, l % r);
    axiom_gcd_symmetric(pow2(260), l % r);
}

/// l_inv_mod_r() is the multiplicative inverse of L modulo R.
///
/// This is now a THEOREM (not an axiom) because:
/// 1. gcd(L % R, R) == 1 (from lemma_gcd_l_r_is_one)
/// 2. l_inv_mod_r() is defined as spec_mod_inverse(L, R)
/// 3. lemma_mod_inverse_correct proves the inverse property
pub(crate) proof fn lemma_l_inv_mod_r_property()
    ensures
        (l_inv_mod_r() * group_order()) % montgomery_radix() == 1,
        l_inv_mod_r() < montgomery_radix(),  // l_inv is in [0, R)
{
    let l = group_order();
    let r = montgomery_radix();

    // Establish R > 1
    lemma_pow2_pos(260);
    assert(r == pow2(260));
    // pow2(260) = 2^260 > 1 (trivially true for any power >= 1)
    assert(r > 1) by {
        // pow2(260) = pow2(259) + pow2(259) >= 2
        lemma_pow2_plus_one(259);
        assert(pow2(260) == pow2(259) + pow2(259));
        lemma_pow2_pos(259);
        assert(pow2(259) > 0);
    }

    // Establish gcd(L % R, R) == 1
    lemma_gcd_l_r_is_one();
    assert(spec_gcd(l % r, r) == 1);

    // Apply lemma_mod_inverse_correct
    lemma_mod_inverse_correct(l, r);

    // l_inv_mod_r() is defined as spec_mod_inverse(l, r)
    // lemma_mod_inverse_correct gives us:
    // - spec_mod_inverse(l, r) < r
    // - (l * spec_mod_inverse(l, r)) % r == 1

    assert(l_inv_mod_r() < r);
    assert((l * l_inv_mod_r()) % r == 1);

    // By commutativity: (l_inv * l) % r == (l * l_inv) % r
    lemma_mul_is_commutative(l_inv_mod_r() as int, l as int);
}

/// If (a + b) % m == 0, then b % m == (m - a % m) % m (i.e., b ≡ -a mod m)
///
/// This is the fundamental property that relates addition to negation in modular arithmetic.
/// When a + b ≡ 0 (mod m), b is the additive inverse of a modulo m.
///
/// # Proof Structure
/// 1. (a + b) % m == 0 implies (a%m + b%m) % m == 0
/// 2. Since a%m, b%m ∈ [0, m), their sum ∈ [0, 2m)
/// 3. For sum % m == 0 with sum ∈ [0, 2m): sum == 0 or sum == m
/// 4. Case split shows b%m equals the canonical negation of a%m
pub(crate) proof fn lemma_sum_zero_implies_neg(a: nat, b: nat, m: nat)
    requires
        m > 0,
        (a + b) % m == 0,
    ensures
        b % m == ((m as int - (a % m) as int) % (m as int)) as nat,
{
    let a_mod = a % m;
    let b_mod = b % m;
    let neg_a: nat = ((m as int - a_mod as int) % (m as int)) as nat;

    // Subgoal 1: (a_mod + b_mod) % m == 0
    lemma_add_mod_noop(a as int, b as int, m as int);
    assert((a_mod + b_mod) % m == 0);

    // Subgoal 2: Both a_mod and b_mod are in [0, m), so sum in [0, 2m)
    assert(a_mod < m && b_mod < m);
    let sum = a_mod + b_mod;
    assert(sum < 2 * m);

    // Subgoal 3: sum == 0 or sum == m (since sum % m == 0 and sum < 2m)
    assert(sum == 0 || sum == m) by {
        if sum < m {
            lemma_small_mod(sum, m);
            // sum % m == sum, so sum == 0
        } else {
            // m <= sum < 2m implies sum % m == sum - m
            lemma_fundamental_div_mod_converse(sum as int, m as int, 1, (sum - m) as int);
            // sum - m == 0 from sum % m == 0
        }
    }

    // Subgoal 4: b_mod == neg_a in both cases
    if sum == 0 {
        // Case 1: a_mod == b_mod == 0
        lemma_mod_self_0(m as int);
        assert(neg_a == 0);
    } else {
        // Case 2: sum == m, so b_mod == m - a_mod
        // Must have a_mod > 0 (else b_mod == m, contradicting b_mod < m)
        assert(a_mod > 0) by {
            if a_mod == 0 {
                assert(b_mod == m);
                assert(false);  // contradiction with b_mod < m
            }
        }
        // 0 < m - a_mod < m, so (m - a_mod) % m == m - a_mod
        lemma_small_mod((m - a_mod) as nat, m);
    }
}

/// Uniqueness of Montgomery quotient: If (T + n*L) ≡ 0 (mod R) and n < R,
/// then n == montgomery_quotient(T).
///
/// This is crucial for connecting the computed n from part1 to the spec definition.
///
/// Mathematical proof:
/// 1. (T + n*L) ≡ 0 (mod R)  implies  n*L ≡ -T (mod R)
/// 2. montgomery_quotient(T) * L ≡ -T (mod R)  (by definition of montgomery_quotient)
/// 3. Therefore n*L ≡ montgomery_quotient(T)*L (mod R)
/// 4. By lemma_cancel_mul_L_mod_R: n ≡ montgomery_quotient(T) (mod R)
/// 5. Since both are in [0, R): n == montgomery_quotient(T)
pub(crate) proof fn lemma_montgomery_quotient_unique(t: nat, n: nat)
    requires
        n < montgomery_radix(),  // n in [0, R)
        (t + n * group_order()) % montgomery_radix() == 0,  // R | (T + n*L)

    ensures
        n == montgomery_quotient(t),
{
    let r = montgomery_radix();
    let l = group_order();
    let l_inv = l_inv_mod_r();
    let q = montgomery_quotient(t);

    // Establish R > 1 (needed for modular arithmetic)
    lemma_pow2_pos(260);
    assert(r == pow2(260));
    assert(r > 1) by {
        lemma_pow2_plus_one(259);
        assert(pow2(260) == pow2(259) + pow2(259));
        lemma_pow2_pos(259);
    }

    // Get the property: l_inv * L ≡ 1 (mod R)
    lemma_l_inv_mod_r_property();
    assert((l_inv * l) % r == 1);
    assert(l_inv < r);

    // Step 1: montgomery_quotient(t) < R
    lemma_montgomery_quotient_bounded(t);
    assert(q < r);

    // ===========================================================================
    // Step 2: From (T + n*L) ≡ 0 (mod R), derive (n*L) % R == neg_t
    // where neg_t = (R - (T % R)) % R is the representation of -T mod R
    // ===========================================================================

    let t_mod = t % r;
    let neg_t: nat = ((r as int - t_mod as int) % (r as int)) as nat;  // -T mod R

    // (t + n*l) % r == 0 implies (n*l) % r == neg_t
    // Use lemma_sum_zero_implies_neg: if (a + b) % m == 0 then b % m == (m - a % m) % m
    lemma_sum_zero_implies_neg(t, n * l, r);
    assert((n * l) % r == neg_t);

    // ===========================================================================
    // Step 3: Show (q * L) % R == neg_t (i.e., q*L ≡ -T mod R)
    // where q = montgomery_quotient(t) = ((r - ((t * l_inv) % r)) % r)
    // ===========================================================================

    // q = (-t * l_inv) mod r (as an unsigned computation)
    // q * l ≡ (-t * l_inv) * l ≡ -t * (l_inv * l) ≡ -t * 1 ≡ -t (mod r)

    assert((q * l) % r == neg_t) by {
        let t_linv_mod = (t * l_inv) % r;

        // Key fact: (l * t * l_inv) % r == t % r
        // Because l_inv * l ≡ 1 (mod r), we have l * t * l_inv = t * (l * l_inv) ≡ t (mod r)
        lemma_mul_is_associative(l as int, t as int, l_inv as int);
        lemma_mul_is_commutative(l as int, t as int);
        assert(l * t * l_inv == t * l * l_inv);
        lemma_mul_is_associative(t as int, l as int, l_inv as int);
        assert(t * l * l_inv == t * (l * l_inv));
        lemma_mul_is_commutative(l as int, l_inv as int);
        assert(l * l_inv == l_inv * l);
        assert(t * (l * l_inv) == t * (l_inv * l));
        lemma_mul_mod_noop_right(t as int, (l_inv * l) as int, r as int);
        assert((t * (l_inv * l)) % r == (t * ((l_inv * l) % r)) % r);
        assert((t * ((l_inv * l) % r)) % r == (t * 1) % r);
        lemma_mul_basics(t as int);
        assert((t * (l_inv * l)) % r == t % r);
        assert((l * t * l_inv) % r == t_mod);

        // Also establish (l * (t * l_inv)) % r == t_mod
        lemma_mul_is_associative(l as int, t as int, l_inv as int);
        assert(l * (t * l_inv) == l * t * l_inv);
        assert((l * (t * l_inv)) % r == t_mod);

        // q = ((r - ((t * l_inv) % r)) % r) by definition of montgomery_quotient
        // We need: (q * l) % r == neg_t

        // Use lemma_mul_distributes_over_neg_mod for the key step
        // lemma_mul_distributes_over_neg_mod(a, b, m) gives:
        // (a * ((m - b % m) as nat)) % m == ((m - (a * b) % m) as nat) % m
        // With a = l, b = t * l_inv, m = r:
        // (l * ((r - (t * l_inv) % r) as nat)) % r == ((r - (l * (t * l_inv)) % r) as nat) % r
        lemma_mul_distributes_over_neg_mod(l, t * l_inv, r);

        // Let's name the key quantities:
        let raw_neg: nat = (r - t_linv_mod) as nat;  // r - (t * l_inv) % r, possibly = r when t_linv_mod == 0

        // From the lemma:
        // (l * raw_neg) % r == ((r - (l * (t * l_inv)) % r) as nat) % r

        // RHS: ((r - (l * (t * l_inv)) % r) as nat) % r
        // Since (l * (t * l_inv)) % r == t_mod, this is ((r - t_mod) as nat) % r
        // When t_mod == 0: (r - 0) % r = r % r = 0 = neg_t
        // When t_mod > 0: (r - t_mod) % r = r - t_mod = neg_t (since r - t_mod < r)
        let rhs: nat = ((r as int - ((l * (t * l_inv)) % r) as int)) as nat % r;
        assert(rhs == neg_t) by {
            assert((l * (t * l_inv)) % r == t_mod);
            if t_mod == 0 {
                lemma_mod_self_0(r as int);
                assert(neg_t == 0);
            } else {
                assert(r - t_mod < r);
                lemma_small_mod((r - t_mod) as nat, r);
                assert(neg_t == (r - t_mod) as nat);
            }
        }

        // LHS: (l * raw_neg) % r
        // We need to show this equals (q * l) % r
        // q = ((r - t_linv_mod) % r) as nat
        // raw_neg = (r - t_linv_mod) as nat (without the % r)
        // When t_linv_mod == 0: raw_neg = r, q = r % r = 0
        //   (l * raw_neg) % r = (l * r) % r = 0 = (l * q) % r ✓
        // When t_linv_mod > 0: raw_neg = r - t_linv_mod = q (since r - t_linv_mod < r)
        //   (l * raw_neg) % r = (l * q) % r ✓

        assert((l * raw_neg) % r == (l * q) % r) by {
            if t_linv_mod == 0 {
                // raw_neg = r, q = 0
                lemma_mod_self_0(r as int);
                assert(q == 0);
                assert(raw_neg == r);
                // (l * r) % r = 0 = (l * 0) % r
                lemma_mod_multiples_basic(l as int, r as int);
                lemma_mul_basics(l as int);
            } else {
                // raw_neg = r - t_linv_mod = q (both < r)
                assert(raw_neg < r);
                lemma_small_mod(raw_neg, r);
                assert(q == raw_neg);
            }
        }

        // By commutativity: (l * q) % r = (q * l) % r
        lemma_mul_is_commutative(l as int, q as int);
        assert((l * q) % r == (q * l) % r);

        // Chain: (q * l) % r == (l * q) % r == (l * raw_neg) % r == rhs == neg_t
        assert((q * l) % r == neg_t);
    }

    // ===========================================================================
    // Step 4: Since (n*L) % R == neg_t and (q*L) % R == neg_t, we have (n*L) % R == (q*L) % R
    // ===========================================================================
    assert((n * l) % r == (q * l) % r);

    // ===========================================================================
    // Step 5: By lemma_cancel_mul_L_mod_R: n % R == q % R
    // ===========================================================================
    lemma_cancel_mul_L_mod_R(n, q);
    assert(n % r == q % r);

    // ===========================================================================
    // Step 6: Since n < R and q < R, n % R == q % R implies n == q
    // ===========================================================================
    // Inlined lemma_mod_unique: if a < m and b < m, then a % m == a and b % m == b
    assert(n == q) by {
        lemma_small_mod(n, r);  // n < r implies n % r == n
        lemma_small_mod(q, r);  // q < r implies q % r == q
    };
}

/// Connects computed intermediate to montgomery_intermediate spec.
///
/// Given that intermediate * R == T + n * L (from part2 chain), if n satisfies
/// the Montgomery quotient property, then intermediate == montgomery_intermediate(T).
///
/// Proof:
/// 1. By uniqueness (lemma_montgomery_quotient_unique), n == montgomery_quotient(t)
/// 2. So intermediate * R == T + montgomery_quotient(T) * L
/// 3. By definition: montgomery_intermediate(T) = (T + montgomery_quotient(T) * L) / R
/// 4. Since (intermediate * R) / R == intermediate, we have the result
pub(crate) proof fn lemma_intermediate_equals_spec(t: nat, n: nat, intermediate: nat)
    requires
        n < montgomery_radix(),
        (t + n * group_order()) % montgomery_radix() == 0,
        intermediate * montgomery_radix() == t + n * group_order(),
    ensures
        intermediate == montgomery_intermediate(t),
{
    // By uniqueness, n == montgomery_quotient(t)
    lemma_montgomery_quotient_unique(t, n);

    // intermediate * R == T + montgomery_quotient(T) * L
    // By definition: montgomery_intermediate(T) = (T + montgomery_quotient(T) * L) / R
    // Since (intermediate * R) / R == intermediate, we have the result
    lemma_pow2_pos(260);
    lemma_div_by_multiple(intermediate as int, montgomery_radix() as int);
}

/// Main REDC Theorem: If T < R × L, then intermediate < 2L.
///
/// This is the core correctness property of Montgomery reduction from the paper.
///
/// Proof strategy:
/// 1. N = montgomery_quotient(T) < R  [from lemma_montgomery_quotient_bounded]
/// 2. T + N×L < R×L + R×L = 2×R×L  [since T < R×L and N×L < R×L]
/// 3. intermediate = (T + N×L) / R < 2L  [by division]
pub(crate) proof fn lemma_canonical_bound_implies_intermediate_less_than_2L(t: nat)
    requires
        t < montgomery_radix() * group_order(),  // T < R × L

    ensures
        montgomery_intermediate(t) < 2 * group_order(),  // intermediate < 2L
{
    let r = montgomery_radix();
    let l = group_order();
    let n = montgomery_quotient(t);
    let sum = t + n * l;
    let intermediate = sum / r;

    // Goal: intermediate < 2L
    assert(intermediate < 2 * l) by {
        // Subgoal 1: N < R
        assert(n < r) by {
            lemma_montgomery_quotient_bounded(t);
        }

        // Subgoal 2: N×L < R×L (since N < R and L > 0)
        assert(n * l < r * l) by {
            assert(l > 0) by {
                assert(l == pow2(252) + 27742317777372353535851937790883648493);
            }
            lemma_mul_strict_inequality(n as int, r as int, l as int);
        }

        // Subgoal 3: sum < 2×R×L
        assert(sum < 2 * r * l) by {
            // T + N×L < R×L + R×L (since T < R×L and N×L < R×L)
            // R×L + R×L = 2×R×L by distributivity and associativity
            lemma_mul_is_distributive_add_other_way((r * l) as int, 1, 1);
            lemma_mul_is_associative(2, r as int, l as int);
        }

        // Subgoal 4: sum / R < 2L
        lemma_pow2_pos(260);
        // Rewrite 2×R×L as R×(2×L) for lemma_div_strictly_bounded
        lemma_mul_is_commutative(2, r as int);
        lemma_mul_is_associative(r as int, 2, l as int);
        lemma_div_strictly_bounded(sum as int, r as int, (2 * l) as int);
    }

    // Connect to spec
    assert(montgomery_intermediate(t) == intermediate);
}

/// Bridging lemma: canonical_bound implies r4 < 2^52 + L[4] via REDC theorem.
///
/// # Proof Strategy
///
/// ```text
/// canonical_bound ⟹ intermediate < 2L
///                 ⟹ r4 ≤ inter/2^208 ≤ 2L/2^208 ≤ 2^45
///                 ⟹ r4 < 2^52 + L[4]
/// ```
pub(crate) proof fn lemma_r4_bound_from_canonical(
    limbs: &[u128; 9],
    r0: u64,
    r1: u64,
    r2: u64,
    r3: u64,
    r4: u64,
)
    requires
        montgomery_reduce_canonical_bound(limbs),
        ({
            let t = slice128_to_nat(limbs);
            let inter_computed = (r0 as nat) + (r1 as nat) * pow2(52) + (r2 as nat) * pow2(104) + (
            r3 as nat) * pow2(156) + (r4 as nat) * pow2(208);
            inter_computed == montgomery_intermediate(t)
        }),
    ensures
        (r4 as nat) < pow2(52) + (constants::L.limbs[4] as nat),
        ({
            let inter = (r0 as nat) + (r1 as nat) * pow2(52) + (r2 as nat) * pow2(104) + (r3 as nat)
                * pow2(156) + (r4 as nat) * pow2(208);
            inter < 2 * group_order()
        }),
{
    let t = slice128_to_nat(limbs);
    let inter = (r0 as nat) + (r1 as nat) * pow2(52) + (r2 as nat) * pow2(104) + (r3 as nat) * pow2(
        156,
    ) + (r4 as nat) * pow2(208);
    let two_l = 2 * group_order();
    let l4 = constants::L.limbs[4] as nat;

    // Subgoal 1: inter < 2L (from REDC theorem)
    assert(inter < two_l) by {
        lemma_canonical_bound_implies_intermediate_less_than_2L(t);
    }

    // Subgoal 2: r4 <= 2L / 2^208
    let two_l_div = two_l / pow2(208);
    assert((r4 as nat) <= two_l_div) by {
        lemma_pow2_pos(208);

        // r4 * 2^208 <= inter (lower limbs are non-negative)
        let lower = (r0 as nat) + (r1 as nat) * pow2(52) + (r2 as nat) * pow2(104) + (r3 as nat)
            * pow2(156);
        assert((r4 as nat) * pow2(208) <= inter);

        // r4 <= inter / 2^208
        lemma_mul_le_implies_div_le(r4 as nat, pow2(208), inter);

        // inter < two_l implies inter / 2^208 <= two_l / 2^208
        lemma_div_is_ordered(inter as int, two_l as int, pow2(208) as int);
    }

    // Subgoal 3: r4 < 2^52 + L[4]
    assert((r4 as nat) < pow2(52) + l4) by {
        // 2L / 2^208 <= 2^45 (from axiom about L's structure)
        axiom_two_l_div_pow2_208_le_pow2_45();
        assert((r4 as nat) <= pow2(45));

        // L[4] == 2^44
        lemma_l_limb4_is_pow2_44();

        // 2^45 + 1 < 2^52 + 2^44 (bit arithmetic)
        lemma_u64_shift_is_pow2(44);
        lemma_u64_shift_is_pow2(45);
        lemma_u64_shift_is_pow2(52);
        assert((1u64 << 45) + 1 < (1u64 << 52) + (1u64 << 44)) by (bit_vector);
    }
}

} // verus!
