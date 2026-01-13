#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;
use super::super::common_lemmas::shift_lemmas::*;

use crate::backend::serial::u64::constants;
use crate::specs::field_specs_u64::*;

verus! {

// =============================================================================
// NOT IN VSTD YET - Kept for other lemmas in this file
// =============================================================================
pub broadcast proof fn lemma_u128_shl_is_mul(x: u128, shift: u128)
    requires
        0 <= shift < <u128>::BITS,
        x * pow2(shift as nat) <= <u128>::MAX,
    ensures
        #[trigger] (x << shift) == x * pow2(shift as nat),
{
    assume(false);
}

// =============================================================================
// Core Divisibility Lemma for part1
// =============================================================================
/// Core divisibility: (s + p * L[0]) % 2^52 = 0 where p = s * LFACTOR mod 2^52
///
/// This is the key insight of Montgomery reduction: LFACTOR * L[0] ≡ -1 (mod 2^52),
/// so p * L[0] ≡ s * (-1) ≡ -s, and s + p * L[0] ≡ 0.
pub(crate) proof fn lemma_part1_divisible(s: u64, p: nat)
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
    let p52: nat = 0x10000000000000nat;

    // Compute all derived values from sum
    let sum_low52: u64 = (sum as u64) & mask52;
    let product: u128 = ((sum_low52 as u128) * (constants::LFACTOR as u128)) as u128;
    let p: u64 = (product as u64) & mask52;
    let total: u128 = (sum + (p as u128) * (constants::L.limbs[0] as u128)) as u128;
    let carry: u128 = total >> 52;
    let L0 = constants::L.limbs[0] as nat;

    assert(pow2(52) == p52) by {
        lemma2_to64_rest();
    }

    // Goal 1: p < 2^52 (masking bounds the result)
    assert(p < (1u64 << 52)) by (bit_vector)
        requires
            p == (product as u64) & mask52,
            mask52 == 0xFFFFFFFFFFFFFu64,
    ;

    // Goal 2: total == carry << 52
    assert(total == carry << 52) by {
        // Step 1: sum_low52 < 2^52
        assert(sum_low52 < pow2(52)) by {
            assert(sum_low52 < 0x10000000000000u64) by (bit_vector)
                requires
                    sum_low52 == (sum as u64) & mask52,
                    mask52 == 0xFFFFFFFFFFFFFu64,
            ;
        }

        // Step 2: p == (sum_low52 * LFACTOR) % 2^52
        assert(p as nat == ((sum_low52 as nat) * (constants::LFACTOR as nat)) % pow2(52)) by {
            assert(((product as u64) & mask52) as u128 == product % 0x10000000000000u128)
                by (bit_vector)
                requires
                    mask52 == 0xFFFFFFFFFFFFFu64,
            ;
        }

        // Step 3: (sum_low52 + p*L[0]) % 2^52 == 0 [core divisibility]
        lemma_part1_divisible(sum_low52, p as nat);

        // Step 4: Extend to full sum - (sum + p*L[0]) % 2^52 == 0
        // First, prove no overflow
        assert((p as u128) * (constants::L.limbs[0] as u128) < (1u128 << 102)) by (bit_vector)
            requires
                p < 0x10000000000000u64,
                constants::L.limbs[0] < 0x4000000000000u64,
        ;
        assert(total as nat == (sum as nat) + (p as nat) * L0) by {
            assert(sum + (p as u128) * (constants::L.limbs[0] as u128) < u128::MAX) by (bit_vector)
                requires
                    sum < (1u128 << 108),
                    (p as u128) * (constants::L.limbs[0] as u128) < (1u128 << 102),
            ;
        }
        // Extension: sum ≡ sum_low52 (mod 2^52), so (sum + p*L[0]) ≡ (sum_low52 + p*L[0]) (mod 2^52)
        assert((total as nat) % pow2(52) == 0) by {
            assert(((sum as u64) & mask52) as u128 == sum % 0x10000000000000u128) by (bit_vector)
                requires
                    mask52 == 0xFFFFFFFFFFFFFu64,
            ;
            assert((sum as nat) % p52 == sum_low52 as nat);
            lemma_mod_add_eq(
                (sum as nat) as int,
                (sum_low52 as nat) as int,
                ((p as nat) * L0) as int,
                p52 as int,
            );
        }

        // Step 5: Shift round-trip
        // Since (total as nat) % pow2(52) == 0, we have (total >> 52) << 52 == total
        assert(pow2(52) == 0x10000000000000nat) by {
            lemma2_to64_rest();
        }
        assert((total >> 52u128) << 52u128 == total) by (bit_vector)
            requires
                total % 0x10000000000000u128 == 0,
        ;
    }
}

/// Helper function for part2 bounds (kept for completeness)
pub proof fn lemma_part2_bounds(sum: u128)
    ensures
        ({
            let carry = sum >> 52;
            let w = (sum as u64) & (((1u64 << 52) - 1) as u64);
            &&& w < (1u64 << 52)
            &&& sum == w + (carry << 52)
        }),
{
    let carry = sum >> 52;
    let w = (sum as u64) & (((1u64 << 52) - 1) as u64);

    assert(w < 1u64 << 52) by {
        assert((sum as u64) & (((1u64 << 52) - 1) as u64) < (1u64 << 52)) by (bit_vector);
    }

    assert(sum == w + (carry << 52)) by {
        let p52 = pow2(52);
        assert(p52 > 0) by {
            lemma_pow2_pos(52);
        }

        assert(sum == p52 * (sum as nat / p52) + sum as nat % p52) by {
            lemma_fundamental_div_mod(sum as int, p52 as int);
        }

        assert(sum >> 52 == sum as nat / p52) by {
            lemma_u128_shr_is_div(sum, 52);
        }
        assert(carry << 52 == p52 * (sum as nat / p52)) by {
            assert(carry << 52 == carry * p52) by {
                assert(carry * p52 <= u128::MAX) by {
                    assert((sum as nat / p52) * p52 <= sum <= u128::MAX) by {
                        assert((sum as nat / p52) * p52 == p52 * (sum as nat / p52)) by {
                            lemma_mul_is_commutative(p52 as int, (sum as nat / p52) as int);
                        }
                        assert(p52 * (sum as nat / p52) <= (p52 * sum) as nat / p52) by {
                            lemma_mul_hoist_inequality(p52 as int, sum as int, p52 as int);
                        }
                        assert((p52 * sum) as nat / p52 == sum) by {
                            lemma_div_multiples_vanish(sum as int, p52 as int);
                        }
                    }
                }
                lemma_u128_shl_is_mul(carry, 52);
            }
            lemma_mul_is_commutative(p52 as int, (sum as nat / p52) as int);
        }

        assert(w == sum as nat % p52) by {
            assert(((1u64 << 52) - 1) as u64 == low_bits_mask(52)) by {
                assert(1u64 << 52 == p52) by {
                    lemma_u64_shift_is_pow2(52);
                }
            }
            assert((sum as u64) & (low_bits_mask(52) as u64) == sum as u64 % (p52 as u64)) by {
                lemma_u64_low_bits_mask_is_mod(sum as u64, 52);
            }

            assert(sum as u64 % (p52 as u64) == sum as nat % p52) by {
                assert(p52 == 0x10000000000000) by {
                    lemma2_to64_rest();
                }
                assert(sum as u64 == sum % 0x10000000000000000) by (bit_vector);
                assert(sum % 0x10000000000000 == (sum % 0x10000000000000000) % 0x10000000000000)
                    by (bit_vector);
            }
        }
    }
}

} // verus!
