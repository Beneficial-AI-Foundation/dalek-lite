#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::calc;
use vstd::prelude::*;

use super::common_lemmas::div_mod_lemmas::*;
use super::common_lemmas::pow_lemmas::*;

use crate::specs::core_specs::*;

verus! {

pub proof fn u8_32_as_nat_le_pow2_256(bytes: &[u8; 32])
    ensures
        u8_32_as_nat(&bytes) < pow2(256),
        u8_32_as_nat(&bytes) == u8_32_as_nat(&bytes) % pow2(256),
{
    assert forall|i: nat| 0 <= i <= 31 implies #[trigger] bytes[i as int] * pow2(i * 8) <= pow2(
        (i + 1) * 8,
    ) - pow2(i * 8) by {
        let b = bytes[i as int];
        assert(b < pow2(8)) by {
            lemma_u8_lt_pow2_8(b);
        }
        lemma_pow2_mul_bound_general(b as nat, 8, i * 8);
        assert(i * 8 + 8 == (i + 1) * 8) by {
            lemma_mul_is_distributive_add_other_way(i as int, 1, 8);
        }
    }
    assert(pow2(0 * 8) == 1) by {
        lemma2_to64();
    }
    assert(u8_32_as_nat(&bytes) % pow2(256) == u8_32_as_nat(&bytes)) by {
        lemma_small_mod(u8_32_as_nat(&bytes), pow2(256));
    }
}

/// Encodes the contribution of the suffix bytes strictly above index `i` as a radix-256 sum.
/// The recurrence mirrors the one used by `pow2_sum`, making it easy to splice the two pieces together.
pub open spec fn bytes_suffix_sum(bytes: &[u8; 32], i: nat) -> nat
    decreases 32 - i,
{
    if i + 1 >= 32 {
        0
    } else {
        bytes[(i + 1) as int] as nat + pow2(8) * bytes_suffix_sum(bytes, i + 1)
    }
}

/// Single-step expansion of `pow2_sum`: adds the (i+1)-th byte weighted by its power-of-two chunk.
proof fn lemma_pow2_sum_step(bytes: &[u8; 32], i: nat)
    requires
        i + 1 < 32,
    ensures
        pow2_sum(bytes, 0, 8, i + 1) == pow2_sum(bytes, 0, 8, i) + bytes[(i + 1) as int] as nat
            * pow2((i + 1) * 8),
{
    reveal_with_fuel(pow2_sum, 1);
}

proof fn lemma_nat_lt_one_is_zero(x: nat)
    requires
        x < 1,
    ensures
        x == 0,
{
    assert(x == 0);
}

/// Splits the full radix-256 sum into a prefix up to `i` and the remaining suffix packed as a multiple of `pow2((i + 1) * 8)`.
/// The recursion mirrors `bytes_suffix_sum`, so the proof mainly re-associates the shared factors.
proof fn lemma_pow2_sum_split(bytes: &[u8; 32], i: nat)
    requires
        i < 32,
    ensures
        pow2_sum(bytes, 0, 8, 31) == pow2_sum(bytes, 0, 8, i) + pow2((i + 1) * 8)
            * bytes_suffix_sum(bytes, i),
    decreases 31 - i,
{
    if i == 31 {
        reveal_with_fuel(bytes_suffix_sum, 1);
        assert(bytes_suffix_sum(bytes, i) == 0);
    } else {
        lemma_pow2_sum_step(bytes, i);
        lemma_pow2_sum_split(bytes, i + 1);

        let prefix = pow2_sum(bytes, 0, 8, i);
        let suffix_next = bytes_suffix_sum(bytes, i + 1);
        let pow_chunk = pow2((i + 1) * 8);
        let pow_next = pow2((i + 2) * 8);

        reveal_with_fuel(bytes_suffix_sum, 1);
        assert(bytes_suffix_sum(bytes, i) == bytes[(i + 1) as int] as nat + pow2(8) * suffix_next);

        // Factor the (i + 1)-th byte out of the suffix so the remaining tail matches the induction hypothesis.
        assert(pow_next == pow_chunk * pow2(8)) by {
            lemma_pow2_adds((i + 1) * 8, 8);
        }

        calc! {
            (==)
            pow2_sum(bytes, 0, 8, 31); (==) {}
            pow2_sum(bytes, 0, 8, i + 1) + pow_next * suffix_next; (==) {}
            pow2_sum(bytes, 0, 8, i + 1) + pow_chunk * pow2(8) * suffix_next; (==) {
                assert(pow2_sum(bytes, 0, 8, i + 1) == prefix + bytes[(i + 1) as int] as nat
                    * pow_chunk);
            }
            prefix + bytes[(i + 1) as int] as nat * pow_chunk + pow_chunk * pow2(8)
                * suffix_next; (==) {
                lemma_mul_is_associative(pow_chunk as int, pow2(8) as int, suffix_next as int);
                lemma_mul_is_distributive_add_other_way(
                    pow_chunk as int,
                    bytes[(i + 1) as int] as int,
                    (pow2(8) * suffix_next) as int,
                );
            }
            prefix + pow_chunk * (bytes[(i + 1) as int] as nat + pow2(8) * suffix_next); (==) {
                reveal_with_fuel(bytes_suffix_sum, 1);
            }
            prefix + pow_chunk * bytes_suffix_sum(bytes, i);
        }
    }
}

/// Shows that dividing the partial radix-256 expansion by `pow2(i * 8)` recovers the digit at index `i`.
/// Strategy: bound the lower prefix so it vanishes when divided, then peel off the digit multiple.
pub proof fn lemma_pow2_sum_digit(bytes: &[u8; 32], i: usize)
    requires
        i < 32,
    ensures
        pow2_sum(bytes, 0, 8, i as nat) / pow2((i as nat) * 8) == bytes[i as int] as nat,
{
    if i == 0 {
        reveal_with_fuel(pow2_sum, 1);
        lemma_u8_lt_pow2_8(bytes[0]);
        assert(pow2(0) == 1) by {
            lemma2_to64();
        }
        assert(pow2_sum(bytes, 0, 8, 0) == bytes[0] as nat);
        assert(pow2_sum(bytes, 0, 8, 0) / pow2(0) == bytes[0] as nat);
    } else {
        let prev = (i - 1) as nat;
        lemma_pow2_sum_step(bytes, prev);
        let prefix = pow2_sum(bytes, 0, 8, prev);
        let pow_div = pow2((i as nat) * 8);

        assert forall|j: nat| 0 <= j <= prev ==> #[trigger] bytes[j as int] < pow2(8) by {
            lemma_u8_lt_pow2_8(bytes[j as int]);
        };
        // Bound the partial sum so it cannot spill into the block starting at index i.
        lemma_pow2_sum_bounds(bytes, 0, 8, prev);
        assert(prefix < pow_div);
        lemma_pow2_pos((i as nat) * 8);
        lemma_div_bound(prefix, (i as nat) * 8, (i as nat) * 8);
        assert(pow2(0) == 1) by {
            lemma2_to64();
        }
        assert(prefix / pow_div < 1);
        lemma_nat_lt_one_is_zero(prefix / pow_div);

        let idx_nat = i as nat;
        let idx_int = idx_nat as int;
        let digit = bytes[idx_int];

        lemma_bindary_sum_div_decomposition(prefix, digit as nat, (i as nat) * 8, (i as nat) * 8);
        lemma_u8_lt_pow2_8(digit);
        assert((digit as nat * pow_div) / pow_div == digit as nat) by {
            lemma_div_multiples_vanish(digit as int, pow_div as int);
        }

        assert(prev + 1 == idx_nat);
        assert(pow2((prev + 1) * 8) == pow_div) by {
            assert(prev + 1 == idx_nat);
        }
        assert(pow2_sum(bytes, 0, 8, idx_nat) == prefix + digit as nat * pow_div) by {
            assert(pow2_sum(bytes, 0, 8, prev + 1) == pow2_sum(bytes, 0, 8, prev) + bytes[(prev
                + 1) as int] as nat * pow2((prev + 1) * 8));
            assert(bytes[(prev + 1) as int] == digit);
            assert(pow2((prev + 1) * 8) == pow_div);
        }
        assert(pow2_sum(bytes, 0, 8, i as nat) == prefix + digit as nat * pow_div);
        assert(pow2_sum(bytes, 0, 8, i as nat) / pow_div == digit as nat);
    }
}

/// Relates the low `(i + 1)` bytes of `u8_32_as_nat` to `pow2_sum`: once the total is split, the suffix vanishes modulo `pow_chunk`.
proof fn lemma_as_nat_mod_prefix(bytes: &[u8; 32], i: nat)
    requires
        i < 32,
    ensures
        u8_32_as_nat(bytes) % pow2((i + 1) * 8) == pow2_sum(bytes, 0, 8, i),
{
    lemma_as_nat_equals_pow2_sum(bytes);
    lemma_pow2_sum_split(bytes, i);

    let total = u8_32_as_nat(bytes);
    let low = pow2_sum(bytes, 0, 8, i);
    let suffix = bytes_suffix_sum(bytes, i);
    let pow_chunk = pow2((i + 1) * 8);

    // Write the total value as a prefix plus a higher-order suffix multiple.
    assert(total == low + pow_chunk * suffix);

    assert forall|j: nat| 0 <= j <= i ==> #[trigger] bytes[j as int] < pow2(8) by {
        lemma_u8_lt_pow2_8(bytes[j as int]);
    };
    lemma_pow2_sum_bounds(bytes, 0, 8, i);
    assert(low < pow_chunk);

    lemma_small_mod(low, pow_chunk);
    assert(pow_chunk > 0) by {
        lemma_pow2_pos((i + 1) * 8);
    }
    lemma_mod_sum_factor(suffix as int, low as int, pow_chunk as int);
}

/// Tie the spec-level `u8_32_as_nat` definition to `pow2_sum` by unfolding one step on each side.
proof fn lemma_as_nat_equals_pow2_sum(bytes: &[u8; 32])
    ensures
        u8_32_as_nat(bytes) == pow2_sum(bytes, 0, 8, 31),
{
    assert(u8_32_as_nat(bytes) == pow2_sum(bytes, 0, 8, 31)) by {
        // Unfold a single step of each definition so their leading terms coincide.
        reveal_with_fuel(u8_32_as_nat, 1);
        assert(pow2(0) == 1) by {
            lemma2_to64();
        }
        assert(bytes[0] == bytes[0] * pow2(0)) by {
            lemma_mul_basics_3(bytes[0] as int);
        }
        reveal_with_fuel(pow2_sum, 32);
    };
}

/// Proves that `u8_32_as_nat` is injective: different byte arrays produce different natural numbers.
pub proof fn lemma_u8_32_as_nat_injective(a: &[u8; 32], b: &[u8; 32])
    requires
        a != b,
    ensures
        u8_32_as_nat(a) != u8_32_as_nat(b),
{
    // contradiction
    if u8_32_as_nat(a) == u8_32_as_nat(b) {
        assert forall|i: int| 0 <= i < 32 implies a[i] == b[i] by {
            lemma_u8_32_as_nat_digit_property(a, i as usize);
            lemma_u8_32_as_nat_digit_property(b, i as usize);

            let pow = pow2((i * 8) as nat);
            let a_digit = (u8_32_as_nat(a) / pow) % 256nat;
            let b_digit = (u8_32_as_nat(b) / pow) % 256nat;

            assert(a_digit == b_digit);
            assert(a[i] as nat == a_digit);
            assert(b[i] as nat == b_digit);
            assert(a[i] == b[i]);
        }
        assert(a =~= b);
        assert(false);
    }
}

/// Extracts the `i`-th byte from the radix-256 number `u8_32_as_nat(bytes)`.
/// We quotient away the lower chunk, show the prefix truncates to zero, and then peel off the digit multiple.
proof fn lemma_u8_32_as_nat_digit_property(bytes: &[u8; 32], i: usize)
    requires
        i < 32,
    ensures
        bytes[i as int] as nat == (u8_32_as_nat(bytes) / pow2((i * 8) as nat)) % 256nat,
{
    let i_nat = i as nat;
    let pow_div = pow2(i_nat * 8);
    let pow_chunk = pow2((i_nat + 1) * 8);
    let total = u8_32_as_nat(bytes);

    assert(pow2(8) == 256) by {
        lemma2_to64();
    }

    calc! {
        (==)
        (total / pow_div) % 256nat; (==) {
            assert(pow2(8) == 256);
        }
        (total / pow_div) % pow2(8); (==) {
            lemma_pow2_div_mod(total, i_nat * 8, 8);
        }
        (total % pow_chunk) / pow_div; (==) {
            lemma_as_nat_mod_prefix(bytes, i_nat);
        }
        pow2_sum(bytes, 0, 8, i_nat) / pow_div; (==) {
            lemma_pow2_sum_digit(bytes, i);
        }
        bytes[i as int] as nat;
    }
}

} // verus!
