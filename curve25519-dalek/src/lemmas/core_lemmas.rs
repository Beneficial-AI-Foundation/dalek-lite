#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use super::common_lemmas::mul_lemmas::*;
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

// ============================================================================
// Word-to-nat conversion lemmas
// ============================================================================
//
// NOTE: These lemmas are currently specialized for 8-word (64-byte) inputs,
// matching the from_bytes_wide use case. They could be made generic over
// array size if other use cases emerge (e.g., for 32-byte or 128-byte inputs).

/// Upper bound: result ≤ 2^(count×64) - 1
/// Note: Currently specialized for &[u64; 8]. Could be made generic over size N.
pub proof fn lemma_words_to_nat_upper_bound(words: &[u64; 8], count: int)
    requires
        0 <= count <= 8,
        forall|k: int| 0 <= k < 8 ==> words[k] < pow2(64),
    ensures
        words_to_nat_u64(words, count, 64) <= pow2((count * 64) as nat) - 1,
    decreases count,
{
    reveal_with_fuel(words_to_nat_gen, 9);

    if count == 0 {
        lemma2_to64();
    } else {
        let idx = count - 1;
        lemma_words_to_nat_upper_bound(words, idx);
        let word_val = words[idx] as nat;

        lemma_mul_upper_bound(
            word_val as int,
            (pow2(64) - 1) as int,
            pow2((idx * 64) as nat) as int,
            pow2((idx * 64) as nat) as int,
        );

        assert(words_to_nat_u64(words, count, 64) <= pow2((count * 64) as nat) - 1) by {
            let pow_prefix = pow2((idx * 64) as nat) as int;
            let pow64 = pow2(64) as int;
            let word_i = word_val as int;
            let prefix_i = words_to_nat_u64(words, idx, 64) as int;

            lemma_pow2_adds((idx * 64) as nat, 64);
            lemma_mul_is_distributive_sub(pow_prefix, pow64, word_i);
            lemma_mul_is_distributive_add(pow_prefix, pow64 - 1 - word_i, 1 as int);
        };
    }
}

/// Equivalence: words_to_nat on word array == words_from_bytes on underlying bytes
/// Note: Currently specialized for &[u64; 8] and &[u8; 64]. Could be made generic over size N.
pub proof fn lemma_words_to_nat_equals_bytes(
    words: &[u64; 8],
    bytes: &[u8; 64],
    count: int,
)
    requires
        0 <= count <= 8,
        forall|k: int| #![auto] 0 <= k < 8 ==> words@[k] as nat == word_from_bytes(bytes@, k),
    ensures
        words_to_nat_u64(words, count, 64) == words_from_bytes_to_nat(bytes@, count),
    decreases count,
{
    reveal_with_fuel(words_to_nat_gen, 9);
    reveal_with_fuel(words_from_bytes_to_nat, 9);
}

/// Expands to explicit 8-term sum (used for from_bytes_wide verification)
/// Note: This is inherently size-specific (explicit 8-term expansion).
/// For other sizes, similar expansion lemmas could be added as needed.
pub proof fn lemma_words_from_bytes_to_nat_wide(bytes: &[u8; 64])
    ensures
        words_from_bytes_to_nat(bytes@, 8) == word_from_bytes(bytes@, 0) + pow2(64) * word_from_bytes(
            bytes@,
            1,
        ) + pow2(128) * word_from_bytes(bytes@, 2) + pow2(192) * word_from_bytes(bytes@, 3) + pow2(
            256,
        ) * word_from_bytes(bytes@, 4) + pow2(320) * word_from_bytes(bytes@, 5) + pow2(384)
            * word_from_bytes(bytes@, 6) + pow2(448) * word_from_bytes(bytes@, 7),
{
    reveal_with_fuel(words_from_bytes_to_nat, 9);
    lemma2_to64();
    assert(words_from_bytes_to_nat(bytes@, 1) == words_from_bytes_to_nat(bytes@, 0) + word_from_bytes(
        bytes@,
        0,
    ) * pow2((0 * 64) as nat));
    // Reorder multiplications using commutativity
    assert(words_from_bytes_to_nat(bytes@, 8) == word_from_bytes(bytes@, 0) + pow2(64)
        * word_from_bytes(bytes@, 1) + pow2(128) * word_from_bytes(bytes@, 2) + pow2(192)
        * word_from_bytes(bytes@, 3) + pow2(256) * word_from_bytes(bytes@, 4) + pow2(320)
        * word_from_bytes(bytes@, 5) + pow2(384) * word_from_bytes(bytes@, 6) + pow2(448)
        * word_from_bytes(bytes@, 7)) by {
        broadcast use lemma_mul_is_commutative;

    };
}

} // verus!
