#[allow(unused_imports)]
use super::super::specs::core_specs::*;
#[allow(unused_imports)]
use super::common_lemmas::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::constants;
#[allow(unused_imports)]
use crate::backend::serial::u64::scalar::Scalar52;
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs_u64::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
#[allow(unused_imports)]
use vstd::bits::*;
#[allow(unused_imports)]
use vstd::calc;
use vstd::prelude::*;

#[allow(unused_imports)]
use super::common_lemmas::shift_lemmas::*;
#[allow(unused_imports)]
use super::common_lemmas::bit_lemmas::*;
#[allow(unused_imports)]
use super::common_lemmas::pow_lemmas::*;

#[allow(unused_imports)]
use super::scalar_lemmas::*;

verus! {

pub proof fn lemma_word_from_bytes_partial_bound(bytes: &[u8; 64], word_idx: int, upto: int)
    requires
        0 <= word_idx < 8,
        0 <= upto <= 7,
    ensures
        word_from_bytes_partial(bytes, word_idx, upto) < pow2((upto * 8) as nat)
    decreases upto
{
    if upto <= 0 {
        assert(pow2(0) == 1) by {
            lemma_shift_is_pow2(0);
            assert(1u64 << 0 == 1) by (bit_vector);
        }
    } else {
        let prev = upto - 1;
        lemma_word_from_bytes_partial_bound(bytes, word_idx, prev);
        let prev_bound = pow2((prev * 8) as nat);
        let byte_val = bytes[(word_idx * 8 + prev) as int] as nat;

        assert(pow2(8) == 256) by {
            lemma_shift_is_pow2(8);
            assert(1u64 << 8 == 256) by (bit_vector);
        };

        lemma_mul_upper_bound(
            byte_val as int,
            (pow2(8) - 1) as int,
            prev_bound as int,
            prev_bound as int,
        );

        assert(pow2(8) * prev_bound == pow2(((prev + 1) * 8) as nat)) by {
            lemma_pow2_adds((prev * 8) as nat, 8);
        }
    }
}

pub proof fn lemma_word_from_bytes_partial_step_last(bytes: &[u8; 64], word_idx: int)
    requires
        0 <= word_idx < 8,
    ensures
        word_from_bytes_partial(bytes, word_idx, 8) == word_from_bytes(bytes, word_idx),
        word_from_bytes_partial(bytes, word_idx, 8) ==
            word_from_bytes_partial(bytes, word_idx, 7) +
            (bytes[(word_idx * 8 + 7) as int] as nat) * pow2((7 * 8) as nat)
{
    reveal_with_fuel(word_from_bytes_partial, 9);
}

pub proof fn lemma_from_bytes_wide_word_update(
    bytes: &[u8; 64],
    word_idx: int,
    byte_pos: int,
    old_word: u64,
    new_word: u64,
)
    requires
        0 <= word_idx < 8,
        0 <= byte_pos < 8,
        old_word as nat == word_from_bytes_partial(bytes, word_idx, byte_pos),
        new_word == old_word | ((bytes[(word_idx * 8 + byte_pos) as int] as u64) << (byte_pos * 8)),
    ensures
        new_word as nat == word_from_bytes_partial(bytes, word_idx, byte_pos + 1),
        byte_pos < 7 ==> new_word < (1u64 << (((byte_pos + 1) * 8) as u64)),
        byte_pos == 7 ==> new_word as nat == word_from_bytes_partial(bytes, word_idx, 8),
{
    let byte = bytes[(word_idx * 8 + byte_pos) as int];
    let byte_val = byte as u64;
    let shift_u64 = ((byte_pos as usize) * 8) as u64;
    let shift_nat = (byte_pos * 8) as nat;

    lemma_u8_times_pow2_fits_u64(byte, shift_nat);
    vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(byte_val, shift_u64, u64::MAX);

    lemma_word_from_bytes_partial_bound(bytes, word_idx, byte_pos);
    lemma_shift_is_pow2(shift_nat);

    lemma_bit_or_is_plus(old_word, byte_val, shift_u64);

    vstd::bits::lemma_u64_shl_is_mul(byte_val, shift_u64);

    if byte_pos < 7 {
        lemma_word_from_bytes_partial_bound(bytes, word_idx, byte_pos + 1);
        lemma_shift_is_pow2(((byte_pos + 1) * 8) as nat);
    } else {
        lemma_word_from_bytes_partial_step_last(bytes, word_idx);
    }
}

pub proof fn lemma_bytes_wide_to_nat_rec_matches_word_partial(bytes: &[u8; 64], word_idx: int, upto: int)
    requires
        0 <= word_idx < 8,
        0 <= upto <= 8,
    ensures
        bytes_wide_to_nat_rec(bytes, word_idx * 8) ==
            pow2(((word_idx * 8) * 8) as nat) * word_from_bytes_partial(bytes, word_idx, upto) +
            bytes_wide_to_nat_rec(bytes, word_idx * 8 + upto)
    decreases upto
{
    let base = word_idx * 8;
    let pow_base = pow2((base * 8) as nat);
    if upto == 0 {
        assert(pow_base * 0 + bytes_wide_to_nat_rec(bytes, base + 0) == pow_base * word_from_bytes_partial(bytes, word_idx, 0) + bytes_wide_to_nat_rec(bytes, base + 0));
    } else {
        let prev = upto - 1;
        lemma_bytes_wide_to_nat_rec_matches_word_partial(bytes, word_idx, prev);
        if upto < 8 {
        } else {
            lemma_word_from_bytes_partial_step_last(bytes, word_idx);
        }

        let partial_prev = word_from_bytes_partial(bytes, word_idx, prev);
        let byte_val = bytes[(base + prev) as int] as nat;

        lemma_pow2_adds(((base * 8) as nat), ((prev * 8) as nat));

        calc! {
            (==)
            pow_base * partial_prev + byte_val * pow2(((base + prev) * 8) as nat) + bytes_wide_to_nat_rec(bytes, base + upto); {
                assert(byte_val * (pow_base * pow2((prev * 8) as nat)) == pow_base * byte_val * pow2((prev * 8) as nat)) by (nonlinear_arith);
            }
            pow_base * partial_prev + pow_base * byte_val * pow2((prev * 8) as nat) + bytes_wide_to_nat_rec(bytes, base + upto); {
                assert(pow_base * partial_prev + pow_base * byte_val * pow2((prev * 8) as nat) == pow_base * (partial_prev + byte_val * pow2((prev * 8) as nat))) by (nonlinear_arith);
            }
            pow_base * word_from_bytes_partial(bytes, word_idx, upto) + bytes_wide_to_nat_rec(bytes, base + upto);
        }
    }
}

pub proof fn lemma_bytes_wide_to_nat_rec_chunk(bytes: &[u8; 64], word_idx: int)
    requires
        0 <= word_idx < 8,
    ensures
        bytes_wide_to_nat_rec(bytes, word_idx * 8) ==
            word_from_bytes(bytes, word_idx) * pow2((word_idx * 64) as nat) +
            bytes_wide_to_nat_rec(bytes, (word_idx + 1) * 8)
{
    lemma_bytes_wide_to_nat_rec_matches_word_partial(bytes, word_idx, 8);
    calc! {
        (==)
        pow2(((word_idx * 8) * 8) as nat) * word_from_bytes_partial(bytes, word_idx, 8) + bytes_wide_to_nat_rec(bytes, (word_idx + 1) * 8); {}
        pow2((word_idx * 64) as nat) * word_from_bytes(bytes, word_idx) + bytes_wide_to_nat_rec(bytes, (word_idx + 1) * 8); {}
        word_from_bytes(bytes, word_idx) * pow2((word_idx * 64) as nat) + bytes_wide_to_nat_rec(bytes, (word_idx + 1) * 8);
    }
}

pub proof fn lemma_word_from_bytes_bound(bytes: &[u8; 64], word_idx: int)
    requires
        0 <= word_idx < 8,
    ensures
        word_from_bytes(bytes, word_idx) < pow2(64)
{
    lemma_word_from_bytes_partial_bound(bytes, word_idx, 7);
    lemma_word_from_bytes_partial_step_last(bytes, word_idx);
    let last_byte = bytes[(word_idx * 8 + 7) as int] as nat;

    assert(pow2(8) == 256) by {
        lemma_shift_is_pow2(8);
        assert(1u64 << 8 == 256) by (bit_vector);
    };

    lemma_pow2_mul_bound_general(last_byte, 8, 56);
}

pub proof fn lemma_words_to_nat_gen_u64_bound_le(words: &[u64; 8], count: int)
    requires
        0 <= count <= 8,
        forall|k: int| 0 <= k < 8 ==> words[k] < pow2(64),
    ensures
        words_to_nat_gen_u64(words, count, 64) <= pow2((count * 64) as nat) - 1,
    decreases count
{
    reveal_with_fuel(words_to_nat_gen_u64, 9);

    if count == 0 {
        lemma2_to64();
    } else {
        let idx = count - 1;
        lemma_words_to_nat_gen_u64_bound_le(words, idx);
        let word_val = words[idx] as nat;

        lemma_mul_upper_bound(
            word_val as int,
            (pow2(64) - 1) as int,
            pow2((idx * 64) as nat) as int,
            pow2((idx * 64) as nat) as int,
        );

        assert(words_to_nat_gen_u64(words, count, 64) <= pow2((count * 64) as nat) - 1) by {
            let pow_prefix = pow2((idx * 64) as nat) as int;
            let pow64 = pow2(64) as int;
            let word_i = word_val as int;
            let prefix_i = words_to_nat_gen_u64(words, idx, 64) as int;

            lemma_pow2_adds((idx * 64) as nat, 64);

            calc! {
                (==)
                pow_prefix * pow64 - 1 - (word_i * pow_prefix + prefix_i); {}
                pow_prefix * pow64 - word_i * pow_prefix - (prefix_i + 1); {
                    lemma_mul_is_distributive_sub(pow_prefix, pow64, word_i);
                }
                pow_prefix * ((pow64 - 1 - word_i) + 1) - (prefix_i + 1); {
                    lemma_mul_is_distributive_add(pow_prefix, pow64 - 1 - word_i, 1 as int);
                }
                (pow64 - 1 - word_i) * pow_prefix + (pow_prefix - 1 - prefix_i);
            };
        };
    }
}

pub proof fn lemma_words_to_nat_gen_u64_prefix_matches_bytes(
    words: &[u64; 8],
    bytes: &[u8; 64],
    count: int,
)
    requires
        0 <= count <= 8,
        forall|k: int| 0 <= k < 8 ==> words@[k] as nat == word_from_bytes(bytes, k),
    ensures
        words_to_nat_gen_u64(words, count, 64) == words_from_bytes_to_nat(bytes, count),
    decreases count
{
    reveal_with_fuel(words_to_nat_gen_u64, 9);
    reveal_with_fuel(words_from_bytes_to_nat, 9);
}

pub proof fn lemma_word_split_low4(word: u64)
    ensures
        pow2(4) * ((word >> 4) as nat) + (word & 0xf) as nat == word as nat
{
    lemma_low_bits_mask_values();

    let pow4 = pow2(4);
    let mask: u64 = 0xf;

    lemma_pow2_pos(4);

    lemma_u64_shr_is_div(word, 4);
    lemma_u64_low_bits_mask_is_mod(word, 4);

    let remainder = word as nat % pow4;

    assert((word & mask) as nat == remainder) by {
        assert(word & mask == word % (1u64 << 4)) by {
            lemma_shift_is_pow2(4);
        };
        assert((word % (1u64 << 4)) as nat == word as nat % pow4) by {
            lemma_shift_is_pow2(4);
        }
    }
}

pub proof fn lemma_words_from_bytes_to_nat_wide(bytes: &[u8; 64])
    ensures
        words_from_bytes_to_nat(bytes, 8) ==
            word_from_bytes(bytes, 0) +
            pow2(64) * word_from_bytes(bytes, 1) +
            pow2(128) * word_from_bytes(bytes, 2) +
            pow2(192) * word_from_bytes(bytes, 3) +
            pow2(256) * word_from_bytes(bytes, 4) +
            pow2(320) * word_from_bytes(bytes, 5) +
            pow2(384) * word_from_bytes(bytes, 6) +
            pow2(448) * word_from_bytes(bytes, 7),
{
    reveal_with_fuel(words_from_bytes_to_nat, 9);

    assert(pow2((0 * 64) as nat) == pow2(0));
    assert(pow2(0) == 1) by {
        lemma_shift_is_pow2(0);
        assert(1u64 << 0 == 1u64) by (bit_vector);
    }

    assert(words_from_bytes_to_nat(bytes, 1) == words_from_bytes_to_nat(bytes, 0) + word_from_bytes(bytes, 0) * pow2((0 * 64) as nat));

    lemma_mul_is_commutative(word_from_bytes(bytes, 1) as int, pow2((1 * 64) as nat) as int);
    lemma_mul_is_commutative(word_from_bytes(bytes, 2) as int, pow2((2 * 64) as nat) as int);
    lemma_mul_is_commutative(word_from_bytes(bytes, 3) as int, pow2((3 * 64) as nat) as int);
    lemma_mul_is_commutative(word_from_bytes(bytes, 4) as int, pow2((4 * 64) as nat) as int);
    lemma_mul_is_commutative(word_from_bytes(bytes, 5) as int, pow2((5 * 64) as nat) as int);
    lemma_mul_is_commutative(word_from_bytes(bytes, 6) as int, pow2((6 * 64) as nat) as int);
    lemma_mul_is_commutative(word_from_bytes(bytes, 7) as int, pow2((7 * 64) as nat) as int);
}

pub proof fn lemma_low_limbs_encode_low_expr(lo: &[u64; 5], words: &[u64; 8], mask: u64)
    requires
        mask == (1u64 << 52) - 1u64,
        lo[0] == words[0] & mask,
        lo[1] == ((words[0] >> 52) | (words[1] << 12)) & mask,
        lo[2] == ((words[1] >> 40) | (words[2] << 24)) & mask,
        lo[3] == ((words[2] >> 28) | (words[3] << 36)) & mask,
        lo[4] == ((words[3] >> 16) | (words[4] << 48)) & mask,
    ensures
        five_limbs_to_nat_aux(*lo) ==
            (words[0] as nat) +
            pow2(64) * (words[1] as nat) +
            pow2(128) * (words[2] as nat) +
            pow2(192) * (words[3] as nat) +
            pow2(256) * ((words[4] & 0xf) as nat)
{
    let masked_words_sum =
        ((words[0] & mask) as nat) +
        pow2(52) * ((((words[0] >> 52) | (words[1] << 12)) & mask) as nat) +
        pow2(104) * ((((words[1] >> 40) | (words[2] << 24)) & mask) as nat) +
        pow2(156) * ((((words[2] >> 28) | (words[3] << 36)) & mask) as nat) +
        pow2(208) * ((((words[3] >> 16) | (words[4] << 48)) & mask) as nat);

    let unmasked_words_sum =
        (words[0] as nat) +
        pow2(64) * (words[1] as nat) +
        pow2(128) * (words[2] as nat) +
        pow2(192) * (words[3] as nat) +
        pow2(256) * ((words[4] & 0xf) as nat);

    let limb1 = (((words[0] >> 52) | (words[1] << 12)) & mask) as nat;
    let limb2 = (((words[1] >> 40) | (words[2] << 24)) & mask) as nat;
    let limb3 = (((words[2] >> 28) | (words[3] << 36)) & mask) as nat;
    let limb4 = (((words[3] >> 16) | (words[4] << 48)) & mask) as nat;

    let w0_low = ((words[0] & mask) as nat);
    let w0_high = (words[0] >> 52) as nat;

    let w1_low = ((words[1] & (u64::MAX >> 24)) as nat);
    let w1_high = (words[1] >> 40) as nat;
    let w2_low = ((words[2] & (u64::MAX >> 36)) as nat);
    let w2_high = (words[2] >> 28) as nat;
    let w3_low = ((words[3] & (u64::MAX >> 48)) as nat);
    let w3_high = (words[3] >> 16) as nat;
    let w4_low = (words[4] & 0xf) as nat;

    // Limb 1 consists of word 0's top 12 bits and word 1's low 40 bits.
    assert(limb1 == w0_high + pow2(12) * w1_low) by {
        let w0 = words[0];
        let w1 = words[1];
        let high12 = w0 >> 52;
        let low40_mask: u64 = u64::MAX >> 24;
        let low40 = w1 & low40_mask;

        assert((1u64 << 52) - 1u64 == u64::MAX >> 12) by (bit_vector);
        assert(((w0 >> 52) | (w1 << 12)) & (u64::MAX >> 12) == (w0 >> 52) | ((w1 & (u64::MAX >> 24)) << 12)) by (bit_vector);
        assert((w0 >> 52) < (1u64 << 12)) by (bit_vector);
        assert((w1 & (u64::MAX >> 24)) <= u64::MAX >> 12) by (bit_vector);

        assert(((w0 >> 52) | ((w1 & (u64::MAX >> 24)) << 12)) < (1u64 << 52)) by (bit_vector);
        lemma_bit_or_is_plus(high12, low40, 12);
        assert((low40 << 12) as nat == pow2(12) * (low40 as nat)) by {
            let shift_u64: u64 = 12;
            vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(low40, shift_u64, u64::MAX);
            vstd::bits::lemma_u64_shl_is_mul(low40, shift_u64);
        }
    };
    // Limb 2 consists of word 1's top 24 bits and word 2's low 28 bits.
    assert(limb2 == w1_high + pow2(24) * w2_low) by {
        let w1 = words[1];
        let w2 = words[2];
        let high24 = w1 >> 40;
        let low28_mask: u64 = u64::MAX >> 36;
        let low28 = w2 & low28_mask;

        assert((1u64 << 52) - 1u64 == u64::MAX >> 12) by (bit_vector);
        assert(((w1 >> 40) | (w2 << 24)) & (u64::MAX >> 12) == (w1 >> 40) | ((w2 & (u64::MAX >> 36)) << 24)) by (bit_vector);
        assert((w1 >> 40) < (1u64 << 24)) by (bit_vector);
        assert((w2 & (u64::MAX >> 36)) <= u64::MAX >> 24) by (bit_vector);

        assert(((w1 >> 40) | ((w2 & (u64::MAX >> 36)) << 24)) < (1u64 << 52)) by (bit_vector);
        lemma_bit_or_is_plus(high24, low28, 24);
        assert((low28 << 24) as nat == pow2(24) * (low28 as nat)) by {
            let shift_u64: u64 = 24;
            vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(low28, shift_u64, u64::MAX);
            vstd::bits::lemma_u64_shl_is_mul(low28, shift_u64);
        }
    };
    // Limb 3 consists of word 2's top 36 bits and word 3's low 16 bits.
    assert(limb3 == w2_high + pow2(36) * w3_low) by {
        let w2 = words[2];
        let w3 = words[3];
        let high36 = w2 >> 28;
        let low16_mask: u64 = u64::MAX >> 48;
        let low16 = w3 & low16_mask;

        assert((1u64 << 52) - 1u64 == u64::MAX >> 12) by (bit_vector);
        assert(((w2 >> 28) | (w3 << 36)) & (u64::MAX >> 12) == (w2 >> 28) | ((w3 & (u64::MAX >> 48)) << 36)) by (bit_vector);
        assert((w2 >> 28) < (1u64 << 36)) by (bit_vector);
        assert((w3 & (u64::MAX >> 48)) <= u64::MAX >> 36) by (bit_vector);

        assert(((w2 >> 28) | ((w3 & (u64::MAX >> 48)) << 36)) < (1u64 << 52)) by (bit_vector);
        lemma_bit_or_is_plus(high36, low16, 36);
        assert((low16 << 36) as nat == pow2(36) * (low16 as nat)) by {
            let shift_u64: u64 = 36;
            vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(low16, shift_u64, u64::MAX);
            vstd::bits::lemma_u64_shl_is_mul(low16, shift_u64);
        }
    };
    // Limb 4 consists of word 3's top 48 bits and word 4's low 4 bits.
    assert(limb4 == w3_high + pow2(48) * w4_low) by {
        let w3 = words[3];
        let w4 = words[4];
        let high48 = w3 >> 16;
        let low4 = w4 & 0xf;

        assert((1u64 << 52) - 1u64 == u64::MAX >> 12) by (bit_vector);
        assert(((w3 >> 16) | (w4 << 48)) & (u64::MAX >> 12) == (w3 >> 16) | ((w4 & 0xf) << 48)) by (bit_vector);
        assert((w3 >> 16) < (1u64 << 48)) by (bit_vector);
        assert((w4 & 0xf) <= u64::MAX >> 48) by (bit_vector);
        assert(((w3 >> 16) | ((w4 & 0xf) << 48)) < (1u64 << 52)) by (bit_vector);
        lemma_bit_or_is_plus(high48, low4, 48);
        assert((low4 << 48) as nat == pow2(48) * (low4 as nat)) by {
            let shift_u64: u64 = 48;
            vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(low4, shift_u64, u64::MAX);
            vstd::bits::lemma_u64_shl_is_mul(low4, shift_u64);
        }
    };
    // Word 0 equals its low 52 bits plus its top 12 bits shifted by 52.
    assert(words[0] as nat == w0_low + pow2(52) * w0_high) by {
        let w0 = words[0];
        let high = w0 >> 52;
        let low = w0 & mask;

        assert((1u64 << 52) - 1u64 == u64::MAX >> 12) by (bit_vector);
        assert((w0 & (u64::MAX >> 12)) < (1u64 << 52)) by (bit_vector);
        assert((w0 >> 52) <= u64::MAX >> 52) by (bit_vector);
        lemma_decompose(w0, mask);
        lemma_bit_or_is_plus(low, high, 52);

    };
    // Word 1's contribution at scale 2^64 equals its low 40 bits plus its high 24 bits.
    assert(pow2(64) * (words[1] as nat) == pow2(64) * w1_low + pow2(104) * w1_high) by {
        let w1 = words[1];
        let low_mask: u64 = u64::MAX >> 24;
        let low = w1 & low_mask;
        let high = w1 >> 40;

        assert((w1 & (u64::MAX >> 24)) < (1u64 << 40)) by (bit_vector);
        assert((w1 >> 40) <= u64::MAX >> 40) by (bit_vector);
        assert(w1 == (w1 & (u64::MAX >> 24)) | ((w1 >> 40) << 40)) by (bit_vector);
        lemma_bit_or_is_plus(low, high, 40);
        let shift_u64: u64 = 40;
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(high, shift_u64, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(high, shift_u64);
        assert(pow2(64) * (pow2(40) * w1_high) == pow2(104) * w1_high) by {
            assert(pow2(64) * (pow2(40) * w1_high) == (pow2(64) * pow2(40)) * w1_high) by (nonlinear_arith);
            lemma_pow2_adds(64, 40);
        }

        broadcast use group_mul_is_distributive;
    };
    // Word 2's contribution at scale 2^128 equals its low 28 bits plus its high 36 bits.
    assert(pow2(128) * (words[2] as nat) == pow2(128) * w2_low + pow2(156) * w2_high) by {
        let w2 = words[2];
        let low_mask: u64 = u64::MAX >> 36;
        let low = w2 & low_mask;
        let high = w2 >> 28;

        assert((w2 & (u64::MAX >> 36)) < (1u64 << 28)) by (bit_vector);
        assert((w2 >> 28) <= u64::MAX >> 28) by (bit_vector);
        assert(w2 == (w2 & (u64::MAX >> 36)) | ((w2 >> 28) << 28)) by (bit_vector);

        lemma_bit_or_is_plus(low, high, 28);
        let shift_u64: u64 = 28;
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(high, shift_u64, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(high, shift_u64);
        assert(pow2(128) * (pow2(28) * w2_high) == pow2(156) * w2_high) by {
            assert(pow2(128) * (pow2(28) * w2_high) == (pow2(128) * pow2(28)) * w2_high) by (nonlinear_arith);
            lemma_pow2_adds(128, 28);
        }

        broadcast use group_mul_is_distributive;
    };
    // Word 3's contribution at scale 2^192 equals its low 16 bits plus its high 48 bits.
    assert(pow2(192) * (words[3] as nat) == pow2(192) * w3_low + pow2(208) * w3_high) by {
        let w3 = words[3];
        let low_mask: u64 = u64::MAX >> 48;
        let low = w3 & low_mask;
        let high = w3 >> 16;

        assert((w3 & (u64::MAX >> 48)) < (1u64 << 16)) by (bit_vector);
        assert((w3 >> 16) <= u64::MAX >> 16) by (bit_vector);
        assert(w3 == (w3 & (u64::MAX >> 48)) | ((w3 >> 16) << 16)) by (bit_vector);

        lemma_bit_or_is_plus(low, high, 16);
        let shift_u64: u64 = 16;
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(high, shift_u64, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(high, shift_u64);
        assert(pow2(192) * (pow2(16) * w3_high) == pow2(208) * w3_high) by {
            assert(pow2(192) * (pow2(16) * w3_high) == (pow2(192) * pow2(16)) * w3_high) by (nonlinear_arith);
            lemma_pow2_adds(192, 16);
        }

        broadcast use group_mul_is_distributive;
    };

    assert(w0_low + pow2(52) * (w0_high + pow2(12) * w1_low) + pow2(104) * (w1_high + pow2(24) * w2_low) + pow2(156) * (w2_high + pow2(36) * w3_low) + pow2(208) * (w3_high + pow2(48) * w4_low) == unmasked_words_sum) by {
        broadcast use group_mul_is_distributive;
        broadcast use lemma_mul_is_associative;
        lemma_pow2_adds(52, 12);
        lemma_pow2_adds(104, 24);
        lemma_pow2_adds(156, 36);
        lemma_pow2_adds(208, 48);
    };
    assert(masked_words_sum == unmasked_words_sum);
}

pub proof fn lemma_high_limbs_encode_high_expr(hi: &[u64; 5], words: &[u64; 8], mask: u64)
    requires
        mask == (1u64 << 52) - 1u64,
        hi[0] == (words[4] >> 4) & mask,
        hi[1] == ((words[4] >> 56) | (words[5] << 8)) & mask,
        hi[2] == ((words[5] >> 44) | (words[6] << 20)) & mask,
        hi[3] == ((words[6] >> 32) | (words[7] << 32)) & mask,
        hi[4] == words[7] >> 20,
    ensures
        five_limbs_to_nat_aux(*hi) ==
            (words[4] >> 4) as nat +
            pow2(60) * (words[5] as nat) +
            pow2(124) * (words[6] as nat) +
            pow2(188) * (words[7] as nat)

{
    let limb0 = ((words[4] >> 4) & mask) as nat;
    let limb1 = (((words[4] >> 56) | (words[5] << 8)) & mask) as nat;
    let limb2 = (((words[5] >> 44) | (words[6] << 20)) & mask) as nat;
    let limb3 = (((words[6] >> 32) | (words[7] << 32)) & mask) as nat;
    let limb4 = (words[7] >> 20) as nat;

    let masked_words_sum =
        limb0 +
        pow2(52) * limb1 +
        pow2(104) * limb2 +
        pow2(156) * limb3 +
        pow2(208) * limb4;

    let unmasked_words_sum =
        (words[4] >> 4) as nat +
        pow2(60) * (words[5] as nat) +
        pow2(124) * (words[6] as nat) +
        pow2(188) * (words[7] as nat);

    let w4_high = (words[4] >> 56) as nat;
    let w5_low = (words[5] & (u64::MAX >> 20)) as nat;
    let w5_high = (words[5] >> 44) as nat;
    let w6_low = (words[6] & (u64::MAX >> 32)) as nat;
    let w6_high = (words[6] >> 32) as nat;
    let w7_low = (words[7] & (u64::MAX >> 44)) as nat;
    let w7_high = (words[7] >> 20) as nat;

    // Limb 0 consists of word 4's bits 4 through 55.

    // Limb 1 consists of word 4's top 8 bits and word 5's low 44 bits.
    assert(limb1 == w4_high + pow2(8) * w5_low) by {
        let w4 = words[4];
        let w5 = words[5];
        let high8 = w4 >> 56;
        let low44_mask: u64 = u64::MAX >> 20;
        let low44 = w5 & low44_mask;

        assert((w4 >> 56) < (1u64 << 8)) by (bit_vector);
        assert((w5 & (u64::MAX >> 20)) <= u64::MAX >> 8) by (bit_vector);
        assert((1u64 << 52) - 1u64 == u64::MAX >> 12) by (bit_vector);

        assert(((w4 >> 56) | (w5 << 8)) & (u64::MAX >> 12) == (w4 >> 56) | ((w5 & (u64::MAX >> 20)) << 8)) by (bit_vector);
        assert(((w4 >> 56) | ((w5 & (u64::MAX >> 20)) << 8)) < (1u64 << 52)) by (bit_vector);
        lemma_bit_or_is_plus(high8, low44, 8);
        assert((low44 << 8) as nat == pow2(8) * (low44 as nat)) by {
            let shift_u64: u64 = 8;
            vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(low44, shift_u64, u64::MAX);
            vstd::bits::lemma_u64_shl_is_mul(low44, shift_u64);
        }
    };

    // Limb 2 consists of word 5's top 20 bits and word 6's low 32 bits.
    assert(limb2 == w5_high + pow2(20) * w6_low) by {
        let w5 = words[5];
        let w6 = words[6];
        let high20 = w5 >> 44;
        let low32_mask: u64 = u64::MAX >> 32;
        let low32 = w6 & low32_mask;

        assert((w5 >> 44) < (1u64 << 20)) by (bit_vector);
        assert((w6 & (u64::MAX >> 32)) <= u64::MAX >> 20) by (bit_vector);
        assert((1u64 << 52) - 1u64 == u64::MAX >> 12) by (bit_vector);

        assert(((w5 >> 44) | (w6 << 20)) & (u64::MAX >> 12) == (w5 >> 44) | ((w6 & (u64::MAX >> 32)) << 20)) by (bit_vector);
        assert(((w5 >> 44) | ((w6 & (u64::MAX >> 32)) << 20)) < (1u64 << 52)) by (bit_vector);
        lemma_bit_or_is_plus(high20, low32, 20);
        assert((low32 << 20) as nat == pow2(20) * (low32 as nat)) by {
            let shift_u64: u64 = 20;
            vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(low32, shift_u64, u64::MAX);
            vstd::bits::lemma_u64_shl_is_mul(low32, shift_u64);
        }
    };

    // Limb 3 consists of word 6's top 32 bits and word 7's low 20 bits.
    assert(limb3 == w6_high + pow2(32) * w7_low) by {
        let w6 = words[6];
        let w7 = words[7];
        let high32 = w6 >> 32;
        let low20_mask: u64 = u64::MAX >> 44;
        let low20 = w7 & low20_mask;

        assert((w6 >> 32) < (1u64 << 32)) by (bit_vector);
        assert((w7 & (u64::MAX >> 44)) <= u64::MAX >> 32) by (bit_vector);
        assert((1u64 << 52) - 1u64 == u64::MAX >> 12) by (bit_vector);

        assert(((w6 >> 32) | (w7 << 32)) & (u64::MAX >> 12) == (w6 >> 32) | ((w7 & (u64::MAX >> 44)) << 32)) by (bit_vector);
        assert(((w6 >> 32) | ((w7 & (u64::MAX >> 44)) << 32)) < (1u64 << 52)) by (bit_vector);
        lemma_bit_or_is_plus(high32, low20, 32);
        assert((low20 << 32) as nat == pow2(32) * (low20 as nat)) by {
            let shift_u64: u64 = 32;
            vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(low20, shift_u64, u64::MAX);
            vstd::bits::lemma_u64_shl_is_mul(low20, shift_u64);
        }
    };

    // Limb 4 consists of word 7's top 44 bits.

    // Word 4 shifted by 4 equals limb 0 plus limb 1's contribution from word 4's high bits.
    assert((words[4] >> 4) as nat == limb0 + pow2(52) * w4_high) by {
        let w4 = words[4];
        let low52 = (w4 >> 4) & mask;
        let high8 = w4 >> 56;

        assert((1u64 << 52) - 1u64 == u64::MAX >> 12) by (bit_vector);
        assert(((w4 >> 4) & (u64::MAX >> 12)) < (1u64 << 52)) by (bit_vector);
        assert(high8 <= u64::MAX >> 52) by {
            assert((w4 >> 56) <= u64::MAX >> 56) by (bit_vector);
            assert(u64::MAX >> 56 <= u64::MAX >> 52) by (bit_vector);
        }
        assert((w4 >> 4) == ((w4 >> 4) & (u64::MAX >> 12)) | ((w4 >> 56) << 52)) by (bit_vector);
        lemma_bit_or_is_plus(low52, high8, 52);
        assert(((high8 << 52) as nat) == pow2(52) * (high8 as nat)) by {
            let shift_u64: u64 = 52;
            vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(high8, shift_u64, u64::MAX);
            vstd::bits::lemma_u64_shl_is_mul(high8, shift_u64);
        }
    };

    // Word 5's contribution at scale 2^60 equals its low 44 bits plus its high 20 bits.
    assert(pow2(60) * (words[5] as nat) == pow2(60) * w5_low + pow2(104) * w5_high) by {
        let w5 = words[5];
        let low_mask: u64 = u64::MAX >> 20;
        let low = w5 & low_mask;
        let high = w5 >> 44;

        assert((w5 & (u64::MAX >> 20)) < (1u64 << 44)) by (bit_vector);
        assert((w5 >> 44) <= u64::MAX >> 44) by (bit_vector);
        assert(w5 == (w5 & (u64::MAX >> 20)) | ((w5 >> 44) << 44)) by (bit_vector);
        lemma_bit_or_is_plus(low, high, 44);
        let shift_u64: u64 = 44;
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(high, shift_u64, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(high, shift_u64);

        assert(pow2(60) * (pow2(44) * w5_high) == pow2(104) * w5_high) by {
            assert(pow2(60) * (pow2(44) * w5_high) == (pow2(60) * pow2(44)) * w5_high) by (nonlinear_arith);
            lemma_pow2_adds(60, 44);
        }

        assert(pow2(60) * (w5_low + pow2(44) * w5_high) == pow2(60) * w5_low + pow2(104) * w5_high) by {
            broadcast use group_mul_is_distributive;
        };
    };

    // Word 6's contribution at scale 2^124 equals its low 32 bits plus its high 32 bits.
    assert(pow2(124) * (words[6] as nat) == pow2(124) * w6_low + pow2(156) * w6_high) by {
        let w6 = words[6];
        let low_mask: u64 = u64::MAX >> 32;
        let low = w6 & low_mask;
        let high = w6 >> 32;

        assert((w6 & (u64::MAX >> 32)) < (1u64 << 32)) by (bit_vector);
        assert((w6 >> 32) <= u64::MAX >> 32) by (bit_vector);
        assert(w6 == (w6 & (u64::MAX >> 32)) | ((w6 >> 32) << 32)) by (bit_vector);
        lemma_bit_or_is_plus(low, high, 32);

        let shift_u64: u64 = 32;
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(high, shift_u64, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(high, shift_u64);

        assert(pow2(124) * (pow2(32) * w6_high) == pow2(156) * w6_high) by {
            assert(pow2(124) * (pow2(32) * w6_high) == (pow2(124) * pow2(32)) * w6_high) by (nonlinear_arith);
            lemma_pow2_adds(124, 32);
        }

        assert(pow2(124) * (w6_low + pow2(32) * w6_high) == pow2(124) * w6_low + pow2(156) * w6_high) by {
            broadcast use group_mul_is_distributive;
        };
    };

    // Word 7's contribution at scale 2^188 equals its low 20 bits plus its high 44 bits.
    assert(pow2(188) * (words[7] as nat) == pow2(188) * w7_low + pow2(208) * w7_high) by {
        let w7 = words[7];
        let low_mask: u64 = u64::MAX >> 44;
        let low = w7 & low_mask;
        let high = w7 >> 20;

        assert((w7 & (u64::MAX >> 44)) < (1u64 << 20)) by (bit_vector);
        assert((w7 >> 20) <= u64::MAX >> 20) by (bit_vector);
        assert(w7 == (w7 & (u64::MAX >> 44)) | ((w7 >> 20) << 20)) by (bit_vector);

        lemma_bit_or_is_plus(low, high, 20);
        let shift_u64: u64 = 20;
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(high, shift_u64, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(high, shift_u64);

        assert(pow2(188) * (pow2(20) * w7_high) == pow2(208) * w7_high) by {
            assert(pow2(188) * (pow2(20) * w7_high) == (pow2(188) * pow2(20)) * w7_high) by (nonlinear_arith);
            lemma_pow2_adds(188, 20);
        }

        assert(pow2(188) * (w7_low + pow2(20) * w7_high) == pow2(188) * w7_low + pow2(208) * w7_high) by {
            broadcast use group_mul_is_distributive;
        };
    };

    assert(limb0 + pow2(52) * (w4_high + pow2(8) * w5_low) + pow2(104) * (w5_high + pow2(20) * w6_low) + pow2(156) * (w6_high + pow2(32) * w7_low) + pow2(208) * w7_high == unmasked_words_sum) by {
        broadcast use group_mul_is_distributive;
        broadcast use lemma_mul_is_associative;
        lemma_pow2_adds(52, 8);
        lemma_pow2_adds(104, 20);
        lemma_pow2_adds(156, 32);
    };
    assert(masked_words_sum == unmasked_words_sum);
}

} // verus!
