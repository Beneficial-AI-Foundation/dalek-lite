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
use super::common_lemmas::bit_lemmas::*;
#[allow(unused_imports)]
use super::common_lemmas::pow_lemmas::*;
#[allow(unused_imports)]
use super::common_lemmas::shift_lemmas::*;
#[allow(unused_imports)]
use super::field_lemmas::load8_lemmas::*;

#[allow(unused_imports)]
use super::scalar_lemmas::*;

verus! {

pub proof fn lemma_word_from_bytes_partial_step_last(bytes: &[u8; 64], word_idx: int)
    requires
        0 <= word_idx < 8,
    ensures
        word_from_bytes_partial(bytes, word_idx, 8) == word_from_bytes(bytes, word_idx),
        word_from_bytes_partial(bytes, word_idx, 8) == word_from_bytes_partial(bytes, word_idx, 7)
            + (bytes[(word_idx * 8 + 7) as int] as nat) * pow2((7 * 8) as nat),
{
    reveal_with_fuel(word_from_bytes_partial, 9);
}

pub proof fn lemma_word_from_bytes_matches_spec_load8(bytes: &[u8; 64], word_idx: int)
    requires
        0 <= word_idx < 8,
    ensures
        spec_load8_at(bytes, (word_idx * 8) as usize) == word_from_bytes(bytes, word_idx),
{
    let base = word_idx * 8;
    let idx = base as usize;
    // spec_load8_at uses pow2(k*8) * byte, word_from_bytes uses byte * pow2(k*8)
    // Show both equal the same combined value via commutativity
    let combined_load8 = pow2(0) * (bytes[(base + 0) as int] as nat)
        + pow2(8) * (bytes[(base + 1) as int] as nat)
        + pow2(16) * (bytes[(base + 2) as int] as nat)
        + pow2(24) * (bytes[(base + 3) as int] as nat)
        + pow2(32) * (bytes[(base + 4) as int] as nat)
        + pow2(40) * (bytes[(base + 5) as int] as nat)
        + pow2(48) * (bytes[(base + 6) as int] as nat)
        + pow2(56) * (bytes[(base + 7) as int] as nat);
    assert(spec_load8_at(bytes, idx) == combined_load8);
    assert(word_from_bytes(bytes, word_idx) == combined_load8);
}

pub proof fn lemma_bytes_wide_to_nat_rec_matches_word_partial(
    bytes: &[u8; 64],
    word_idx: int,
    upto: int,
)
    requires
        0 <= word_idx < 8,
        0 <= upto <= 8,
    ensures
        bytes_wide_to_nat_rec(bytes, word_idx * 8) == pow2(((word_idx * 8) * 8) as nat)
            * word_from_bytes_partial(bytes, word_idx, upto) + bytes_wide_to_nat_rec(
            bytes,
            word_idx * 8 + upto,
        ),
    decreases upto,
{
    let base = word_idx * 8;
    let pow_base = pow2((base * 8) as nat);
    if upto == 0 {
        assert(pow_base * 0 + bytes_wide_to_nat_rec(bytes, base + 0) == pow_base
            * word_from_bytes_partial(bytes, word_idx, 0) + bytes_wide_to_nat_rec(bytes, base + 0));
    } else {
        let prev = upto - 1;
        lemma_bytes_wide_to_nat_rec_matches_word_partial(bytes, word_idx, prev);
        if upto >= 8 {
            lemma_word_from_bytes_partial_step_last(bytes, word_idx);
        }

        let partial_prev = word_from_bytes_partial(bytes, word_idx, prev);
        let byte_val = bytes[(base + prev) as int] as nat;

        lemma_pow2_adds(((base * 8) as nat), ((prev * 8) as nat));

        // Rewriting byte_val * pow2((base + prev) * 8) = pow_base * byte_val * pow2(prev * 8)
        assert(byte_val * (pow_base * pow2((prev * 8) as nat)) == pow_base * byte_val
            * pow2((prev * 8) as nat)) by (nonlinear_arith);
        // Factor out pow_base
        assert(pow_base * partial_prev + pow_base * byte_val * pow2((prev * 8) as nat)
            == pow_base * (partial_prev + byte_val * pow2((prev * 8) as nat)))
            by (nonlinear_arith);
    }
}

pub proof fn lemma_bytes_wide_to_nat_rec_chunk(bytes: &[u8; 64], word_idx: int)
    requires
        0 <= word_idx < 8,
    ensures
        bytes_wide_to_nat_rec(bytes, word_idx * 8) == word_from_bytes(bytes, word_idx) * pow2(
            (word_idx * 64) as nat,
        ) + bytes_wide_to_nat_rec(bytes, (word_idx + 1) * 8),
{
    lemma_bytes_wide_to_nat_rec_matches_word_partial(bytes, word_idx, 8);
    lemma_mul_is_commutative(pow2((word_idx * 64) as nat) as int, word_from_bytes(bytes, word_idx) as int);
}

pub proof fn lemma_word_from_bytes_bound(bytes: &[u8; 64], word_idx: int)
    requires
        0 <= word_idx < 8,
    ensures
        word_from_bytes(bytes, word_idx) < pow2(64),
{
    let idx = (word_idx * 8) as usize;
    lemma_spec_load8_at_fits_u64(bytes, idx);
    lemma_word_from_bytes_matches_spec_load8(bytes, word_idx);
    assert(u64::MAX == pow2(64) - 1) by {
        lemma2_to64_rest();
    }
}

pub proof fn lemma_words_to_nat_gen_u64_bound_le(words: &[u64; 8], count: int)
    requires
        0 <= count <= 8,
        forall|k: int| 0 <= k < 8 ==> words[k] < pow2(64),
    ensures
        words_to_nat_gen_u64(words, count, 64) <= pow2((count * 64) as nat) - 1,
    decreases count,
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
            lemma_mul_is_distributive_sub(pow_prefix, pow64, word_i);
            lemma_mul_is_distributive_add(pow_prefix, pow64 - 1 - word_i, 1 as int);
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
    decreases count,
{
    reveal_with_fuel(words_to_nat_gen_u64, 9);
    reveal_with_fuel(words_from_bytes_to_nat, 9);
}

pub proof fn lemma_word_split_low4(word: u64)
    ensures
        pow2(4) * ((word >> 4) as nat) + (word & 0xf) as nat == word as nat,
{
    lemma_low_bits_mask_values();
    lemma_pow2_pos(4);
    lemma_u64_shr_is_div(word, 4);
    lemma_u64_low_bits_mask_is_mod(word, 4);
    lemma_shift_is_pow2(4);
}

pub proof fn lemma_words_from_bytes_to_nat_wide(bytes: &[u8; 64])
    ensures
        words_from_bytes_to_nat(bytes, 8) == word_from_bytes(bytes, 0) + pow2(64) * word_from_bytes(
            bytes,
            1,
        ) + pow2(128) * word_from_bytes(bytes, 2) + pow2(192) * word_from_bytes(bytes, 3) + pow2(
            256,
        ) * word_from_bytes(bytes, 4) + pow2(320) * word_from_bytes(bytes, 5) + pow2(384)
            * word_from_bytes(bytes, 6) + pow2(448) * word_from_bytes(bytes, 7),
{
    reveal_with_fuel(words_from_bytes_to_nat, 9);

    assert(pow2((0 * 64) as nat) == pow2(0));
    assert(pow2(0) == 1) by { lemma2_to64(); }

    assert(words_from_bytes_to_nat(bytes, 1) == words_from_bytes_to_nat(bytes, 0) + word_from_bytes(
        bytes,
        0,
    ) * pow2((0 * 64) as nat));

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
        five_limbs_to_nat_aux(*lo) == (words[0] as nat) + pow2(64) * (words[1] as nat) + pow2(128)
            * (words[2] as nat) + pow2(192) * (words[3] as nat) + pow2(256) * ((words[4]
            & 0xf) as nat),
{
    // Common mask equality used throughout
    assert((1u64 << 52) - 1u64 == u64::MAX >> 12) by (bit_vector);

    let masked_words_sum = ((words[0] & mask) as nat) + pow2(52) * ((((words[0] >> 52) | (words[1]
        << 12)) & mask) as nat) + pow2(104) * ((((words[1] >> 40) | (words[2] << 24))
        & mask) as nat) + pow2(156) * ((((words[2] >> 28) | (words[3] << 36)) & mask) as nat)
        + pow2(208) * ((((words[3] >> 16) | (words[4] << 48)) & mask) as nat);

    let unmasked_words_sum = (words[0] as nat) + pow2(64) * (words[1] as nat) + pow2(128) * (
    words[2] as nat) + pow2(192) * (words[3] as nat) + pow2(256) * ((words[4] & 0xf) as nat);

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
        let low40 = w1 & (u64::MAX >> 24);

        assert(((w0 >> 52) | (w1 << 12)) & (u64::MAX >> 12) == (w0 >> 52) | ((w1 & (u64::MAX >> 24))
            << 12)) by (bit_vector);
        assert((w0 >> 52) < (1u64 << 12)) by (bit_vector);
        assert((w1 & (u64::MAX >> 24)) <= u64::MAX >> 12) by (bit_vector);
        assert(((w0 >> 52) | ((w1 & (u64::MAX >> 24)) << 12)) < (1u64 << 52)) by (bit_vector);
        lemma_bit_or_is_plus(high12, low40, 12);
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(low40, 12, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(low40, 12);
    };
    // Limb 2 consists of word 1's top 24 bits and word 2's low 28 bits.
    assert(limb2 == w1_high + pow2(24) * w2_low) by {
        let w1 = words[1];
        let w2 = words[2];
        let high24 = w1 >> 40;
        let low28 = w2 & (u64::MAX >> 36);

        assert(((w1 >> 40) | (w2 << 24)) & (u64::MAX >> 12) == (w1 >> 40) | ((w2 & (u64::MAX >> 36))
            << 24)) by (bit_vector);
        assert((w1 >> 40) < (1u64 << 24)) by (bit_vector);
        assert((w2 & (u64::MAX >> 36)) <= u64::MAX >> 24) by (bit_vector);
        assert(((w1 >> 40) | ((w2 & (u64::MAX >> 36)) << 24)) < (1u64 << 52)) by (bit_vector);
        lemma_bit_or_is_plus(high24, low28, 24);
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(low28, 24, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(low28, 24);
    };
    // Limb 3 consists of word 2's top 36 bits and word 3's low 16 bits.
    assert(limb3 == w2_high + pow2(36) * w3_low) by {
        let w2 = words[2];
        let w3 = words[3];
        let high36 = w2 >> 28;
        let low16 = w3 & (u64::MAX >> 48);

        assert(((w2 >> 28) | (w3 << 36)) & (u64::MAX >> 12) == (w2 >> 28) | ((w3 & (u64::MAX >> 48))
            << 36)) by (bit_vector);
        assert((w2 >> 28) < (1u64 << 36)) by (bit_vector);
        assert((w3 & (u64::MAX >> 48)) <= u64::MAX >> 36) by (bit_vector);
        assert(((w2 >> 28) | ((w3 & (u64::MAX >> 48)) << 36)) < (1u64 << 52)) by (bit_vector);
        lemma_bit_or_is_plus(high36, low16, 36);
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(low16, 36, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(low16, 36);
    };
    // Limb 4 consists of word 3's top 48 bits and word 4's low 4 bits.
    assert(limb4 == w3_high + pow2(48) * w4_low) by {
        let w3 = words[3];
        let w4 = words[4];
        let high48 = w3 >> 16;
        let low4 = w4 & 0xf;

        assert(((w3 >> 16) | (w4 << 48)) & (u64::MAX >> 12) == (w3 >> 16) | ((w4 & 0xf) << 48))
            by (bit_vector);
        assert((w3 >> 16) < (1u64 << 48)) by (bit_vector);
        assert((w4 & 0xf) <= u64::MAX >> 48) by (bit_vector);
        assert(((w3 >> 16) | ((w4 & 0xf) << 48)) < (1u64 << 52)) by (bit_vector);
        lemma_bit_or_is_plus(high48, low4, 48);
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(low4, 48, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(low4, 48);
    };
    // Word 0 equals its low 52 bits plus its top 12 bits shifted by 52.
    assert(words[0] as nat == w0_low + pow2(52) * w0_high) by {
        let w0 = words[0];
        let high = w0 >> 52;
        let low = w0 & mask;

        assert((w0 & (u64::MAX >> 12)) < (1u64 << 52)) by (bit_vector);
        assert((w0 >> 52) <= u64::MAX >> 52) by (bit_vector);
        lemma_decompose(w0, mask);
        lemma_bit_or_is_plus(low, high, 52);

    };
    // Word 1's contribution at scale 2^64 equals its low 40 bits plus its high 24 bits.
    assert(pow2(64) * (words[1] as nat) == pow2(64) * w1_low + pow2(104) * w1_high) by {
        let w1 = words[1];
        let low = w1 & (u64::MAX >> 24);
        let high = w1 >> 40;

        assert((w1 & (u64::MAX >> 24)) < (1u64 << 40)) by (bit_vector);
        assert((w1 >> 40) <= u64::MAX >> 40) by (bit_vector);
        assert(w1 == (w1 & (u64::MAX >> 24)) | ((w1 >> 40) << 40)) by (bit_vector);
        lemma_bit_or_is_plus(low, high, 40);
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(high, 40, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(high, 40);
        assert(pow2(64) * (pow2(40) * w1_high) == pow2(104) * w1_high) by {
            assert(pow2(64) * (pow2(40) * w1_high) == (pow2(64) * pow2(40)) * w1_high)
                by (nonlinear_arith);
            lemma_pow2_adds(64, 40);
        }
        broadcast use group_mul_is_distributive;
    };
    // Word 2's contribution at scale 2^128 equals its low 28 bits plus its high 36 bits.
    assert(pow2(128) * (words[2] as nat) == pow2(128) * w2_low + pow2(156) * w2_high) by {
        let w2 = words[2];
        let low = w2 & (u64::MAX >> 36);
        let high = w2 >> 28;

        assert((w2 & (u64::MAX >> 36)) < (1u64 << 28)) by (bit_vector);
        assert((w2 >> 28) <= u64::MAX >> 28) by (bit_vector);
        assert(w2 == (w2 & (u64::MAX >> 36)) | ((w2 >> 28) << 28)) by (bit_vector);
        lemma_bit_or_is_plus(low, high, 28);
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(high, 28, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(high, 28);
        assert(pow2(128) * (pow2(28) * w2_high) == pow2(156) * w2_high) by {
            assert(pow2(128) * (pow2(28) * w2_high) == (pow2(128) * pow2(28)) * w2_high)
                by (nonlinear_arith);
            lemma_pow2_adds(128, 28);
        }
        broadcast use group_mul_is_distributive;
    };
    // Word 3's contribution at scale 2^192 equals its low 16 bits plus its high 48 bits.
    assert(pow2(192) * (words[3] as nat) == pow2(192) * w3_low + pow2(208) * w3_high) by {
        let w3 = words[3];
        let low = w3 & (u64::MAX >> 48);
        let high = w3 >> 16;

        assert((w3 & (u64::MAX >> 48)) < (1u64 << 16)) by (bit_vector);
        assert((w3 >> 16) <= u64::MAX >> 16) by (bit_vector);
        assert(w3 == (w3 & (u64::MAX >> 48)) | ((w3 >> 16) << 16)) by (bit_vector);
        lemma_bit_or_is_plus(low, high, 16);
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(high, 16, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(high, 16);
        assert(pow2(192) * (pow2(16) * w3_high) == pow2(208) * w3_high) by {
            assert(pow2(192) * (pow2(16) * w3_high) == (pow2(192) * pow2(16)) * w3_high)
                by (nonlinear_arith);
            lemma_pow2_adds(192, 16);
        }
        broadcast use group_mul_is_distributive;
    };

    assert(w0_low + pow2(52) * (w0_high + pow2(12) * w1_low) + pow2(104) * (w1_high + pow2(24)
        * w2_low) + pow2(156) * (w2_high + pow2(36) * w3_low) + pow2(208) * (w3_high + pow2(48)
        * w4_low) == unmasked_words_sum) by {
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
        five_limbs_to_nat_aux(*hi) == (words[4] >> 4) as nat + pow2(60) * (words[5] as nat) + pow2(
            124,
        ) * (words[6] as nat) + pow2(188) * (words[7] as nat),
{
    // Common mask equality used throughout
    assert((1u64 << 52) - 1u64 == u64::MAX >> 12) by (bit_vector);

    let limb0 = ((words[4] >> 4) & mask) as nat;
    let limb1 = (((words[4] >> 56) | (words[5] << 8)) & mask) as nat;
    let limb2 = (((words[5] >> 44) | (words[6] << 20)) & mask) as nat;
    let limb3 = (((words[6] >> 32) | (words[7] << 32)) & mask) as nat;
    let limb4 = (words[7] >> 20) as nat;

    let masked_words_sum = limb0 + pow2(52) * limb1 + pow2(104) * limb2 + pow2(156) * limb3 + pow2(
        208,
    ) * limb4;

    let unmasked_words_sum = (words[4] >> 4) as nat + pow2(60) * (words[5] as nat) + pow2(124) * (
    words[6] as nat) + pow2(188) * (words[7] as nat);

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
        let low44 = w5 & (u64::MAX >> 20);

        assert((w4 >> 56) < (1u64 << 8)) by (bit_vector);
        assert((w5 & (u64::MAX >> 20)) <= u64::MAX >> 8) by (bit_vector);
        assert(((w4 >> 56) | (w5 << 8)) & (u64::MAX >> 12) == (w4 >> 56) | ((w5 & (u64::MAX >> 20))
            << 8)) by (bit_vector);
        assert(((w4 >> 56) | ((w5 & (u64::MAX >> 20)) << 8)) < (1u64 << 52)) by (bit_vector);
        lemma_bit_or_is_plus(high8, low44, 8);
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(low44, 8, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(low44, 8);
    };

    // Limb 2 consists of word 5's top 20 bits and word 6's low 32 bits.
    assert(limb2 == w5_high + pow2(20) * w6_low) by {
        let w5 = words[5];
        let w6 = words[6];
        let high20 = w5 >> 44;
        let low32 = w6 & (u64::MAX >> 32);

        assert((w5 >> 44) < (1u64 << 20)) by (bit_vector);
        assert((w6 & (u64::MAX >> 32)) <= u64::MAX >> 20) by (bit_vector);
        assert(((w5 >> 44) | (w6 << 20)) & (u64::MAX >> 12) == (w5 >> 44) | ((w6 & (u64::MAX >> 32))
            << 20)) by (bit_vector);
        assert(((w5 >> 44) | ((w6 & (u64::MAX >> 32)) << 20)) < (1u64 << 52)) by (bit_vector);
        lemma_bit_or_is_plus(high20, low32, 20);
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(low32, 20, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(low32, 20);
    };

    // Limb 3 consists of word 6's top 32 bits and word 7's low 20 bits.
    assert(limb3 == w6_high + pow2(32) * w7_low) by {
        let w6 = words[6];
        let w7 = words[7];
        let high32 = w6 >> 32;
        let low20 = w7 & (u64::MAX >> 44);

        assert((w6 >> 32) < (1u64 << 32)) by (bit_vector);
        assert((w7 & (u64::MAX >> 44)) <= u64::MAX >> 32) by (bit_vector);
        assert(((w6 >> 32) | (w7 << 32)) & (u64::MAX >> 12) == (w6 >> 32) | ((w7 & (u64::MAX >> 44))
            << 32)) by (bit_vector);
        assert(((w6 >> 32) | ((w7 & (u64::MAX >> 44)) << 32)) < (1u64 << 52)) by (bit_vector);
        lemma_bit_or_is_plus(high32, low20, 32);
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(low20, 32, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(low20, 32);
    };

    // Limb 4 consists of word 7's top 44 bits.

    // Word 4 shifted by 4 equals limb 0 plus limb 1's contribution from word 4's high bits.
    assert((words[4] >> 4) as nat == limb0 + pow2(52) * w4_high) by {
        let w4 = words[4];
        let low52 = (w4 >> 4) & mask;
        let high8 = w4 >> 56;

        assert(((w4 >> 4) & (u64::MAX >> 12)) < (1u64 << 52)) by (bit_vector);
        assert(high8 <= u64::MAX >> 52) by {
            assert((w4 >> 56) <= u64::MAX >> 56) by (bit_vector);
            assert(u64::MAX >> 56 <= u64::MAX >> 52) by (bit_vector);
        }
        assert((w4 >> 4) == ((w4 >> 4) & (u64::MAX >> 12)) | ((w4 >> 56) << 52)) by (bit_vector);
        lemma_bit_or_is_plus(low52, high8, 52);
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(high8, 52, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(high8, 52);
    };

    // Word 5's contribution at scale 2^60 equals its low 44 bits plus its high 20 bits.
    assert(pow2(60) * (words[5] as nat) == pow2(60) * w5_low + pow2(104) * w5_high) by {
        let w5 = words[5];
        let low = w5 & (u64::MAX >> 20);
        let high = w5 >> 44;

        assert((w5 & (u64::MAX >> 20)) < (1u64 << 44)) by (bit_vector);
        assert((w5 >> 44) <= u64::MAX >> 44) by (bit_vector);
        assert(w5 == (w5 & (u64::MAX >> 20)) | ((w5 >> 44) << 44)) by (bit_vector);
        lemma_bit_or_is_plus(low, high, 44);
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(high, 44, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(high, 44);
        assert(pow2(60) * (pow2(44) * w5_high) == pow2(104) * w5_high) by {
            assert(pow2(60) * (pow2(44) * w5_high) == (pow2(60) * pow2(44)) * w5_high)
                by (nonlinear_arith);
            lemma_pow2_adds(60, 44);
        }
        broadcast use group_mul_is_distributive;
    };

    // Word 6's contribution at scale 2^124 equals its low 32 bits plus its high 32 bits.
    assert(pow2(124) * (words[6] as nat) == pow2(124) * w6_low + pow2(156) * w6_high) by {
        let w6 = words[6];
        let low = w6 & (u64::MAX >> 32);
        let high = w6 >> 32;

        assert((w6 & (u64::MAX >> 32)) < (1u64 << 32)) by (bit_vector);
        assert((w6 >> 32) <= u64::MAX >> 32) by (bit_vector);
        assert(w6 == (w6 & (u64::MAX >> 32)) | ((w6 >> 32) << 32)) by (bit_vector);
        lemma_bit_or_is_plus(low, high, 32);
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(high, 32, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(high, 32);
        assert(pow2(124) * (pow2(32) * w6_high) == pow2(156) * w6_high) by {
            assert(pow2(124) * (pow2(32) * w6_high) == (pow2(124) * pow2(32)) * w6_high)
                by (nonlinear_arith);
            lemma_pow2_adds(124, 32);
        }
        broadcast use group_mul_is_distributive;
    };

    // Word 7's contribution at scale 2^188 equals its low 20 bits plus its high 44 bits.
    assert(pow2(188) * (words[7] as nat) == pow2(188) * w7_low + pow2(208) * w7_high) by {
        let w7 = words[7];
        let low = w7 & (u64::MAX >> 44);
        let high = w7 >> 20;

        assert((w7 & (u64::MAX >> 44)) < (1u64 << 20)) by (bit_vector);
        assert((w7 >> 20) <= u64::MAX >> 20) by (bit_vector);
        assert(w7 == (w7 & (u64::MAX >> 44)) | ((w7 >> 20) << 20)) by (bit_vector);
        lemma_bit_or_is_plus(low, high, 20);
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(high, 20, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(high, 20);
        assert(pow2(188) * (pow2(20) * w7_high) == pow2(208) * w7_high) by {
            assert(pow2(188) * (pow2(20) * w7_high) == (pow2(188) * pow2(20)) * w7_high)
                by (nonlinear_arith);
            lemma_pow2_adds(188, 20);
        }
        broadcast use group_mul_is_distributive;
    };

    assert(limb0 + pow2(52) * (w4_high + pow2(8) * w5_low) + pow2(104) * (w5_high + pow2(20)
        * w6_low) + pow2(156) * (w6_high + pow2(32) * w7_low) + pow2(208) * w7_high
        == unmasked_words_sum) by {
        broadcast use group_mul_is_distributive;
        broadcast use lemma_mul_is_associative;

        lemma_pow2_adds(52, 8);
        lemma_pow2_adds(104, 20);
        lemma_pow2_adds(156, 32);
    };
    assert(masked_words_sum == unmasked_words_sum);
}

} // verus!
