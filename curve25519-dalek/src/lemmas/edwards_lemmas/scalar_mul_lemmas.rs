//! Lemmas for Edwards curve scalar multiplication
//!
//! This module contains proofs about scalar multiplication on Edwards curve points.
//!
//! ## Lemmas
//!
//! - `lemma_edwards_scalar_mul_pow2_succ`: Scalar multiplication by 2^(k+1) unfolds to doubling.
//! - `lemma_scalar_to_nat_basepoint_order_private_equals_group_order`: BASEPOINT_ORDER_PRIVATE
//!   encodes the group order ℓ.
#[cfg(verus_keep_ghost)]
use crate::constants;
#[cfg(verus_keep_ghost)]
use crate::lemmas::common_lemmas::pow_lemmas::{lemma_pow2_even, pow2_MUL_div};
#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::{edwards_double, edwards_scalar_mul};
#[cfg(verus_keep_ghost)]
use crate::specs::scalar52_specs::group_order;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar_specs::scalar_to_nat;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{
    lemma2_to64, lemma2_to64_rest, lemma_pow2_adds, lemma_pow2_pos, pow2,
};
use vstd::prelude::*;

verus! {

/// Lemma: scalar multiplication by a power-of-two exponent unfolds to a doubling.
///
/// For any point P and exponent k ≥ 0:
///   [2^(k+1)]P = double([2^k]P)
///
/// This is used to prove `mul_by_pow_2` correct by showing each doubling step
/// computes the next power-of-two multiple.
pub proof fn lemma_edwards_scalar_mul_pow2_succ(point_affine: (nat, nat), k: nat)
    ensures
        edwards_scalar_mul(point_affine, pow2(k + 1)) == {
            let half = edwards_scalar_mul(point_affine, pow2(k));
            edwards_double(half.0, half.1)
        },
{
    // Unfold one step of scalar multiplication at n = 2^(k+1).
    reveal_with_fuel(edwards_scalar_mul, 1);

    // pow2(k+1) is positive and even.
    lemma_pow2_pos(k + 1);
    lemma_pow2_even(k + 1);
    assert(pow2(k + 1) != 0);
    assert(pow2(k + 1) % 2 == 0);

    // pow2(k+1) / 2 == pow2(k).
    pow2_MUL_div(1, k + 1, 1);
    assert(pow2(1) == 2) by {
        lemma2_to64();
    }
    assert(pow2(k + 1) / 2 == pow2(k)) by {
        // From pow2_MUL_div: (1 * pow2(k+1)) / pow2(1) == 1 * pow2(k)
        assert((1 * pow2(k + 1)) / pow2(1) == pow2(k));
    }

    // Since pow2(k+1) is even and nonzero, it cannot be 1.
    assert(pow2(k + 1) != 1) by {
        assert(1nat % 2 == 1) by (compute);
    }

    // Now the even branch applies.
    assert(edwards_scalar_mul(point_affine, pow2(k + 1)) == {
        let half = edwards_scalar_mul(point_affine, (pow2(k + 1) / 2) as nat);
        edwards_double(half.0, half.1)
    });
}

/// BASEPOINT_ORDER_PRIVATE encodes the (prime) subgroup order ℓ in little-endian bytes.
///
/// This lemma bridges the byte-level constant to the `group_order()` nat used in specs.
/// The group order is: ℓ = 2^252 + 27742317777372353535851937790883648493
pub(crate) proof fn lemma_scalar_to_nat_basepoint_order_private_equals_group_order()
    ensures
        scalar_to_nat(&constants::BASEPOINT_ORDER_PRIVATE) == group_order(),
{
    // Expand the (little-endian) 32-byte constant into its nat value.
    //
    // bytes = [ed, d3, f5, 5c, 1a, 63, 12, 58, d6, 9c, f7, a2, de, f9, de, 14,
    //          00 .. 00, 10]
    let expanded: nat = 237nat * pow2(0) + 211nat * pow2(8) + 245nat * pow2(16) + 92nat * pow2(24)
        + 26nat * pow2(32) + 99nat * pow2(40) + 18nat * pow2(48) + 88nat * pow2(56) + 214nat * pow2(
        64,
    ) + 156nat * pow2(72) + 247nat * pow2(80) + 162nat * pow2(88) + 222nat * pow2(96) + 249nat
        * pow2(104) + 222nat * pow2(112) + 20nat * pow2(120) + 16nat * pow2(248);

    // Make the constant bytes available to SMT (compute can read the array, SMT typically won't).
    // Using the fully-qualified path avoids `compute_only` panicking on local variables.
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[0] == 0xed_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[1] == 0xd3_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[2] == 0xf5_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[3] == 0x5c_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[4] == 0x1a_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[5] == 0x63_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[6] == 0x12_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[7] == 0x58_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[8] == 0xd6_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[9] == 0x9c_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[10] == 0xf7_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[11] == 0xa2_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[12] == 0xde_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[13] == 0xf9_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[14] == 0xde_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[15] == 0x14_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[16] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[17] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[18] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[19] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[20] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[21] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[22] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[23] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[24] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[25] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[26] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[27] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[28] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[29] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[30] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[31] == 0x10_u8) by (compute_only);

    // Now the spec-level conversion agrees with our concrete expansion.
    assert(scalar_to_nat(&constants::BASEPOINT_ORDER_PRIVATE) == expanded);

    // Basic pow2 facts for the 64-bit word computations.
    assert(pow2(0) == 1) by {
        lemma2_to64();
    }
    assert(pow2(4) == 16) by {
        lemma2_to64();
    }
    assert(pow2(8) == 256) by {
        lemma2_to64();
    }
    assert(pow2(16) == 65536) by {
        lemma2_to64();
    }
    assert(pow2(24) == 16777216) by {
        lemma2_to64();
    }
    assert(pow2(32) == 4294967296) by {
        lemma2_to64();
    }
    assert(pow2(40) == 1099511627776) by {
        lemma2_to64_rest();
    }
    assert(pow2(48) == 281474976710656) by {
        lemma2_to64_rest();
    }
    assert(pow2(56) == 72057594037927936) by {
        lemma2_to64_rest();
    }

    // 2^64 = 2^56 * 2^8.
    assert(pow2(64) == 0x10000000000000000) by {
        lemma_pow2_adds(56, 8);
        assert(pow2(64) == pow2(56) * pow2(8));
    }

    // Split into two 64-bit words (low 128 bits) plus the top byte (bit 252 set).
    let word0: nat = 237nat * pow2(0) + 211nat * pow2(8) + 245nat * pow2(16) + 92nat * pow2(24)
        + 26nat * pow2(32) + 99nat * pow2(40) + 18nat * pow2(48) + 88nat * pow2(56);

    let word1: nat = 214nat * pow2(0) + 156nat * pow2(8) + 247nat * pow2(16) + 162nat * pow2(24)
        + 222nat * pow2(32) + 249nat * pow2(40) + 222nat * pow2(48) + 20nat * pow2(56);

    // The upper word is shifted by 64 bits in the full 256-bit value.
    let shifted_word1: nat = 214nat * pow2(64) + 156nat * pow2(72) + 247nat * pow2(80) + 162nat
        * pow2(88) + 222nat * pow2(96) + 249nat * pow2(104) + 222nat * pow2(112) + 20nat * pow2(
        120,
    );

    // Relate the shifted word to `word1 * 2^64` using pow2-addition identities.
    assert(shifted_word1 == word1 * pow2(64)) by {
        lemma_pow2_adds(64, 0);
        lemma_pow2_adds(64, 8);
        lemma_pow2_adds(64, 16);
        lemma_pow2_adds(64, 24);
        lemma_pow2_adds(64, 32);
        lemma_pow2_adds(64, 40);
        lemma_pow2_adds(64, 48);
        lemma_pow2_adds(64, 56);
    }

    // The high byte is 16 at position 248, i.e. 16 * 2^248 = 2^252.
    lemma_pow2_adds(4, 248);
    assert(pow2(252) == pow2(4) * pow2(248));
    assert(16nat * pow2(248) == pow2(252));

    // Evaluate the 64-bit words to concrete constants.
    let word0_num: nat = 237nat * 1nat + 211nat * 256nat + 245nat * 65536nat + 92nat * 16777216nat
        + 26nat * 4294967296nat + 99nat * 1099511627776nat + 18nat * 281474976710656nat + 88nat
        * 72057594037927936nat;
    assert(237nat * 1nat + 211nat * 256nat + 245nat * 65536nat + 92nat * 16777216nat + 26nat
        * 4294967296nat + 99nat * 1099511627776nat + 18nat * 281474976710656nat + 88nat
        * 72057594037927936nat == 0x5812631a5cf5d3ed_u64 as nat) by (compute_only);
    assert(word0 == word0_num);

    let word1_num: nat = 214nat * 1nat + 156nat * 256nat + 247nat * 65536nat + 162nat * 16777216nat
        + 222nat * 4294967296nat + 249nat * 1099511627776nat + 222nat * 281474976710656nat + 20nat
        * 72057594037927936nat;
    assert(214nat * 1nat + 156nat * 256nat + 247nat * 65536nat + 162nat * 16777216nat + 222nat
        * 4294967296nat + 249nat * 1099511627776nat + 222nat * 281474976710656nat + 20nat
        * 72057594037927936nat == 0x14def9dea2f79cd6_u64 as nat) by (compute_only);
    assert(word1 == word1_num);

    // Compute the low 128-bit constant c.
    assert(0x5812631a5cf5d3ed_u64 as nat + (0x14def9dea2f79cd6_u64 as nat) * 0x10000000000000000
        == 27742317777372353535851937790883648493nat) by (compute_only);
    assert(word0 + word1 * pow2(64) == 27742317777372353535851937790883648493nat);

    // Reconstruct expanded and conclude.
    assert(expanded == word0 + shifted_word1 + 16nat * pow2(248));
    assert(expanded == pow2(252) + 27742317777372353535851937790883648493nat);
    assert(group_order() == pow2(252) + 27742317777372353535851937790883648493nat);
    assert(scalar_to_nat(&constants::BASEPOINT_ORDER_PRIVATE) == group_order());
}

} // verus!
