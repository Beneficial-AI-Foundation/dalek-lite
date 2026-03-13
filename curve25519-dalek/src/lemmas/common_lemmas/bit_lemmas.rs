#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::mask_lemmas::*;
use super::pow_lemmas::*;
use super::shift_lemmas::*;

// Proofs that bitwise or with zero returns the other value
macro_rules! lemma_bitwise_or_zero_is_id {
    ($name:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "Proof that for any `x` of type "]
        #[doc = stringify!($uN)]
        #[doc = ", both `x | 0` and `0 | x` equal x."]
        pub broadcast proof fn $name(x: $uN)
            ensures
                #![trigger x | 0, 0 | x]
                x | 0 == x,
                0 | x == x,
        {
            assert(x | 0 == x) by (bit_vector);
            assert(0 | x == x) by (bit_vector);
        }
    }
    };
}

lemma_bitwise_or_zero_is_id!(lemma_u8_bitwise_or_zero_is_id, u8);
lemma_bitwise_or_zero_is_id!(lemma_u16_bitwise_or_zero_is_id, u16);
lemma_bitwise_or_zero_is_id!(lemma_u32_bitwise_or_zero_is_id, u32);
lemma_bitwise_or_zero_is_id!(lemma_u64_bitwise_or_zero_is_id, u64);
lemma_bitwise_or_zero_is_id!(lemma_u128_bitwise_or_zero_is_id, u128);

// Proofs that bitwise disjunction for N-bit integers equals addition if for some `n` one factor
// only uses the top `N-n` bits, and the other the low `n` bits.
macro_rules! lemma_bit_or_is_plus {
    ($name:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "Proof that for any `a`, `b` and `k` of type "]
        #[doc = stringify!($uN)]
        #[doc = ", `a | (b << k)` equals `a + (b << k)` if `a` is smaller than `2^k` and `b << k` does not overflow."]
        pub proof fn $name(a: $uN, b: $uN, k: $uN)
            by (bit_vector)
            requires
                k < <$uN>::BITS,
                a < (1 as $uN) << k,
                b <= (<$uN>::MAX >> k),
            ensures
                a | (b << k) == a + (b << k)
            {}
    }
    };
}

lemma_bit_or_is_plus!(lemma_u8_bit_or_is_plus, u8);
lemma_bit_or_is_plus!(lemma_u16_bit_or_is_plus, u16);
lemma_bit_or_is_plus!(lemma_u32_bit_or_is_plus, u32);
lemma_bit_or_is_plus!(lemma_u64_bit_or_is_plus, u64);
lemma_bit_or_is_plus!(lemma_u128_bit_or_is_plus, u128);

// Proofs that right-shifting and masking distribute over bitwise disjunction
macro_rules! lemma_distribute_over_bit_or {
    ($name:ident, $no_overflow:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "Proof that for any `a`, `b` and `k` of type "]
        #[doc = stringify!($uN)]
        #[doc = ", `(a | b) >> c` equals `(a >> c) | (b >> c)` and `(a | b) & M` equals `(a & M) | (b & M)` for `M = low_bits_mask(c)`."]
        pub proof fn $name(a: $uN, b: $uN, c: $uN)
            requires
                c < <$uN>::BITS,
            ensures
                (a | b) >> c == (a >> c) | (b >> c),
                (a | b) & (low_bits_mask(c as nat) as $uN) ==
                (a & (low_bits_mask(c as nat) as $uN)) |
                (b & (low_bits_mask(c as nat) as $uN)),
            {
                assert(low_bits_mask(c as nat) <= $uN::MAX) by {
                    $no_overflow(c as nat);
                }
                assert((a | b) >> c == (a >> c) | (b >> c)) by (bit_vector);
                let lbm = (low_bits_mask(c as nat) as $uN);
                assert((a | b) & lbm == (a & lbm) | (b & lbm)) by (bit_vector);
            }
    }
    };
}

lemma_distribute_over_bit_or!(
    lemma_u8_distribute_over_bit_or,
    lemma_u8_low_bits_masks_fit,
    u8
);
lemma_distribute_over_bit_or!(
    lemma_u16_distribute_over_bit_or,
    lemma_u16_low_bits_masks_fit,
    u16
);
lemma_distribute_over_bit_or!(
    lemma_u32_distribute_over_bit_or,
    lemma_u32_low_bits_masks_fit,
    u32
);
lemma_distribute_over_bit_or!(
    lemma_u64_distribute_over_bit_or,
    lemma_u64_low_bits_masks_fit,
    u64
);

// =============================================================================
// Single-bit mask helpers for u8
// =============================================================================
#[cfg(verus_keep_ghost)]
verus! {

/// Spec function wrapping single-bit test; usable as a quantifier trigger.
pub open spec fn mask_bit(mask: u8, j: int) -> bool {
    (mask & (1u8 << (j as u8))) != 0
}

/// OR-ing `val << pos` into `mask` preserves existing bits at other positions
/// and sets bit `pos` iff `val == 1`.
pub proof fn lemma_or_bit(mask: u8, val: u8, pos: u8, j: u8)
    requires
        pos < 8,
        j < 8,
        val == 0 || val == 1,
    ensures
        j != pos ==> ((mask | (val << pos)) & (1u8 << j)) == (mask & (1u8 << j)),
        j == pos ==> (((mask | (val << pos)) & (1u8 << j)) != 0) == ((mask & (1u8 << j)) != 0 || val
            == 1u8),
{
    if j != pos {
        assert(((mask | (val << pos)) & (1u8 << j)) == (mask & (1u8 << j))) by (bit_vector)
            requires
                pos < 8u8,
                j < 8u8,
                val == 0u8 || val == 1u8,
                j != pos,
        ;
    }
    if j == pos {
        assert((((mask | (val << pos)) & (1u8 << j)) != 0) == ((mask & (1u8 << j)) != 0 || val
            == 1u8)) by (bit_vector)
            requires
                pos < 8u8,
                j < 8u8,
                val == 0u8 || val == 1u8,
                j == pos,
        ;
    }
}

/// If `mask < 2^bound_shift`, then bit `j` (where j >= bound_shift) is clear.
pub proof fn lemma_mask_bound_implies_bit_clean(mask: u8, bound_shift: u8, j: u8)
    requires
        bound_shift <= 8,
        j < 8,
        j >= bound_shift,
        (mask as u16) < (1u16 << (bound_shift as u16)),
    ensures
        (mask & (1u8 << j)) == 0,
{
    assert((mask & (1u8 << j)) == 0u8) by (bit_vector)
        requires
            bound_shift <= 8u8,
            j < 8u8,
            j >= bound_shift,
            (mask as u16) < (1u16 << (bound_shift as u16)),
    ;
}

/// After OR-ing `val << pos` into a mask bounded by `2^pos`, the result
/// is bounded by `2^(pos+1)`.
pub proof fn lemma_mask_or_bound(mask: u8, val: u8, pos: u8)
    requires
        pos < 8,
        val == 0 || val == 1,
        (mask as u16) < (1u16 << (pos as u16)),
    ensures
        ((mask | (val << pos)) as u16) < (1u16 << ((pos + 1) as u16)),
{
    assert(((mask | (val << pos)) as u16) < (1u16 << ((pos + 1) as u16))) by (bit_vector)
        requires
            pos < 8u8,
            val == 0u8 || val == 1u8,
            (mask as u16) < (1u16 << (pos as u16)),
    ;
}

/// Prove `lemma_or_bit` for every bit position 0..8 in one call.
pub proof fn lemma_or_bit_all(mask: u8, val: u8, pos: u8)
    requires
        pos < 8,
        val == 0 || val == 1,
    ensures
        forall|j: u8|
            #![auto]
            j < 8 ==> (j != pos ==> ((mask | (val << pos)) & (1u8 << j)) == (mask & (1u8 << j)))
                && (j == pos ==> (((mask | (val << pos)) & (1u8 << j)) != 0) == ((mask & (1u8 << j))
                != 0 || val == 1u8)),
{
    lemma_or_bit(mask, val, pos, 0);
    lemma_or_bit(mask, val, pos, 1);
    lemma_or_bit(mask, val, pos, 2);
    lemma_or_bit(mask, val, pos, 3);
    lemma_or_bit(mask, val, pos, 4);
    lemma_or_bit(mask, val, pos, 5);
    lemma_or_bit(mask, val, pos, 6);
    lemma_or_bit(mask, val, pos, 7);
}

} // verus!
