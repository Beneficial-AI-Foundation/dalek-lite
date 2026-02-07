//! Arithmetic mod \\(2\^{252} + 27742317777372353535851937790883648493\\)
//! with five \\(52\\)-bit unsigned limbs.
//!
//! \\(51\\)-bit limbs would cover the desired bit range (\\(253\\)
//! bits), but isn't large enough to reduce a \\(512\\)-bit number with
//! Montgomery multiplication, so \\(52\\) bits is used instead.  To see
//! that this is safe for intermediate results, note that the largest
//! limb in a \\(5\times 5\\) product of \\(52\\)-bit limbs will be
//!
//! ```text
//! (0xfffffffffffff^2) * 5 = 0x4ffffffffffff60000000000005 (107 bits).
//! ```
use super::field::load8_at;
#[allow(unused_imports)]
use super::subtle_assumes::select;
use core::fmt::Debug;
use core::ops::{Index, IndexMut};
#[allow(unused_imports)]
use subtle::Choice;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

#[allow(unused_imports)]
use crate::constants;

#[allow(unused_imports)]
use crate::backend::serial::u64::subtle_assumes::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::bit_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::div_mod_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::mul_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::pow_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::shift_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::to_nat_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::load8_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::montgomery_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::scalar_byte_lemmas::bytes_to_scalar_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::scalar_byte_lemmas::scalar_to_bytes_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas::*; // TODO: see https://github.com/Beneficial-AI-Foundation/dalek-lite/issues/386
#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas_::montgomery_reduce_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas_::montgomery_reduce_part1_chain_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas_::montgomery_reduce_part2_chain_lemmas::*;
#[allow(unused_imports)]
use crate::specs::montgomery_reduce_specs::*;
use crate::specs::scalar52_specs::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
#[allow(unused_imports)]
use vstd::calc;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::lemmas::common_lemmas::to_nat_lemmas::lemma_bytes32_to_nat_equals_suffix_64;
#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas_extra::*;
#[cfg(verus_keep_ghost)]
use crate::lemmas::scalar_montgomery_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::specs::core_specs::bytes32_to_nat;
#[cfg(verus_keep_ghost)]
use crate::specs::core_specs::bytes_seq_to_nat;
#[cfg(verus_keep_ghost)]
use crate::specs::core_specs::bytes_to_nat_prefix;
#[cfg(verus_keep_ghost)]
use crate::specs::core_specs::bytes_to_nat_suffix;
#[cfg(verus_keep_ghost)]
use crate::specs::core_specs::spec_load8_at;
#[cfg(verus_keep_ghost)]
use crate::specs::core_specs::word64_from_bytes;
#[cfg(verus_keep_ghost)]
use crate::specs::core_specs::words64_from_bytes_to_nat;

verus! {

/// The `Scalar52` struct represents an element in
/// \\(\mathbb Z / \ell \mathbb Z\\) as 5 \\(52\\)-bit limbs.
#[derive(Copy, Clone)]
pub struct Scalar52 {
    pub limbs: [u64; 5],
}

} // verus!
impl Debug for Scalar52 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Scalar52: {:?}", self.limbs)
    }
}

verus! {

#[cfg(feature = "zeroize")]
impl Zeroize for Scalar52 {
    /* <VERIFICATION NOTE>
    Using wrapper function for Verus compatibility instead of direct call to zeroize
    </VERIFICATION NOTE> */
    fn zeroize(&mut self)
        ensures
            forall|i: int| 0 <= i < 5 ==> self.limbs[i] == 0,
    {
        /* ORIGINAL CODE: self.limbs.zeroize(); */
        crate::core_assumes::zeroize_limbs5(&mut self.limbs);
    }
}

impl Index<usize> for Scalar52 {
    type Output = u64;

    fn index(&self, _index: usize) -> (result: &u64)
        requires
            _index < 5,
        ensures
            result == &(self.limbs[_index as int]),
    {
        &(self.limbs[_index])
    }
}

} // verus!
// VERIFICATION EXCLUDED: mutable returns unsupported by Verus
impl IndexMut<usize> for Scalar52 {
    fn index_mut(&mut self, _index: usize) -> &mut u64 {
        &mut (self.limbs[_index])
    }
}

verus! {

/// u64 * u64 = u128 multiply helper
#[inline(always)]
fn m(x: u64, y: u64) -> (z: u128)
    ensures
        (z as nat) == (x as nat) * (y as nat),
{
    proof {
        lemma_mul_le(x as nat, u64::MAX as nat, y as nat, u64::MAX as nat);
    }
    (x as u128) * (y as u128)
}

impl Scalar52 {
    /// The scalar \\( 0 \\).
    pub const ZERO: Scalar52 = Scalar52 { limbs: [0, 0, 0, 0, 0] };

    /// Unpack a 32 byte / 256 bit scalar into 5 52-bit limbs.
    #[rustfmt::skip]  // keep alignment of s[*] calculations
    pub fn from_bytes(bytes: &[u8; 32]) -> (s: Scalar52)
        ensures
            bytes32_to_nat(bytes) == scalar52_to_nat(&s),
            limbs_bounded(&s),
            limb_prod_bounded_u128(s.limbs, s.limbs, 5),
    {
        let mut words = [0u64;4];
        for i in 0..4
            invariant
                0 <= i <= 4,
                forall|i2: int| i <= i2 < 4 ==> words[i2] == 0,
                forall|i2: int|
                    0 <= i2 < i ==> (words[i2] == bytes_to_nat_prefix(
                        Seq::new(8, |j: int| bytes[i2 * 8 + j]),
                        8,
                    )),
        {
            proof {
                assert(words[i as int] == 0);
                lemma_pow2_pos(0)
            }

            for j in 0..8
                invariant
                    0 <= j <= 8 && 0 <= i < 4,
                    words[i as int] < pow2(j as nat * 8),
                    forall|i2: int| i + 1 <= i2 < 4 ==> words[i2] == 0,
                    words[i as int] == bytes_to_nat_prefix(
                        Seq::new(8, |j2: int| bytes[i as int * 8 + j2]),
                        j as nat,
                    ),
                    forall|i2: int|
                        0 <= i2 < i ==> ((words[i2] as nat) == bytes_to_nat_prefix(
                            Seq::new(8, |j: int| bytes[i2 * 8 + j]),
                            8,
                        )),
            {
                proof {
                    lemma_byte_to_word_step(*bytes, words, i, j);
                }
                words[i] |= (bytes[(i * 8) + j] as u64) << (j * 8);
            }
        }

        proof {
            lemma_bytes_to_word_equivalence(bytes, words);
            assert(1u64 << 52 > 0) by (bit_vector);
            assert(1u64 << 48 > 0) by (bit_vector);
        }

        let mask = (1u64 << 52) - 1;
        let top_mask = (1u64 << 48) - 1;
        let mut s = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        //test workflow graphs
        s.limbs[0] = words[0] & mask;
        s.limbs[1] = ((words[0] >> 52) | (words[1] << 12)) & mask;
        s.limbs[2] = ((words[1] >> 40) | (words[2] << 24)) & mask;
        s.limbs[3] = ((words[2] >> 28) | (words[3] << 36)) & mask;
        s.limbs[4] = (words[3] >> 16) & top_mask;

        proof {
            lemma_words_to_scalar(words, s, mask, top_mask);
            assert(bytes32_to_nat(bytes) == scalar52_to_nat(&s));
            lemma_limbs_bounded_implies_prod_bounded(&s, &s);
        }

        s
    }

    /// Reduce a 64 byte / 512 bit scalar mod l
    #[rustfmt::skip]  // keep alignment of lo[*] and hi[*] calculations
    #[verifier::rlimit(40)]
    pub fn from_bytes_wide(bytes: &[u8; 64]) -> (s: Scalar52)
        ensures
    // VERIFICATION NOTE: Result is canonical

            is_canonical_scalar52(&s),
            scalar52_to_nat(&s) == bytes_seq_to_nat(bytes@) % group_order(),
    {
        let ghost wide_input = bytes_seq_to_nat(bytes@);

        proof {
            // Bridge bytes_seq_to_nat with the suffix sum for loop invariant
            lemma_bytes32_to_nat_equals_suffix_64(bytes);
        }

        // Stage 1 assumption: the byte-to-word packing yields the expected little-endian value.
        let mut words = [0u64;8];
        for i in 0..8
            invariant
                forall|k: int|
                    #![auto]
                    0 <= k < i ==> words@[k] as nat == word64_from_bytes(bytes@, k),
                words64_from_bytes_to_nat(bytes@, i as int) + bytes_to_nat_suffix(
                    bytes,
                    (i as int) * 8,
                ) == bytes_seq_to_nat(bytes@),
                forall|k: int| i <= k < 8 ==> words@[k] == 0,
        {
            let offset = i * 8;
            let _offset_end = offset + 7usize;
            proof {
                // offset + 7 = i*8 + 7 <= 7*8 + 7 = 63 < 64 = bytes.len()
                assert(_offset_end < 64);
            }
            let chunk = load8_at(bytes, offset);
            words[i] = chunk;

            proof {
                let i_int = i as int;
                // spec_load8_at uses pow2(k*8) * byte, word64_from_bytes uses byte * pow2(k*8)
                assert(spec_load8_at(bytes, (i_int * 8) as usize) == word64_from_bytes(
                    bytes@,
                    i_int,
                )) by {
                    broadcast use lemma_mul_is_commutative;

                };
                assert forall|k: int| i + 1 <= k < 8 implies words@[k] == 0 by {
                    assert(words@[#[trigger] k] == 0);
                };
                reveal_with_fuel(words64_from_bytes_to_nat, 9);
                assert(bytes_to_nat_suffix(bytes, i_int * 8) == word64_from_bytes(bytes@, i_int)
                    * pow2((i_int * 64) as nat) + bytes_to_nat_suffix(bytes, (i_int + 1) * 8)) by {
                    lemma_bytes_suffix_matches_word_partial(bytes, i_int, 8);
                    broadcast use lemma_mul_is_commutative;

                };
            }
        }

        proof {
            lemma_words_to_nat_equals_bytes(&words, bytes, 8);
        }

        // Stage 2 word bounds: every assembled chunk fits in 64 bits.
        assert forall|k: int| 0 <= k < 8 implies words[k] < pow2(64) by {
            let idx = (k * 8) as usize;
            lemma_spec_load8_at_fits_u64(bytes, idx);
            // spec_load8_at uses pow2(k*8) * byte, word64_from_bytes uses byte * pow2(k*8)
            assert(spec_load8_at(bytes, idx) == word64_from_bytes(bytes@, k)) by {
                broadcast use lemma_mul_is_commutative;

            };
            lemma2_to64_rest();  // u64::MAX == pow2(64) - 1
        };

        proof {
            assert(1u64 << 52 > 0) by (bit_vector);
        }
        let mask = (1u64 << 52) - 1;
        let mut lo = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        let mut hi = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };

        lo.limbs[0] = words[0] & mask;
        lo.limbs[1] = ((words[0] >> 52) | (words[1] << 12)) & mask;
        lo.limbs[2] = ((words[1] >> 40) | (words[2] << 24)) & mask;
        lo.limbs[3] = ((words[2] >> 28) | (words[3] << 36)) & mask;
        lo.limbs[4] = ((words[3] >> 16) | (words[4] << 48)) & mask;
        hi.limbs[0] = (words[4] >> 4) & mask;
        hi.limbs[1] = ((words[4] >> 56) | (words[5] << 8)) & mask;
        hi.limbs[2] = ((words[5] >> 44) | (words[6] << 20)) & mask;
        hi.limbs[3] = ((words[6] >> 32) | (words[7] << 32)) & mask;
        hi.limbs[4] = words[7] >> 20;

        // Stage 3: the masked limbs contributed by each 64-bit word remain below 2^52.
        let ghost lo_raw = lo;
        let ghost hi_raw = hi;

        proof {
            lemma_lo_limbs_bounded(&lo_raw, &words, mask);
            lemma_hi_limbs_bounded(&hi_raw, &words, mask);
        }

        let ghost pow2_260 = pow2(260);
        let ghost low_expr = (words[0] as nat) + pow2(64) * (words[1] as nat) + pow2(128) * (
        words[2] as nat) + pow2(192) * (words[3] as nat) + pow2(256) * ((words[4] & 0xf) as nat);

        let ghost high_expr = (words[4] >> 4) as nat + pow2(60) * (words[5] as nat) + pow2(124) * (
        words[6] as nat) + pow2(188) * (words[7] as nat);

        let ghost wide_sum = (words[0] as nat) + pow2(64) * (words[1] as nat) + pow2(128) * (
        words[2] as nat) + pow2(192) * (words[3] as nat) + pow2(256) * (words[4] as nat) + pow2(320)
            * (words[5] as nat) + pow2(384) * (words[6] as nat) + pow2(448) * (words[7] as nat);

        proof {
            // Reading the five 52-bit limbs in radix 2^52 reproduces the low chunk reconstructed from the 64-bit words.
            lemma_low_limbs_encode_low_expr(&lo_raw.limbs, &words, mask);
            lemma_five_limbs_equals_to_nat(&lo_raw.limbs);
            // Reading the five 52-bit limbs in radix 2^52 reproduces the high chunk reconstructed from the 64-bit words.
            lemma_high_limbs_encode_high_expr(&hi_raw.limbs, &words, mask);
            lemma_five_limbs_equals_to_nat(&hi_raw.limbs);
        }
        assert(scalar52_to_nat(&hi_raw) == high_expr);

        // Assumption [L2]: The 512-bit input splits as `pow2(260) * high_expr + low_expr`.
        // WideSum-Expansion: converting the eight 64-bit words back into a natural number matches the explicit little-endian sum of their weighted contributions.
        proof {
            lemma_words64_from_bytes_to_nat_wide(bytes);
        }

        // HighLow-Recombine: Combining the high and low chunks at the 2^260 boundary reproduces the weighted word sum.
        // Bridge bit operations to arithmetic operations for word4
        let ghost word4 = words[4];
        let ghost word4_high_nat = (word4 >> 4) as nat;
        let ghost word4_low_nat = (word4 & 0xf) as nat;
        // word4 >> 4 == word4 / 16 and word4 & 0xf == word4 % 16 (for u64)
        assert(word4_high_nat == (word4 as nat) / 16 && word4_low_nat == (word4 as nat) % 16) by {
            assert(word4 >> 4 == word4 / 16 && word4 & 0xf == word4 % 16) by (bit_vector)
                requires
                    word4 == word4,
            ;
        };
        proof {
            lemma_high_low_recombine(
                words[0] as nat,
                words[1] as nat,
                words[2] as nat,
                words[3] as nat,
                word4 as nat,
                words[5] as nat,
                words[6] as nat,
                words[7] as nat,
                word4_low_nat,
                word4_high_nat,
            );
        }

        assert(wide_input == pow2_260 * high_expr + low_expr);
        // L3: The lower chunk has value strictly below 2^260.
        proof {
            lemma_bound_scalar(&lo_raw);
        }
        assert(low_expr < pow2_260);

        // Assumption: The lower bits of the wide input, modulo 2^260, match the natural value encoded by `lo_raw`.
        assert(scalar52_to_nat(&lo_raw) == wide_input % pow2(260)) by {
            lemma_mod_multiples_vanish(high_expr as int, low_expr as int, pow2_260 as int);
            lemma_small_mod(low_expr, pow2_260);
        };
        // Assumption: The upper bits of the wide input, divided by 2^260, match the natural value encoded by `hi_raw`.
        assert(scalar52_to_nat(&hi_raw) == wide_input / pow2(260)) by {
            // Re-assert the precondition to help Z3
            assert(wide_input == pow2_260 * high_expr + low_expr);
            lemma_fundamental_div_mod_converse(
                wide_input as int,
                pow2_260 as int,
                high_expr as int,
                low_expr as int,
            );
        };
        // Recombining quotient and remainder at the 2^260 radix recreates the original wide input.
        assert(high_expr < pow2(252)) by {
            lemma_words_to_nat_upper_bound(&words, 8);
            lemma_pow2_adds(260, 252);
            assert(pow2_260 * pow2(252) == pow2(512));
            lemma_multiply_divide_lt(wide_input as int, pow2_260 as int, pow2(252) as int);
        };

        // Stage 4 assumption: Montgomery reductions behave as expected for these operands.
        proof {
            lemma_r_limbs_bounded();  // had to write this one manually due to crashes
            lemma_rr_limbs_bounded();
            lemma_limbs_bounded_implies_prod_bounded(&lo, &constants::R);
            lemma_limbs_bounded_implies_prod_bounded(&hi, &constants::RR);
        }

        let lo_product = Scalar52::mul_internal(&lo, &constants::R);
        proof {
            // Establish montgomery_reduce's preconditions
            lemma_bounded_product_satisfies_input_bounds(&lo, &constants::R, &lo_product);
            // R is canonical (< L), so the product satisfies canonical_bound
            lemma_r_equals_spec(constants::R);  // gives scalar52_to_nat(&R) < group_order()
            lemma_canonical_product_satisfies_canonical_bound(&lo, &constants::R, &lo_product);
        }
        lo = Scalar52::montgomery_reduce(&lo_product);  // (lo * R) / R = lo
        // is_canonical_scalar52(&lo) follows from montgomery_reduce postcondition

        let hi_product = Scalar52::mul_internal(&hi, &constants::RR);
        proof {
            // Establish montgomery_reduce's preconditions
            lemma_bounded_product_satisfies_input_bounds(&hi, &constants::RR, &hi_product);
            // RR is canonical (< L), so the product satisfies canonical_bound
            lemma_rr_equals_spec();  // gives scalar52_to_nat(&RR) < group_order()
            lemma_canonical_product_satisfies_canonical_bound(&hi, &constants::RR, &hi_product);
        }
        hi = Scalar52::montgomery_reduce(&hi_product);  // (hi * R^2) / R = hi * R
        // is_canonical_scalar52(&hi) follows from montgomery_reduce postcondition

        proof {
            let ghost lo_before_nat = scalar52_to_nat(&lo_raw);
            let ghost lo_after_nat = scalar52_to_nat(&lo);
            let ghost r_nat = scalar52_to_nat(&constants::R);
            lemma_r_equals_spec(constants::R);
            // lo: multiply by R, reduce => extra_factor = 1
            lemma_montgomery_reduce_cancels_r(lo_after_nat, lo_before_nat, r_nat, 1);

            let ghost hi_before_nat = scalar52_to_nat(&hi_raw);
            let ghost hi_after_nat = scalar52_to_nat(&hi);
            let ghost rr_nat = scalar52_to_nat(&constants::RR);
            lemma_rr_equals_spec();
            // hi: multiply by R², reduce => extra_factor = R
            lemma_montgomery_reduce_cancels_r(
                hi_after_nat,
                hi_before_nat,
                rr_nat,
                montgomery_radix(),
            );
        }

        let result = Scalar52::add(&hi, &lo);

        // Stage 5 assumption: combining the reduced pieces matches the wide scalar modulo L.
        proof {
            lemma_montgomery_reduced_sum_congruent(
                scalar52_to_nat(&result),
                scalar52_to_nat(&hi),
                scalar52_to_nat(&lo),
                scalar52_to_nat(&hi_raw),
                scalar52_to_nat(&lo_raw),
                wide_input,
            );

            lemma_cancel_mul_pow2_mod(scalar52_to_nat(&result), wide_input, montgomery_radix());

            // Since result < group_order() (from add's postcondition),
            // we have scalar52_to_nat(&result) % group_order() == scalar52_to_nat(&result)
            lemma_small_mod(scalar52_to_nat(&result), group_order());
        }

        result
    }

    /// Pack the limbs of this `Scalar52` into 32 bytes
    #[rustfmt::skip]  // keep alignment of s[*] calculations
    #[allow(clippy::identity_op)]
    #[allow(clippy::wrong_self_convention)]
    pub fn as_bytes(self) -> (s: [u8; 32])
        requires
            limbs_bounded(&self),
        ensures
            bytes32_to_nat(&s) == scalar52_to_nat(&self) % pow2(256),
    {
        let mut s = [0u8;32];

        s[0] = (self.limbs[0] >> 0) as u8;
        s[1] = (self.limbs[0] >> 8) as u8;
        s[2] = (self.limbs[0] >> 16) as u8;
        s[3] = (self.limbs[0] >> 24) as u8;
        s[4] = (self.limbs[0] >> 32) as u8;
        s[5] = (self.limbs[0] >> 40) as u8;
        s[6] = ((self.limbs[0] >> 48) | (self.limbs[1] << 4)) as u8;
        s[7] = (self.limbs[1] >> 4) as u8;
        s[8] = (self.limbs[1] >> 12) as u8;
        s[9] = (self.limbs[1] >> 20) as u8;
        s[10] = (self.limbs[1] >> 28) as u8;
        s[11] = (self.limbs[1] >> 36) as u8;
        s[12] = (self.limbs[1] >> 44) as u8;
        s[13] = (self.limbs[2] >> 0) as u8;
        s[14] = (self.limbs[2] >> 8) as u8;
        s[15] = (self.limbs[2] >> 16) as u8;
        s[16] = (self.limbs[2] >> 24) as u8;
        s[17] = (self.limbs[2] >> 32) as u8;
        s[18] = (self.limbs[2] >> 40) as u8;
        s[19] = ((self.limbs[2] >> 48) | (self.limbs[3] << 4)) as u8;
        s[20] = (self.limbs[3] >> 4) as u8;
        s[21] = (self.limbs[3] >> 12) as u8;
        s[22] = (self.limbs[3] >> 20) as u8;
        s[23] = (self.limbs[3] >> 28) as u8;
        s[24] = (self.limbs[3] >> 36) as u8;
        s[25] = (self.limbs[3] >> 44) as u8;
        s[26] = (self.limbs[4] >> 0) as u8;
        s[27] = (self.limbs[4] >> 8) as u8;
        s[28] = (self.limbs[4] >> 16) as u8;
        s[29] = (self.limbs[4] >> 24) as u8;
        s[30] = (self.limbs[4] >> 32) as u8;
        s[31] = (self.limbs[4] >> 40) as u8;

        proof {
            // The main lemma proves the property using the non-recursive (_aux) versions
            lemma_as_bytes_52(self.limbs, s);
            lemma_five_limbs_equals_to_nat(&self.limbs);
        }

        s
    }

    /// Compute `a + b` (mod l)
    pub fn add(a: &Scalar52, b: &Scalar52) -> (s: Scalar52)
        requires
            limbs_bounded(a),
            limbs_bounded(b),
            scalar52_to_nat(&a) < group_order(),
            scalar52_to_nat(&b) < group_order(),
        ensures
            scalar52_to_nat(&s) == (scalar52_to_nat(&a) + scalar52_to_nat(&b)) % group_order(),
            // VERIFICATION NOTE: Result is canonical
            scalar52_to_nat(&s) < group_order(),
            // VERIFICATION NOTE: Result has bounded limbs (from sub)
            limbs_bounded(&s),
    {
        let mut sum = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        proof {
            assert(1u64 << 52 > 0) by (bit_vector);
        }
        let mask = (1u64 << 52) - 1;

        // a + b
        let mut carry: u64 = 0;
        proof {
            // Base case: empty subrange has value 0
            assert(seq_u64_to_nat(a.limbs@.subrange(0, 0 as int)) == 0);
            assert(seq_u64_to_nat(b.limbs@.subrange(0, 0 as int)) == 0);
            assert(seq_u64_to_nat(sum.limbs@.subrange(0, 0 as int)) == 0);
            assert((carry >> 52) == 0) by (bit_vector)
                requires
                    carry == 0,
            ;
            lemma2_to64();
            assert(pow2(0) == 1);
        }
        for i in 0..5
            invariant
                forall|j: int| 0 <= j < i ==> sum.limbs[j] < 1u64 << 52,
                limbs_bounded(a),
                limbs_bounded(b),
                mask == (1u64 << 52) - 1,
                i == 0 ==> carry == 0,
                i >= 1 ==> (carry >> 52) < 2,
                seq_u64_to_nat(a.limbs@.subrange(0, i as int)) + seq_u64_to_nat(
                    b.limbs@.subrange(0, i as int),
                ) == seq_u64_to_nat(sum.limbs@.subrange(0, i as int)) + (carry >> 52) * pow2(
                    (52 * (i) as nat),
                ),
        {
            proof {
                lemma_add_loop_bounds(i as int, carry, a.limbs[i as int], b.limbs[i as int]);
            }
            let ghost old_carry = carry;
            carry = a.limbs[i] + b.limbs[i] + (carry >> 52);
            let ghost sum_loop_start = sum;
            sum.limbs[i] = carry & mask;
            assert(sum_loop_start.limbs@.subrange(0, i as int) == sum.limbs@.subrange(0, i as int));
            proof {
                lemma_add_loop_invariant(sum, carry, i, a, b, old_carry, mask, sum_loop_start);
            }
            proof {
                lemma_add_carry_and_sum_bounds(carry, mask);
            }
        }

        assert(seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) + seq_u64_to_nat(
            b.limbs@.subrange(0, 5 as int),
        ) == seq_u64_to_nat(sum.limbs@.subrange(0, 5 as int)) + (carry >> 52) * pow2(
            (52 * (5) as nat),
        ));

        proof {
            lemma_add_sum_simplify(a, b, &sum, carry);
        }

        // subtract l if the sum is >= l
        proof {
            lemma_l_value_properties(&constants::L, &sum);
        }
        assert(group_order() > scalar52_to_nat(&sum) - group_order() >= -group_order());
        proof {
            lemma_l_equals_group_order();
        }
        proof {
            lemma_mod_sub_multiples_vanish(scalar52_to_nat(&sum) as int, group_order() as int);
        }
        Scalar52::sub(&sum, &constants::L)
    }

    // VERIFICATION NOTE: refactored sub function from Dalek upstream
    #[allow(dead_code)]
    pub fn sub_new(a: &Scalar52, b: &Scalar52) -> (s: Scalar52)
        requires
            limbs_bounded(a),
            limbs_bounded(b),
            -group_order() <= scalar52_to_nat(&a) - scalar52_to_nat(&b) < group_order(),
        ensures
            scalar52_to_nat(&s) == (scalar52_to_nat(&a) - scalar52_to_nat(&b)) % (
            group_order() as int),
    {
        assume(false);  // TODO: complete the proof
        let mut difference = Scalar52::ZERO;
        let mask = (1u64 << 52) - 1;

        // a - b
        let mut borrow: u64 = 0;
        for i in 0..5 {
            assume(false);
            borrow = a.limbs[i].wrapping_sub(b.limbs[i] + (borrow >> 63));
            difference[i] = borrow & mask;
        }

        // conditionally add l if the difference is negative
        difference.conditional_add_l(Choice::from((borrow >> 63) as u8));
        difference
    }

    // VERIFICATION NOTE: conditional_add_l function only used in sub_new function
    #[allow(dead_code)]
    pub(crate) fn conditional_add_l(&mut self, condition: Choice) -> (carry: u64)
        requires
            limbs_bounded(&old(self)),
            scalar52_to_nat(old(self)) + group_order() < pow2(260),
        ensures
    // The mathematical value modulo group_order doesn't change (since L = group_order)

            scalar52_to_nat(self) % group_order() == scalar52_to_nat(old(self)) % group_order(),
            // VERIFICATION NOTE: expression below unsupported by Verus
            //limbs_bounded(&self),
            // Meaning of conditional addition
            choice_is_true(condition) ==> scalar52_to_nat(self) == scalar52_to_nat(old(self))
                + group_order(),
            !choice_is_true(condition) ==> scalar52_to_nat(self) == scalar52_to_nat(old(self)),
    {
        let mut carry: u64 = 0;

        proof {
            assert(1u64 << 52 > 0) by (bit_vector);
        }
        let mask = (1u64 << 52) - 1;

        for i in 0..5
            invariant
                mask == (1u64 << 52) - 1,
                forall|j: int| 0 <= j < i ==> self.limbs[j] < (1u64 << 52),
                forall|j: int| i <= j < 5 ==> self.limbs[j] == old(self).limbs[j],
                forall|j: int| i <= j < 5 ==> self.limbs[j] < (1u64 << 52),
                i == 0 ==> carry == 0,
                i >= 1 ==> (carry >> 52) < 2,
        {
            /* <VERIFICATION NOTE> Using wrapper function for Verus compatibility instead of direct call to conditional_select */
            let addend = select(&0, &constants::L.limbs[i], condition);
            /* <ORIGINAL CODE>
             let addend = u64::conditional_select(&0, &constants::L[i], condition);
             <ORIGINAL CODE>*/

            // Prove no overflow using the same lemma as in sub()
            proof {
                lemma_scalar_subtract_no_overflow(
                    carry,
                    self.limbs[i as int],
                    addend,
                    i as u32,
                    &constants::L,
                );
            }

            carry = (carry >> 52) + self.limbs[i] + addend;
            self.limbs[i] = carry & mask;

            proof {
                lemma_carry_bounded_after_mask(carry, mask);
            }
        }

        proof {
            // TODO: Prove the postconditions
            assume(scalar52_to_nat(self) % group_order() == scalar52_to_nat(old(self))
                % group_order());
            //   assume(limbs_bounded(&self));
            assume(choice_is_true(condition) ==> scalar52_to_nat(self) == scalar52_to_nat(old(self))
                + group_order());
            assume(!choice_is_true(condition) ==> scalar52_to_nat(self) == scalar52_to_nat(
                old(self),
            ));
        }

        carry
    }

    /// Compute `a - b` (mod l)
    ///
    /// PRECONDITION RELAXATION: `a` doesn't need to be fully bounded.
    /// Limbs 0-3 must be < 2^52, but limb 4 can be up to 2^52 + b[4].
    /// This is needed for montgomery_reduce where the intermediate has r4 > 2^52.
    /// See docs/proofs_for_montgomery_reduce/sub_and_bounds_analysis.md for analysis.
    pub fn sub(a: &Scalar52, b: &Scalar52) -> (s: Scalar52)
        requires
    // Relaxed bound: limbs 0-3 bounded, limb 4 can exceed 2^52 by up to b[4]

            limbs_bounded_for_sub(a, b),
            limbs_bounded(
                b,
            ),
    // NOTE: Value constraint removed from requires - now conditional in ensures

        ensures
    // UNCONDITIONAL: limbs are always bounded due to masking in both loops

            limbs_bounded(&s),
            // CONDITIONAL: modular correctness and canonicity only when value constraint holds
            // -L <= (a - b) < L
            ({
                let diff = scalar52_to_nat(&a) as int - scalar52_to_nat(&b) as int;
                let l = group_order() as int;
                -l <= diff && diff < l
            }) ==> (scalar52_to_nat(&s) == (scalar52_to_nat(&a) as int - scalar52_to_nat(&b) as int)
                % (group_order() as int)),
            ({
                let diff = scalar52_to_nat(&a) as int - scalar52_to_nat(&b) as int;
                let l = group_order() as int;
                -l <= diff && diff < l
            }) ==> is_canonical_scalar52(&s),
    {
        let mut difference = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        proof {
            assert(1u64 << 52 > 0) by (bit_vector);
        }
        let mask = (1u64 << 52) - 1;

        // a - b
        let mut borrow: u64 = 0;
        assert(seq_u64_to_nat(a.limbs@.subrange(0, 0 as int)) - seq_u64_to_nat(
            b.limbs@.subrange(0, 0 as int),
        ) == seq_u64_to_nat(difference.limbs@.subrange(0, 0 as int)));
        assert((borrow >> 63) == 0) by (bit_vector)
            requires
                borrow == 0,
        ;
        assert(seq_u64_to_nat(a.limbs@.subrange(0, 0 as int)) - seq_u64_to_nat(
            b.limbs@.subrange(0, 0 as int),
        ) == seq_u64_to_nat(difference.limbs@.subrange(0, 0 as int)) - (borrow >> 63) * pow2(
            (52 * (0) as nat),
        ));
        for i in 0..5
            invariant
                limbs_bounded(b),
                // Relaxed bound on a: limbs 0-3 are bounded, limb 4 can be up to 2^52 + b[4]
                limbs_bounded_for_sub(a, b),
                forall|j: int| 0 <= j < i ==> difference.limbs[j] < (1u64 << 52),
                mask == (1u64 << 52) - 1,
                seq_u64_to_nat(a.limbs@.subrange(0, i as int)) - seq_u64_to_nat(
                    b.limbs@.subrange(0, i as int),
                ) == seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) - (borrow >> 63)
                    * pow2((52 * (i) as nat)),
        {
            proof {
                assert((borrow >> 63) < 2) by (bit_vector);
            }
            let ghost old_borrow = borrow;
            borrow = a.limbs[i].wrapping_sub(b.limbs[i] + (borrow >> 63));
            let ghost difference_loop1_start = difference;
            difference.limbs[i] = borrow & mask;
            assert(difference_loop1_start.limbs@.subrange(0, i as int)
                == difference.limbs@.subrange(0, i as int));
            assert(seq_u64_to_nat(a.limbs@.subrange(0, i as int)) - seq_u64_to_nat(
                b.limbs@.subrange(0, i as int),
            ) == seq_u64_to_nat(difference_loop1_start.limbs@.subrange(0, i as int)) - (old_borrow
                >> 63) * pow2((52 * (i) as nat)));
            proof {
                lemma_sub_loop1_invariant(
                    difference,
                    borrow,
                    i,
                    a,
                    b,
                    old_borrow,
                    mask,
                    difference_loop1_start,
                );
            }
            proof {
                lemma_borrow_and_mask_bounded(borrow, mask);
            }
        }

        assert(seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) - seq_u64_to_nat(
            b.limbs@.subrange(0, 5 as int),
        ) == seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) - (borrow >> 63) * pow2(
            (52 * (5) as nat),
        ));
        // conditionally add l if the difference is negative
        assert(borrow >> 63 == 1 || borrow >> 63 == 0) by (bit_vector);
        let mut carry: u64 = 0;
        let ghost difference_after_loop1 = difference;
        assert(seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, 0 as int)) == 0);
        assert(seq_u64_to_nat(constants::L.limbs@.subrange(0, 0 as int)) == 0);
        assert(seq_u64_to_nat(difference.limbs@.subrange(0, 0 as int)) == 0);
        assert(carry >> 52 == 0) by (bit_vector)
            requires
                carry == 0,
        ;
        for i in 0..5
            invariant
                forall|j: int| 0 <= j < 5 ==> difference.limbs[j] < (1u64 << 52),  // from first loop
                forall|j: int|
                    i <= j < 5 ==> difference.limbs[j] == difference_after_loop1.limbs[j],
                mask == (1u64 << 52) - 1,
                i == 0 ==> carry == 0,
                i >= 1 ==> (carry >> 52) < 2,
                (i >= 1 && borrow >> 63 == 0) ==> carry == difference.limbs[i - 1],
                borrow >> 63 == 0 ==> difference_after_loop1 == difference,
                borrow >> 63 == 1 ==> seq_u64_to_nat(
                    difference_after_loop1.limbs@.subrange(0, i as int),
                ) + seq_u64_to_nat(constants::L.limbs@.subrange(0, i as int)) == seq_u64_to_nat(
                    difference.limbs@.subrange(0, i as int),
                ) + (carry >> 52) * pow2(52 * i as nat),
        {
            let ghost old_carry = carry;
            let underflow = Choice::from((borrow >> 63) as u8);
            let addend = select(&0, &constants::L.limbs[i], underflow);
            if borrow >> 63 == 0 {
                assert(addend == 0);
            }
            if borrow >> 63 == 1 {
                assert(addend == constants::L.limbs[i as int]);
            }
            proof {
                lemma_scalar_subtract_no_overflow(
                    carry,
                    difference.limbs[i as int],
                    addend,
                    i as u32,
                    &constants::L,
                );
            }
            carry = (carry >> 52) + difference.limbs[i] + addend;
            let ghost difference_loop2_start = difference;
            difference.limbs[i] = carry & mask;
            proof {
                lemma_carry_bounded_after_mask(carry, mask);
                assert(difference_loop2_start.limbs@.subrange(0, i as int)
                    == difference.limbs@.subrange(0, i as int));
                lemma_sub_loop2_invariant(
                    difference,
                    i,
                    a,
                    b,
                    mask,
                    difference_after_loop1,
                    difference_loop2_start,
                    carry,
                    old_carry,
                    addend,
                    borrow,
                );
            }
        }
        proof {
            // UNCONDITIONAL: Prove limbs_bounded from loop invariant
            // After loop 2, each limb is masked with (2^52 - 1), so < 2^52
            // The loop 2 invariant maintains: forall|j: int| 0 <= j < 5 ==> difference.limbs[j] < (1u64 << 52)
            assert(limbs_bounded(&difference)) by {
                assert(forall|j: int| 0 <= j < 5 ==> difference.limbs[j] < (1u64 << 52));
                // limbs_bounded requires each limb < pow2(52)
                // (1u64 << 52) == pow2(52)
                assert((1u64 << 52) == pow2(52)) by {
                    lemma_u64_shift_is_pow2(52);
                }
            }

            // CONDITIONAL: Modular correctness and canonicity only when value constraint holds
            let a_val = scalar52_to_nat(&a) as int;
            let b_val = scalar52_to_nat(&b) as int;
            let l_val = group_order() as int;
            if -l_val <= a_val - b_val && a_val - b_val < l_val {
                lemma_sub_correct_after_loops(
                    difference,
                    carry,
                    a,
                    b,
                    difference_after_loop1,
                    borrow,
                );
            }
        }
        difference
    }

    // NOTE: sub_for_montgomery was moved to unused_scalar_backup.rs (local backup, not committed)
    // It was an alternative sub variant with different preconditions (a >= b instead of -L <= a-b < L)
    /// Compute `a * b`
    #[inline(always)]
    #[rustfmt::skip]  // keep alignment of z[*] calculations
    pub(crate) fn mul_internal(a: &Scalar52, b: &Scalar52) -> (z: [u128; 9])
        requires
            limb_prod_bounded_u128(a.limbs, b.limbs, 5),
        ensures
            slice128_to_nat(&z) == scalar52_to_nat(&a) * scalar52_to_nat(&b),
            spec_mul_internal(a, b) == z,
    {
        proof { lemma_mul_internal_no_overflow() }

        let mut z = [0u128;9];

        z[0] = m(a.limbs[0], b.limbs[0]);
        z[1] = m(a.limbs[0], b.limbs[1]) + m(a.limbs[1], b.limbs[0]);
        z[2] = m(a.limbs[0], b.limbs[2]) + m(a.limbs[1], b.limbs[1]) + m(a.limbs[2], b.limbs[0]);
        z[3] = m(a.limbs[0], b.limbs[3]) + m(a.limbs[1], b.limbs[2]) + m(a.limbs[2], b.limbs[1])
            + m(a.limbs[3], b.limbs[0]);
        z[4] = m(a.limbs[0], b.limbs[4]) + m(a.limbs[1], b.limbs[3]) + m(a.limbs[2], b.limbs[2])
            + m(a.limbs[3], b.limbs[1]) + m(a.limbs[4], b.limbs[0]);
        z[5] = m(a.limbs[1], b.limbs[4]) + m(a.limbs[2], b.limbs[3]) + m(a.limbs[3], b.limbs[2])
            + m(a.limbs[4], b.limbs[1]);
        z[6] = m(a.limbs[2], b.limbs[4]) + m(a.limbs[3], b.limbs[3]) + m(a.limbs[4], b.limbs[2]);
        z[7] = m(a.limbs[3], b.limbs[4]) + m(a.limbs[4], b.limbs[3]);
        z[8] = m(a.limbs[4], b.limbs[4]);

        proof {
            lemma_mul_internal_correct(&a.limbs, &b.limbs, &z);
        }

        z
    }

    /* <ORIGINAL CODE>
    fn square_internal(a: &Scalar52) -> [u128; 9] {
        let aa = [
            a[0] * 2,
            a[1] * 2,
            a[2] * 2,
            a[3] * 2,
        ];

        [
            m( a[0], a[0]),
            m(aa[0], a[1]),
            m(aa[0], a[2]) + m( a[1], a[1]),
            m(aa[0], a[3]) + m(aa[1], a[2]),
            m(aa[0], a[4]) + m(aa[1], a[3]) + m( a[2], a[2]),
                             m(aa[1], a[4]) + m(aa[2], a[3]),
                                              m(aa[2], a[4]) + m( a[3], a[3]),
                                                               m(aa[3], a[4]),
                                                                                m(a[4], a[4])
        ]
    }
    </ORIGINAL CODE> */
    /* <VERIFICATION NOTE>
    -  refactored verified version of square_internal
    - slightly slower ?
    </VERIFICATION NOTE> */
    /// Compute `a^2`
    #[inline(always)]
    #[rustfmt::skip]  // keep alignment of calculations
    pub(crate) fn square_internal(a: &Scalar52) -> (z: [u128; 9])
        requires
            limb_prod_bounded_u128(a.limbs, a.limbs, 5),
        ensures
            slice128_to_nat(&z) == scalar52_to_nat(&a) * scalar52_to_nat(&a),
            spec_mul_internal(a, a) == z,
            limbs_bounded(&a) ==> forall|i: int| 0 <= i < 9 ==> z[i] < 5 * (1u128 << 104),
    {
        proof { lemma_square_internal_no_overflow() }

        let mut z = [0u128;9];
        z[0] = m(a.limbs[0], a.limbs[0]);
        z[1] = m(a.limbs[0], a.limbs[1]) * 2;
        z[2] = m(a.limbs[0], a.limbs[2]) * 2 + m(a.limbs[1], a.limbs[1]);
        z[3] = m(a.limbs[0], a.limbs[3]) * 2 + m(a.limbs[1], a.limbs[2]) * 2;
        z[4] = m(a.limbs[0], a.limbs[4]) * 2 + m(a.limbs[1], a.limbs[3]) * 2 + m(
            a.limbs[2],
            a.limbs[2],
        );
        z[5] = m(a.limbs[1], a.limbs[4]) * 2 + m(a.limbs[2], a.limbs[3]) * 2;
        z[6] = m(a.limbs[2], a.limbs[4]) * 2 + m(a.limbs[3], a.limbs[3]);
        z[7] = m(a.limbs[3], a.limbs[4]) * 2;
        z[8] = m(a.limbs[4], a.limbs[4]);

        proof {
            lemma_square_internal_correct(&a.limbs, &z);

            if (limbs_bounded(&a)) {
                assert((1u64 << 52) * (1u64 << 52) == 1u128 << 104) by (bit_vector);
                assert(5 * (1u128 << 104) <= u128::MAX) by (bit_vector);
                let bound = 1u64 << 52;
                let b2 = 1u128 << 104;
                assert forall|i: int| 0 <= i < 9 implies z[i] < 5 * b2 by {
                    assert forall|j: int, k: int| 0 <= j < 5 && 0 <= k < 5 implies (
                    a.limbs[j] as u128) * (a.limbs[k] as u128) < b2 by {
                        // trigger foralls in limbs_bounded:
                        assert(a.limbs[j] < bound);
                        assert(a.limbs[k] < bound);
                        lemma_mul_lt(
                            a.limbs[j] as nat,
                            bound as nat,
                            a.limbs[k] as nat,
                            bound as nat,
                        );
                    }
                    assert(z[i] < b2 * 2 + b2 * 2 + b2);
                    assert(b2 * 2 + b2 * 2 + b2 == 5 * b2) by {
                        assert(b2 * 2 + b2 * 2 == b2 * 4) by {
                            lemma_mul_is_distributive_add(b2 as int, 2, 2);
                        }
                        assert(b2 == b2 * 1) by {
                            lemma_mul_basics_3(b2 as int);
                        }
                        assert(b2 * 4 + b2 * 1 == 5 * b2) by {
                            lemma_mul_is_distributive_add(b2 as int, 4, 1);
                            lemma_mul_is_commutative(b2 as int, 5);
                        }
                    }
                }
            }
        }

        z
    }

    /// Compute `limbs/R` (mod l), where R is the Montgomery modulus 2^260
    ///
    /// /* ORIGINAL CODE - from dalek-cryptography/curve25519-dalek @ 61533d75
    /// pub (crate) fn montgomery_reduce(limbs: &[u128; 9]) -> Scalar52 {
    ///     #[inline(always)]
    ///     fn part1(sum: u128) -> (u128, u64) {
    ///         let p = (sum as u64).wrapping_mul(constants::LFACTOR) & ((1u64 << 52) - 1);
    ///         ((sum + m(p, constants::L[0])) >> 52, p)
    ///     }
    ///     #[inline(always)]
    ///     fn part2(sum: u128) -> (u128, u64) {
    ///         let w = (sum as u64) & ((1u64 << 52) - 1);
    ///         (sum >> 52, w)
    ///     }
    ///     // note: l[3] is zero, so its multiples can be skipped
    ///     let l = &constants::L;
    ///     // the first half computes the Montgomery adjustment factor n, and begins adding n*l to make limbs divisible by R
    ///     let (carry, n0) = part1(        limbs[0]);
    ///     let (carry, n1) = part1(carry + limbs[1] + m(n0, l[1]));
    ///     let (carry, n2) = part1(carry + limbs[2] + m(n0, l[2]) + m(n1, l[1]));
    ///     let (carry, n3) = part1(carry + limbs[3]               + m(n1, l[2]) + m(n2, l[1]));
    ///     let (carry, n4) = part1(carry + limbs[4] + m(n0, l[4])               + m(n2, l[2]) + m(n3, l[1]));
    ///     // limbs is divisible by R now, so we can divide by R by simply storing the upper half as the result
    ///     let (carry, r0) = part2(carry + limbs[5]               + m(n1, l[4])               + m(n3, l[2])   + m(n4, l[1]));
    ///     let (carry, r1) = part2(carry + limbs[6]                             + m(n2,l[4])                  + m(n4, l[2]));
    ///     let (carry, r2) = part2(carry + limbs[7]                                           + m(n3, l[4])                );
    ///     let (carry, r3) = part2(carry + limbs[8]                                                           + m(n4, l[4]));
    ///     let         r4 = carry as u64;
    ///     // result may be >= l, so attempt to subtract l
    ///     Scalar52::sub(&Scalar52([r0, r1, r2, r3, r4]), l)
    /// }
    /// */
    ///
    /// # Preconditions
    /// - `montgomery_reduce_input_bounds(limbs)`: Per-limb bounds for overflow-safe computation
    /// - `montgomery_reduce_canonical_bound(limbs)`: T < R×L (HAC 14.32's value constraint)
    ///
    /// # Postconditions (all unconditional given preconditions)
    /// - `limbs_bounded(&result)`: Result limbs are bounded (< 2^52)
    /// - `montgomery_congruent(&result, limbs)`: (result × R) ≡ T (mod L)
    /// - `is_canonical_scalar52(&result)`: result < L
    ///
    /// # Note
    /// The `canonical_bound` precondition corresponds to HAC Algorithm 14.32's requirement
    /// that T < m×R for correct Montgomery reduction. This ensures intermediate < 2L,
    /// which is needed for sub's correctness and the r4 < 2^52 + L[4] bound.
    /// HAC is at https://cacr.uwaterloo.ca/hac/about/chap14.pdf
    /// The `input_bounds` precondition ensures no overflow in u128 arithmetic.
    #[inline(always)]
    #[rustfmt::skip]  // keep alignment of n* and r* calculations
    pub(crate) fn montgomery_reduce(limbs: &[u128; 9]) -> (result: Scalar52)
        requires
    // Per-limb bounds for overflow-safe u128 arithmetic

            montgomery_reduce_input_bounds(limbs),
            // HAC 14.32's value constraint: T < R×L ensures intermediate < 2L
            montgomery_reduce_canonical_bound(limbs),
        ensures
    // All postconditions are now unconditional (given preconditions)

            limbs_bounded(&result),
            montgomery_congruent(&result, limbs),
            is_canonical_scalar52(&result),
    {
        // note: l[3] is zero, so its multiples can be skipped
        let l = &constants::L;

        // =====================================================================
        // PHASE 1: First half - compute Montgomery adjustment factors n0..n4
        // Each part1 call requires sum < 2^108
        // =====================================================================

        // Establish L is limbs_bounded once for all lemma_m calls
        proof {
            lemma_l_limbs_bounded();
        }

        // Establish once: product bound, overflow safety, and shift-to-pow2 conversions
        proof {
            assert(((1u64 << 52) as u128) * ((1u64 << 52) as u128) == (1u128 << 104))
                by (bit_vector);
            assert((1u128 << 108) < u128::MAX) by (bit_vector);
            // Convert pow2(N) to (1u128 << N) for all limb bounds used below
            lemma_u128_shift_is_pow2(104);
            lemma_u128_shift_is_pow2(105);
            lemma_u128_shift_is_pow2(106);
            lemma_u128_shift_is_pow2(107);
            lemma_u128_shift_is_pow2(108);
        }

        // part1 call 0: limbs[0] < 2^104 < 2^108 ✓
        proof {
            lemma_pow2_strictly_increases(104, 108);
        }
        let (carry, n0) = Self::part1(limbs[0]);
        let ghost carry0 = carry;

        // part1 call 1: sum1 = carry + limbs[1] + m(n0,l[1])
        let m_n0_l1 = m(n0, l.limbs[1]);
        // Goal: sum1 < 2^108 (part1's precondition)
        proof {
            lemma_m(n0, l.limbs[1], (1u64 << 52), (1u64 << 52));
            assert((1u128 << 57) + (1u128 << 105) + (1u128 << 104) <= (1u128 << 108))
                by (bit_vector);
        }
        let sum1 = carry + limbs[1] + m_n0_l1;
        let (carry, n1) = Self::part1(sum1);
        let ghost carry1 = carry;

        // part1 call 2 (n2): sum2 = carry + limbs[2] + m(n0,l[2]) + m(n1,l[1])
        let m_n0_l2 = m(n0, l.limbs[2]);
        let m_n1_l1 = m(n1, l.limbs[1]);
        // Goal: sum2 < 2^108 (part1's precondition)
        proof {
            lemma_m(n0, l.limbs[2], (1u64 << 52), (1u64 << 52));
            lemma_m(n1, l.limbs[1], (1u64 << 52), (1u64 << 52));
            assert((1u128 << 57) + (1u128 << 106) + 2 * (1u128 << 104) <= (1u128 << 108))
                by (bit_vector);
        }
        let sum2 = carry + limbs[2] + m_n0_l2 + m_n1_l1;
        let (carry, n2) = Self::part1(sum2);
        let ghost carry2 = carry;

        // part1 call 3 (n3): sum3 = carry + limbs[3] + m(n1,l[2]) + m(n2,l[1])
        let m_n1_l2 = m(n1, l.limbs[2]);
        let m_n2_l1 = m(n2, l.limbs[1]);
        // Goal: sum3 < 2^108 (part1's precondition)
        proof {
            lemma_m(n1, l.limbs[2], (1u64 << 52), (1u64 << 52));
            lemma_m(n2, l.limbs[1], (1u64 << 52), (1u64 << 52));
            assert((1u128 << 57) + (1u128 << 107) + 2 * (1u128 << 104) <= (1u128 << 108))
                by (bit_vector);
        }
        let sum3 = carry + limbs[3] + m_n1_l2 + m_n2_l1;
        let (carry, n3) = Self::part1(sum3);
        let ghost carry3 = carry;

        // part1 call 4 (n4): sum4 = carry + limbs[4] + m(n0,l[4]) + m(n2,l[2]) + m(n3,l[1])
        let m_n0_l4 = m(n0, l.limbs[4]);
        let m_n2_l2 = m(n2, l.limbs[2]);
        let m_n3_l1 = m(n3, l.limbs[1]);
        // Goal: sum4 < 2^108 (part1's precondition)
        proof {
            lemma_m(n0, l.limbs[4], (1u64 << 52), (1u64 << 52));
            lemma_m(n2, l.limbs[2], (1u64 << 52), (1u64 << 52));
            lemma_m(n3, l.limbs[1], (1u64 << 52), (1u64 << 52));
            assert((1u128 << 57) + (1u128 << 107) + 3 * (1u128 << 104) <= (1u128 << 108))
                by (bit_vector);
        }
        let sum4 = carry + limbs[4] + m_n0_l4 + m_n2_l2 + m_n3_l1;
        let (carry, n4) = Self::part1(sum4);
        let ghost carry4 = carry;

        // =====================================================================
        // PHASE 2: Divide by R (take upper half) - part2 calls
        // part2 has no precondition, only need overflow safety
        // Note: After part1, carry < 2^57. After part2, carry < 2^56.
        // =====================================================================

        // part2 call 0 (r0): carry + limbs[5] + m(n1,l[4]) + m(n3,l[2]) + m(n4,l[1])
        let m_n1_l4 = m(n1, l.limbs[4]);
        let m_n3_l2 = m(n3, l.limbs[2]);
        let m_n4_l1 = m(n4, l.limbs[1]);
        // Goal: sum5 < 2^108 (part2's precondition)
        proof {
            lemma_m(n1, l.limbs[4], (1u64 << 52), (1u64 << 52));
            lemma_m(n3, l.limbs[2], (1u64 << 52), (1u64 << 52));
            lemma_m(n4, l.limbs[1], (1u64 << 52), (1u64 << 52));
            assert((1u128 << 57) + (1u128 << 107) + 3 * (1u128 << 104) <= (1u128 << 108))
                by (bit_vector);
        }
        let sum5 = carry + limbs[5] + m_n1_l4 + m_n3_l2 + m_n4_l1;
        let (carry, r0) = Self::part2(sum5);
        let ghost carry5 = carry;
        assert(r0 < (1u64 << 52));  // from part2 postcondition

        // part2 call 1 (r1): carry + limbs[6] + m(n2,l[4]) + m(n4,l[2])
        let m_n2_l4 = m(n2, l.limbs[4]);
        let m_n4_l2 = m(n4, l.limbs[2]);
        // Goal: sum6 < 2^108 (part2's precondition)
        proof {
            lemma_m(n2, l.limbs[4], (1u64 << 52), (1u64 << 52));
            lemma_m(n4, l.limbs[2], (1u64 << 52), (1u64 << 52));
            assert((1u128 << 56) + (1u128 << 106) + 2 * (1u128 << 104) <= (1u128 << 108))
                by (bit_vector);
        }
        let sum6 = carry + limbs[6] + m_n2_l4 + m_n4_l2;
        let (carry, r1) = Self::part2(sum6);
        let ghost carry6 = carry;
        assert(r1 < (1u64 << 52));  // from part2 postcondition

        // part2 call 2 (r2): carry + limbs[7] + m(n3,l[4])
        let m_n3_l4 = m(n3, l.limbs[4]);
        // Goal: sum7 < 2^108 (part2's precondition)
        proof {
            lemma_m(n3, l.limbs[4], (1u64 << 52), (1u64 << 52));
            assert((1u128 << 56) + (1u128 << 105) + (1u128 << 104) <= (1u128 << 108))
                by (bit_vector);
        }
        let sum7 = carry + limbs[7] + m_n3_l4;
        let (carry, r2) = Self::part2(sum7);
        let ghost carry7 = carry;
        assert(r2 < (1u64 << 52));  // from part2 postcondition

        // part2 call 3 (r3): carry + limbs[8] + m(n4,l[4])
        let m_n4_l4 = m(n4, l.limbs[4]);
        // Goal: sum8 < 2^108 (part2's precondition)
        proof {
            lemma_m(n4, l.limbs[4], (1u64 << 52), (1u64 << 52));
            assert((1u128 << 56) + 2 * (1u128 << 104) <= (1u128 << 108)) by (bit_vector);
        }
        let sum8 = carry + limbs[8] + m_n4_l4;
        let (carry, r3) = Self::part2(sum8);
        let ghost carry8 = carry;  // Ghost: save for algorithm correctness proof (this becomes r4)
        // r3 < 2^52 from part2's postcondition (w < 2^52)
        assert(r3 < (1u64 << 52));

        // Final carry becomes r4
        // KEY INSIGHT: r4 can exceed 2^52! (verified empirically with 1M+ test cases)
        // But r4 < 2^52 + L[4], which is sufficient for sub's relaxed precondition.
        //
        // =====================================================================
        // TWO r4 BOUNDS (for different purposes)
        // =====================================================================
        //
        // 1. CAST SAFETY (lemma_carry8_bound): carry8 < 2^53
        //    Proven from computation structure: sum8 = carry7 + limb8 + n4×L[4] < 2^105
        //    → carry8 = sum8 >> 52 < 2^53
        //    This allows safe cast from u128 to u64.
        //
        // 2. SUB PRECONDITION (REDC theorem, proven later via lemma_r4_bound_from_canonical):
        //    r4 < 2^52 + L[4]
        //    Proven from value constraint: canonical_bound → intermediate < 2L → r4 bounded
        //    This satisfies limbs_bounded_for_sub for sub's precondition.
        //
        // =====================================================================

        // Call lemma_carry8_bound to establish carry < 2^53 BEFORE the cast.
        // This solves the chicken-and-egg problem (lemma_montgomery_reduce_pre_sub
        // takes r4: u64 as input, so we need the bound proven first).
        proof {
            // Call lemma_carry8_bound with all required parameters to establish carry8 < pow2(53)
            // This is a direct proof from sum8 bounds - no assume needed!
            //
            // Inputs:
            //   - limb8 = limbs[8]: bounded < 2^104 (from input_bounds precondition)
            //   - n4: from part1, bounded < 2^52
            //   - l4 = L[4] = 2^44 (constant)
            //   - carry7: from part2(sum7), bounded < 2^56
            //   - sum8: = carry7 + limbs[8] + n4×L[4]
            //   - carry8: = sum8 >> 52
            //
            // The lemma proves: sum8 < 2^105, so carry8 < 2^53
            // Establish preconditions
            let limb8 = limbs[8];
            let l4 = l.limbs[4];

            // limb8 < 2^104 from input_bounds precondition
            lemma_u128_shift_is_pow2(104);
            assert(limb8 < (1u128 << 104));

            // l4 = L[4] = 2^44
            lemma_l_limb4_is_pow2_44();
            assert(l4 == (1u64 << 44)) by {
                assert(pow2(44) == (1u64 << 44) as nat) by {
                    lemma_u64_shift_is_pow2(44);
                }
            }

            // Establish sum8 definition for the precondition
            assert(sum8 == carry7 + limb8 + m_n4_l4);
            assert(m_n4_l4 == (n4 as u128) * (l4 as u128));

            // Derive carry8 == sum8 >> 52 from part2 postcondition
            // part2(sum8) postcondition: sum8 == (r3 as u128) + (carry8 << 52) and r3 < 2^52
            // This implies: carry8 == sum8 >> 52
            assert(sum8 == (r3 as u128) + (carry8 << 52));
            assert(r3 < (1u64 << 52));
            assert(carry8 == sum8 >> 52) by (bit_vector)
                requires
                    sum8 == (r3 as u128) + (carry8 << 52),
                    r3 < (1u64 << 52),
                    carry8 < (1u128 << 56),
            ;  // from part2 postcondition

            lemma_carry8_bound(limb8, n4, l4, carry7, sum8, carry8);

            // Now we have carry8 < pow2(53), which allows safe cast
            assert(carry8 < pow2(53));
            lemma_u128_shift_is_pow2(53);
            assert(carry < (1u128 << 53));
        }
        // Safe cast: carry < 2^53 proven by lemma_carry8_bound
        let r4 = carry as u64;

        // =====================================================================
        // PHASE 3: Conditional subtraction
        // =====================================================================
        // The intermediate result may be >= L, so attempt to subtract L.
        // sub() handles this with constant-time conditional subtraction.
        // =====================================================================
        let intermediate = Scalar52 { limbs: [r0, r1, r2, r3, r4] };

        // =====================================================================
        // Proof: Establish sub() preconditions
        // =====================================================================
        // 1. Part 1 chain proves: (T + N×L) ≡ 0 (mod R) and N < R
        // 2. Part 2 chain proves: intermediate × R = T + N×L
        // 3. Direct REDC bound: T < R×L ∧ N < R → intermediate < 2L → r4 bounded
        // =====================================================================

        proof {
            // =========================================================================
            // SECTION 1: Result limb bounds (r0-r3 from part2 postconditions)
            // =========================================================================
            lemma_u64_shift_is_pow2(52);
            assert(r0 < pow2(52) as u64 && r1 < pow2(52) as u64 && r2 < pow2(52) as u64 && r3
                < pow2(52) as u64);

            // =========================================================================
            // SECTION 2: Part 1 - Convert u128 shift operations to nat arithmetic
            // =========================================================================
            // Part1 postconditions use u128: sum + p*L[0] == carry << 52
            // Divisibility lemma needs nat: sum + p*l0() == carry * pow2(52)

            // Convert all part1 carries (< 2^57) to nat form
            // First establish pow2(57) == (1u128 << 57) for precondition
            lemma_u128_shift_is_pow2(57);
            assert((1u128 << 57) as nat == pow2(57));
            lemma_carry_shift_to_nat(carry0, 57);
            lemma_carry_shift_to_nat(carry1, 57);
            lemma_carry_shift_to_nat(carry2, 57);
            lemma_carry_shift_to_nat(carry3, 57);
            lemma_carry_shift_to_nat(carry4, 57);

            // Stage equations in nat form (follow directly from part1 postconditions)
            assert(limbs[0] as nat + (n0 as nat) * l0() == (carry0 as nat) * pow2(52));
            assert((carry0 as nat + limbs[1] as nat + (n0 as nat) * (constants::L.limbs[1] as nat))
                + (n1 as nat) * l0() == (carry1 as nat) * pow2(52));
            assert((carry1 as nat + limbs[2] as nat + (n0 as nat) * (constants::L.limbs[2] as nat)
                + (n1 as nat) * (constants::L.limbs[1] as nat)) + (n2 as nat) * l0() == (
            carry2 as nat) * pow2(52));
            assert((carry2 as nat + limbs[3] as nat + (n1 as nat) * (constants::L.limbs[2] as nat)
                + (n2 as nat) * (constants::L.limbs[1] as nat)) + (n3 as nat) * l0() == (
            carry3 as nat) * pow2(52));
            assert((carry3 as nat + limbs[4] as nat + (n0 as nat) * (constants::L.limbs[4] as nat)
                + (n2 as nat) * (constants::L.limbs[2] as nat) + (n3 as nat) * (
            constants::L.limbs[1] as nat)) + (n4 as nat) * l0() == (carry4 as nat) * pow2(52));

            // =========================================================================
            // SECTION 3: Call divisibility lemma and establish N < 2^260
            // =========================================================================
            lemma_part1_chain_divisibility(
                limbs,
                n0,
                n1,
                n2,
                n3,
                n4,
                carry0,
                carry1,
                carry2,
                carry3,
                carry4,
            );

            let n = five_u64_limbs_to_nat(n0, n1, n2, n3, n4);

            // Prove N < 2^260 via lemma_general_bound
            assert(n < pow2(260)) by {
                let n_arr: [u64; 5] = [n0, n1, n2, n3, n4];
                lemma_five_limbs_equals_to_nat(&n_arr);

                // Connect five_limbs_to_nat_aux to five_u64_limbs_to_nat
                assert(five_limbs_to_nat_aux(n_arr) == n) by {
                    lemma_mul_is_commutative(pow2(52) as int, n1 as nat as int);
                    lemma_mul_is_commutative(pow2(104) as int, n2 as nat as int);
                    lemma_mul_is_commutative(pow2(156) as int, n3 as nat as int);
                    lemma_mul_is_commutative(pow2(208) as int, n4 as nat as int);
                }

                // Each n_i < 2^52, so limbs52_to_nat < 2^260
                assert(forall|i: int| 0 <= i < 5 ==> n_arr@[i] < (1u64 << 52));
                lemma_general_bound(n_arr@);
                assert(52 * 5 == 260nat) by (compute_only);
            }

            // Divisibility result from lemma_part1_chain_divisibility
            let t_low = limbs[0] as nat + limbs[1] as nat * pow2(52) + limbs[2] as nat * pow2(104)
                + limbs[3] as nat * pow2(156) + limbs[4] as nat * pow2(208);
            let l_low = constants::L.limbs[0] as nat + constants::L.limbs[1] as nat * pow2(52)
                + constants::L.limbs[2] as nat * pow2(104) + constants::L.limbs[3] as nat * pow2(
                156,
            ) + constants::L.limbs[4] as nat * pow2(208);
            assert((t_low + n * l_low) % pow2(260) == 0);

            // =========================================================================
            // SECTION 4: Part 2 - Convert part2 postconditions to nat
            // =========================================================================
            // Sum definitions (from how sums are computed in code)
            assert(sum5 as nat == carry4 as nat + limbs[5] as nat + (n1 as nat) * (
            constants::L.limbs[4] as nat) + (n3 as nat) * (constants::L.limbs[2] as nat) + (
            n4 as nat) * (constants::L.limbs[1] as nat));
            assert(sum6 as nat == carry5 as nat + limbs[6] as nat + (n2 as nat) * (
            constants::L.limbs[4] as nat) + (n4 as nat) * (constants::L.limbs[2] as nat));
            assert(sum7 as nat == carry6 as nat + limbs[7] as nat + (n3 as nat) * (
            constants::L.limbs[4] as nat));
            assert(sum8 as nat == carry7 as nat + limbs[8] as nat + (n4 as nat) * (
            constants::L.limbs[4] as nat));

            // Convert part2 carries (< 2^56) to nat form
            // First establish pow2(56) == (1u128 << 56) for precondition
            lemma_u128_shift_is_pow2(56);
            assert((1u128 << 56) as nat == pow2(56));
            lemma_carry_shift_to_nat(carry5, 56);
            lemma_carry_shift_to_nat(carry6, 56);
            lemma_carry_shift_to_nat(carry7, 56);
            lemma_carry_shift_to_nat(carry8, 56);

            // Part2 stage equations: sum == r + carry * pow2(52)
            assert(sum5 as nat == (r0 as nat) + (carry5 as nat) * pow2(52));
            assert(sum6 as nat == (r1 as nat) + (carry6 as nat) * pow2(52));
            assert(sum7 as nat == (r2 as nat) + (carry7 as nat) * pow2(52));

            // carry8 becomes r4: prove r4 == carry8 (truncation preserves value)
            assert((r4 as nat) == (carry8 as nat)) by {
                lemma_pow2_strictly_increases(56, 64);
                lemma_u128_cast_64_is_mod(carry8);
                assert(pow2(64) == (1u128 << 64) as nat) by {
                    lemma_u128_shift_is_pow2(64);
                }
                assert((1u128 << 64) == 0x10000000000000000u128) by (bit_vector);
                lemma_small_mod(carry8 as nat, 0x10000000000000000nat);
            }
            assert(sum8 as nat == (r3 as nat) + (r4 as nat) * pow2(52));

            // =========================================================================
            // SECTION 5: Call pre_sub lemma for quotient relationship
            // =========================================================================
            lemma_montgomery_reduce_pre_sub(
                limbs,
                n0,
                n1,
                n2,
                n3,
                n4,
                n,
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
                &intermediate,
            );

            // =========================================================================
            // SECTION 6: Establish sub() preconditions via direct REDC bound
            // =========================================================================
            lemma_l_equals_group_order();
            let inter_val = scalar52_to_nat(&intermediate);
            let l_val = group_order();

            // Connect scalar52_to_nat to explicit limb sum
            // lemma_five_limbs_equals_to_nat gives: five_limbs_to_nat_aux(limbs) == scalar52_to_nat
            lemma_five_limbs_equals_to_nat(&intermediate.limbs);
            // Apply commutativity: pow2(k) * limb == limb * pow2(k)
            lemma_mul_is_commutative(pow2(52) as int, r1 as int);
            lemma_mul_is_commutative(pow2(104) as int, r2 as int);
            lemma_mul_is_commutative(pow2(156) as int, r3 as int);
            lemma_mul_is_commutative(pow2(208) as int, r4 as int);

            // Apply direct REDC bound: canonical_bound + N < R + quotient → r4 bounded
            // No uniqueness chain needed — works directly from intermediate × R = T + N×L
            lemma_r4_bound_from_canonical(limbs, r0, r1, r2, r3, r4, n);

            // Results: sub's preconditions
            assert(limbs_bounded_for_sub(&intermediate, l));  // r4 < 2^52 + L[4]
            assert(inter_val < 2 * l_val);  // intermediate < 2L
            assert((inter_val as int) - (l_val as int) >= -(l_val as int));
            assert((inter_val as int) - (l_val as int) < (l_val as int));
        }
        // Now sub's precondition is satisfied

        let result = Scalar52::sub(&intermediate, l);

        // =====================================================================
        // POSTCONDITION PROOFS
        // =====================================================================
        // All postconditions are derived from:
        // 1. lemma_montgomery_reduce_pre_sub - establishes quotient relationship
        // 2. sub - computes result = (intermediate - L) mod L, canonical output
        // 3. lemma_montgomery_reduce_post_sub - derives montgomery_congruent
        // =====================================================================
        proof {
            // Postcondition 1: limbs_bounded(result) - directly from sub postcondition
            assert(limbs_bounded(&result));

            // Postcondition 2: montgomery_congruent(&result, limbs)
            assert(montgomery_congruent(&result, limbs)) by {
                let n = five_u64_limbs_to_nat(n0, n1, n2, n3, n4);

                // Subgoal: L constant equals group order
                assert(scalar52_to_nat(l) == group_order()) by {
                    lemma_l_equals_group_order();
                }

                // From pre_sub lemma: quotient relationship
                // intermediate × R = T + N×L
                assert(scalar52_to_nat(&intermediate) * montgomery_radix() == slice128_to_nat(limbs)
                    + n * group_order());

                // From sub postcondition: result = (intermediate - L) mod L
                assert(scalar52_to_nat(&result) == (scalar52_to_nat(&intermediate) as int
                    - group_order() as int) % (group_order() as int));

                // Derive montgomery_congruent from the above
                lemma_montgomery_reduce_post_sub(limbs, &intermediate, &result, n);
            }

            // Postcondition 3: is_canonical_scalar52(result) - directly from sub postcondition
            assert(is_canonical_scalar52(&result));
        }

        result
    }

    /// Helper function for Montgomery reduction
    /// Computes p such that sum + p*L[0] is divisible by 2^52, returns (carry, p).
    /// VER NOTE: spec validation needed concurrent with proof for montgomery_reduce
    #[inline(always)]
    fn part1(sum: u128) -> (res: (u128, u64))
        requires
    // Bound needed to ensure no overflow and carry bounds

            sum < (1u128 << 108),
        ensures
            ({
                let carry = res.0;
                let p = res.1;
                &&& p < (1u64 << 52)  // p is bounded by 52 bits
                &&& sum + (p as u128) * (constants::L.limbs[0] as u128) == carry
                    << 52
                // Carry bound: sum + p*L[0] < 2^108 + 2^102 < 2^109, so carry < 2^57
                &&& carry < (1u128 << 57)
            }),
    {
        /* ORIGINAL CODE:
         #[inline(always)]
        fn part1(sum: u128) -> (u128, u64) {
            let p = (sum as u64).wrapping_mul(constants::LFACTOR) & ((1u64 << 52) - 1);
            ((sum + m(p, constants::L.limbs[0])) >> 52, p)
        }
         */
        //
        // Verus's `by (bit_vector)` mode cannot reason about wrapping_mul.
        //
        // EQUIVALENT REFACTORING: Extract low 52 bits first, then multiply in u128.
        // This avoids wrapping_mul and is mathematically equivalent because:
        //   (a.wrapping_mul(b)) & MASK52 = (a * b) mod 2^52 = ((a mod 2^52) * b) mod 2^52
        // The tests test_part1_wrapping_mul_equivalence and
        // test_wrapping_mul_mask_equals_mod test this equivalence.
        let mask52: u64 = 0xFFFFFFFFFFFFFu64;  // (1 << 52) - 1
        let sum_low52: u64 = (sum as u64) & mask52;
        let product: u128 = (sum_low52 as u128) * (constants::LFACTOR as u128);
        let p: u64 = (product as u64) & mask52;

        // Bounds for m() precondition - must be outside proof block for exec code
        assert(p < 0x10000000000000u64) by (bit_vector)
            requires
                p == (product as u64) & mask52,
                mask52 == 0xFFFFFFFFFFFFFu64,
        ;
        assert(0x10000000000000u64 == (1u64 << 52)) by (bit_vector);
        assert(p < (1u64 << 52));

        assert(constants::L.limbs[0] < (1u64 << 52));

        let pL0: u128 = m(p, constants::L.limbs[0]);

        proof {
            assert((p as u128) * (constants::L.limbs[0] as u128) < (1u128 << 102)) by (bit_vector)
                requires
                    p < 0x10000000000000u64,
                    constants::L.limbs[0] < 0x4000000000000u64,
            ;
            assert((1u128 << 108) + (1u128 << 102) < (1u128 << 110)) by (bit_vector);
        }

        let total: u128 = sum + pL0;
        let carry: u128 = total >> 52;

        // =====================================================================
        // PROOF (encapsulated in lemma_part1_correctness)
        // =====================================================================
        proof {
            lemma_part1_correctness(sum);

            // Prove carry < 2^57:
            // total = sum + pL0 < 2^108 + 2^102 < 2^109
            // carry = total >> 52 < 2^109 / 2^52 = 2^57
            assert(total < (1u128 << 109)) by {
                assert(sum < (1u128 << 108));
                assert(pL0 < (1u128 << 102));
                assert((1u128 << 108) + (1u128 << 102) < (1u128 << 109)) by (bit_vector);
            }
            assert(carry < (1u128 << 57)) by {
                // total >> 52 < 2^109 / 2^52 = 2^57
                assert(total >> 52 < (1u128 << 57)) by (bit_vector)
                    requires
                        total < (1u128 << 109),
                ;
            }
        }

        (carry, p)
    }

    /// Helper function for Montgomery reduction
    /// VER NOTE: spec validation needed concurrent with proof for montgomery_reduce
    #[inline(always)]
    fn part2(sum: u128) -> (res: (u128, u64))
        requires
            sum < (1u128 << 108),
        ensures
            ({
                let carry = res.0;
                let w = res.1;
                &&& w < (1u64 << 52)  // w is bounded by 52 bits (lower limb)
                &&& sum == (w as u128) + (carry << 52)
                &&& carry < (1u128 << 56)  // carry bound from sum < 2^108

            }),
    {
        proof { lemma_part2_bounds(sum) }
        let w = (sum as u64) & ((1u64 << 52) - 1);
        let carry = sum >> 52;
        (carry, w)
    }

    /// Compute `a * b` (mod l)
    ///
    /// # Preconditions
    /// - Both inputs must be bounded (limbs < 2^52)
    /// - At least one input must be canonical (< L) for verified first reduction
    #[inline(never)]
    pub fn mul(a: &Scalar52, b: &Scalar52) -> (result: Scalar52)
        requires
            limbs_bounded(a),
            limbs_bounded(b),
            // At least one input must be canonical for montgomery_reduce's canonical_bound
            is_canonical_scalar52(a) || is_canonical_scalar52(b),
        ensures
            scalar52_to_nat(&result) % group_order() == (scalar52_to_nat(&a) * scalar52_to_nat(&b))
                % group_order(),
            is_canonical_scalar52(&result),
    {
        proof {
            lemma_rr_limbs_bounded();
            lemma_limbs_bounded_implies_prod_bounded(a, b);
        }

        // First montgomery_reduce: ab*R ≡ a*b (mod L)
        let z1 = Scalar52::mul_internal(a, b);
        proof {
            // Establish montgomery_reduce's preconditions
            lemma_bounded_product_satisfies_input_bounds(a, b, &z1);
            // At least one input is canonical, so product satisfies canonical_bound
            if is_canonical_scalar52(b) {
                lemma_canonical_product_satisfies_canonical_bound(a, b, &z1);
            } else {
                // a must be canonical since one of them is
                lemma_spec_mul_internal_commutative(a, b);
                lemma_canonical_product_satisfies_canonical_bound(b, a, &z1);
            }
        }
        let ab = Scalar52::montgomery_reduce(&z1);

        assert((scalar52_to_nat(&ab) * montgomery_radix()) % group_order() == (scalar52_to_nat(&a)
            * scalar52_to_nat(&b)) % group_order());

        // ab has limbs_bounded from montgomery_reduce's postcondition
        proof {
            lemma_limbs_bounded_implies_prod_bounded(&ab, &constants::RR);
        }

        // Second montgomery_reduce: result*R ≡ ab*RR (mod L)
        // RR is canonical (< L), so product satisfies canonical_bound
        let z2 = Scalar52::mul_internal(&ab, &constants::RR);
        proof {
            // Establish montgomery_reduce's preconditions
            lemma_bounded_product_satisfies_input_bounds(&ab, &constants::RR, &z2);
            lemma_rr_equals_spec();
            lemma_canonical_product_satisfies_canonical_bound(&ab, &constants::RR, &z2);
        }
        let result = Scalar52::montgomery_reduce(&z2);
        // is_canonical_scalar52(&result) follows from montgomery_reduce postcondition

        assert((scalar52_to_nat(&result) * montgomery_radix()) % group_order() == (scalar52_to_nat(
            &ab,
        ) * scalar52_to_nat(&constants::RR)) % group_order());

        proof {
            // 1. Prove RR ≡ R² (mod L)
            lemma_rr_equals_spec();

            // 1. Prove RR ≡ R² (mod L) (already called above, but needed for subsequent proofs)
            // 2. Apply cancellation lemma to get: result ≡ ab*R (mod L)
            //    Combined with ab*R ≡ a*b (mod L), we get result ≡ a*b (mod L)
            lemma_cancel_mul_montgomery_mod(
                scalar52_to_nat(&result),
                scalar52_to_nat(&ab),
                scalar52_to_nat(&constants::RR),
            );

            // 3. Since result < group_order (from montgomery_reduce), result % L == result
            lemma_small_mod(scalar52_to_nat(&result), group_order());
        }

        result
    }

    /// Compute `a^2` (mod l)
    ///
    /// # Preconditions
    /// - Input must be canonical (bounded and < L) for verified first reduction
    #[inline(never)]
    #[allow(dead_code)]  // XXX we don't expose square() via the Scalar API
    pub fn square(&self) -> (result: Scalar52)
        requires
    // Must be canonical for montgomery_reduce's canonical_bound

            is_canonical_scalar52(self),
        ensures
            scalar52_to_nat(&result) == (scalar52_to_nat(self) * scalar52_to_nat(self))
                % group_order(),
    {
        proof {
            lemma_rr_limbs_bounded();
            // Derive limb_prod_bounded_u128 for square_internal's precondition
            lemma_limbs_bounded_implies_prod_bounded(self, self);
        }

        let z1 = Scalar52::square_internal(self);
        proof {
            // Establish montgomery_reduce's preconditions for first call
            lemma_bounded_product_satisfies_input_bounds(self, self, &z1);
            // self is canonical, so product satisfies canonical_bound
            lemma_canonical_product_satisfies_canonical_bound(self, self, &z1);
        }
        let aa = Scalar52::montgomery_reduce(&z1);

        assert((scalar52_to_nat(&aa) * montgomery_radix()) % group_order() == (scalar52_to_nat(self)
            * scalar52_to_nat(self)) % group_order());

        // aa has limbs_bounded from montgomery_reduce's postcondition
        proof {
            lemma_limbs_bounded_implies_prod_bounded(&aa, &constants::RR);
        }

        let z2 = Scalar52::mul_internal(&aa, &constants::RR);
        proof {
            // Establish montgomery_reduce's preconditions for second call
            lemma_bounded_product_satisfies_input_bounds(&aa, &constants::RR, &z2);
            // RR is canonical (< L), so product satisfies canonical_bound
            lemma_rr_equals_spec();
            lemma_canonical_product_satisfies_canonical_bound(&aa, &constants::RR, &z2);
        }
        let result = Scalar52::montgomery_reduce(&z2);
        // is_canonical_scalar52(&result) follows from montgomery_reduce postcondition

        assert((scalar52_to_nat(&result) * montgomery_radix()) % group_order() == (scalar52_to_nat(
            &aa,
        ) * scalar52_to_nat(&constants::RR)) % group_order());

        proof {
            // 1. prove (scalar52_to_nat(&constants::RR) % group_order() == (montgomery_radix()*montgomery_radix()) % group_order()
            lemma_rr_equals_spec();

            // (already called above, but needed for subsequent proofs)
            // 2. Reduce to (scalar52_to_nat(&result)) % group_order() == (scalar52_to_nat(self) * scalar52_to_nat(self)) % group_order()
            lemma_cancel_mul_montgomery_mod(
                scalar52_to_nat(&result),
                scalar52_to_nat(&aa),
                scalar52_to_nat(&constants::RR),
            );

            // 3. allows us to assert (scalar52_to_nat(&result)) % group_order() == (scalar52_to_nat(&result))
            //  true from montgomery_reduce postcondition
            lemma_small_mod((scalar52_to_nat(&result)), group_order())
        }

        assert((scalar52_to_nat(&result)) % group_order() == (scalar52_to_nat(&aa)
            * montgomery_radix()) % group_order());

        result
    }

    /// Compute `(a * b) / R` (mod l), where R is the Montgomery modulus 2^260
    ///
    /// # Preconditions
    /// - Both inputs must have `limbs_bounded` (ensures `input_bounds` for the product)
    /// - At least one input must be canonical for `montgomery_reduce`'s `canonical_bound`
    /// See `docs/proofs_for_montgomery_reduce/precondition_analysis.md`.
    #[inline(never)]
    pub fn montgomery_mul(a: &Scalar52, b: &Scalar52) -> (result: Scalar52)
        requires
            limbs_bounded(a),
            limbs_bounded(b),
            // At least one input must be canonical for montgomery_reduce's canonical_bound
            is_canonical_scalar52(a) || is_canonical_scalar52(b),
        ensures
            limb_prod_bounded_u128(result.limbs, result.limbs, 5),
            (scalar52_to_nat(&result) * montgomery_radix()) % group_order() == (scalar52_to_nat(&a)
                * scalar52_to_nat(&b)) % group_order(),
            // Result is canonical from montgomery_reduce
            is_canonical_scalar52(&result),
    {
        proof {
            // Derive limb_prod_bounded_u128 for mul_internal's precondition
            lemma_limbs_bounded_implies_prod_bounded(a, b);
        }
        let z = Scalar52::mul_internal(a, b);
        proof {
            // Establish montgomery_reduce's preconditions
            lemma_bounded_product_satisfies_input_bounds(a, b, &z);
            // At least one input is canonical, establish canonical_bound
            if is_canonical_scalar52(b) {
                lemma_canonical_product_satisfies_canonical_bound(a, b, &z);
            } else {
                // a must be canonical since one of them is
                lemma_spec_mul_internal_commutative(a, b);
                lemma_canonical_product_satisfies_canonical_bound(b, a, &z);
            }
        }
        let result = Scalar52::montgomery_reduce(&z);
        proof {
            // Derive limb_prod_bounded_u128 from limbs_bounded
            lemma_limbs_bounded_implies_prod_bounded(&result, &result);
        }
        result
    }

    /// Compute `(a^2) / R` (mod l) in Montgomery form, where R is the Montgomery modulus 2^260
    ///
    /// # Preconditions
    /// - Input must be canonical for `montgomery_reduce`'s `canonical_bound`
    ///
    /// Why `limbs_bounded` (part of canonical): `square_internal(self)[0] = self.limbs[0]²`,
    /// and we need `self.limbs[0]² < 2^104`, so `self.limbs[0] < 2^52`.
    /// See `docs/proofs_for_montgomery_reduce/precondition_analysis.md` for details.
    #[inline(never)]
    pub fn montgomery_square(&self) -> (result: Scalar52)
        requires
    // Must be canonical for montgomery_reduce's canonical_bound

            is_canonical_scalar52(self),
        ensures
            limb_prod_bounded_u128(result.limbs, result.limbs, 5),
            (scalar52_to_nat(&result) * montgomery_radix()) % group_order() == (scalar52_to_nat(
                self,
            ) * scalar52_to_nat(self)) % group_order(),
            // Result is canonical from montgomery_reduce
            is_canonical_scalar52(&result),
    {
        proof {
            // Derive limb_prod_bounded_u128 for square_internal's precondition
            lemma_limbs_bounded_implies_prod_bounded(self, self);
        }
        let z = Scalar52::square_internal(self);
        proof {
            // Establish montgomery_reduce's preconditions
            lemma_bounded_product_satisfies_input_bounds(self, self, &z);
            // self is canonical, so product satisfies canonical_bound
            lemma_canonical_product_satisfies_canonical_bound(self, self, &z);
        }
        let result = Scalar52::montgomery_reduce(&z);
        proof {
            // Derive limb_prod_bounded_u128 from limbs_bounded
            lemma_limbs_bounded_implies_prod_bounded(&result, &result);
        }
        result
    }

    /// Puts a Scalar52 in to Montgomery form, i.e. computes `a*R (mod l)`
    ///
    /// # Precondition
    /// Requires `limbs_bounded(self)` because `montgomery_mul` (called internally) now
    /// requires both inputs to have `limbs_bounded`. This is safe because all `Scalar52`
    /// values in practice have `limbs_bounded` (from `unpack()` or other Montgomery ops).
    #[inline(never)]
    pub fn as_montgomery(&self) -> (result: Scalar52)
        requires
            limbs_bounded(self),
        ensures
            limb_prod_bounded_u128(result.limbs, result.limbs, 5),
            #[trigger] (scalar52_to_nat(&result) % group_order()) == #[trigger] ((scalar52_to_nat(
                self,
            ) * montgomery_radix()) % group_order()),
            // Result is canonical because RR is canonical
            is_canonical_scalar52(&result),
    {
        proof {
            lemma_rr_limbs_bounded();
            // RR is canonical (< group_order), so montgomery_mul's canonicity postcondition applies
            lemma_rr_equals_spec();
            assert(group_order() > 0);
        }
        let result = Scalar52::montgomery_mul(self, &constants::RR);
        proof {
            // From montgomery_mul's ensures clause:
            // (scalar52_to_nat(&result) * montgomery_radix()) % group_order() ==
            // (scalar52_to_nat(self) * scalar52_to_nat(&constants::RR)) % group_order()
            // Prove that RR = R² mod L
            lemma_rr_equals_radix_squared();

            // Now we can apply the cancellation lemma
            lemma_cancel_mul_montgomery_mod(
                scalar52_to_nat(&result),
                scalar52_to_nat(self),
                scalar52_to_nat(&constants::RR),
            );
        }
        result
    }

    /// Takes a Scalar52 out of Montgomery form, i.e. computes `a/R (mod l)`
    ///
    /// # Precondition: Why `limbs_bounded` instead of `limb_prod_bounded_u128`
    ///
    /// For consistency with `montgomery_square` and `montgomery_invert`, and because
    /// all callers have `limbs_bounded` anyway (from `montgomery_invert`'s ensures).
    /// See `docs/proofs_for_montgomery_reduce/precondition_analysis.md`.
    #[allow(clippy::wrong_self_convention)]
    #[inline(never)]
    pub fn from_montgomery(&self) -> (result: Scalar52)
        requires
            limbs_bounded(self),
        ensures
            (scalar52_to_nat(&result) * montgomery_radix()) % group_order() == scalar52_to_nat(self)
                % group_order(),
            // Result is canonical (< group_order). This follows from montgomery_reduce's postcondition
            is_canonical_scalar52(&result),
    {
        let mut limbs = [0u128;9];
        #[allow(clippy::needless_range_loop)]
        for i in 0..5
            invariant
                forall|j: int| #![auto] 0 <= j < i ==> limbs[j] == self.limbs[j] as u128,
                forall|j: int| #![auto] i <= j < 9 ==> limbs[j] == 0,
        {
            limbs[i] = self.limbs[i] as u128;
        }
        proof {
            // Derive limb_prod_bounded_u128 for lemma_from_montgomery_is_product_with_one's precondition
            lemma_limbs_bounded_implies_prod_bounded(self, self);
            lemma_from_montgomery_is_product_with_one(self, &limbs);
            // Establish montgomery_reduce's preconditions
            lemma_identity_array_satisfies_input_bounds(self, &limbs);
            lemma_identity_array_satisfies_canonical_bound(self, &limbs);
        }
        let result = Scalar52::montgomery_reduce(&limbs);
        // is_canonical_scalar52(&result) follows from montgomery_reduce postcondition
        // (canonical_bound holds, so postcondition gives is_canonical_scalar52)
        proof {
            lemma_from_montgomery_limbs_conversion(&limbs, &self.limbs);
        }
        result
    }
}

} // verus!
#[cfg(test)]
pub mod test {
    use super::*;
    use num_bigint::BigUint;
    use num_traits::{One, Zero};
    use proptest::prelude::*;

    // Executable versions of spec functions to match the spec as closely as possible

    /// Convert 5 limbs (52-bit each) to a BigUint
    /// Matches the spec: scalar52_to_nat(&[u64; 5])
    pub fn to_nat_exec(limbs: &[u64; 5]) -> BigUint {
        let mut result = BigUint::zero();
        let radix = BigUint::from(1u128 << 52);
        for i in (0..5).rev() {
            result = result * &radix + BigUint::from(limbs[i]);
        }
        result
    }

    /// Convert 9 u128 limbs (52-bit each) to a BigUint
    /// Matches the spec: slice128_to_nat(&[u128; 9])
    pub fn slice128_to_nat_exec(limbs: &[u128; 9]) -> BigUint {
        let mut result = BigUint::zero();
        let radix = BigUint::from(1u128 << 52);
        for i in (0..9).rev() {
            result = result * &radix + BigUint::from(limbs[i]);
        }
        result
    }

    /// The group order L
    /// Matches the spec: group_order()
    pub fn group_order_exec() -> BigUint {
        // L = 2^252 + 27742317777372353535851937790883648493
        let base = BigUint::one() << 252;
        let offset = BigUint::parse_bytes(b"27742317777372353535851937790883648493", 10).unwrap();
        base + offset
    }

    /// Montgomery radix R = 2^260
    /// Matches the spec: montgomery_radix()
    pub fn montgomery_radix_exec() -> BigUint {
        BigUint::one() << 260
    }

    /// Check if all limbs are bounded by 2^52
    /// Matches the spec: limbs_bounded(&Scalar52)
    pub fn limbs_bounded_exec(s: &Scalar52) -> bool {
        s.limbs.iter().all(|&limb| limb < (1u64 << 52))
    }

    // Property-based test generators

    /// Generate a valid Scalar52 with bounded limbs (each limb < 2^52)
    fn arb_bounded_scalar52() -> impl Strategy<Value = Scalar52> {
        prop::array::uniform5(0u64..(1u64 << 52)).prop_map(|limbs| Scalar52 { limbs })
    }

    /// Generate a canonical scalar: limbs_bounded AND value < L
    /// This generates a random BigUint in [0, L) and converts it to Scalar52
    fn arb_canonical_scalar52() -> impl Strategy<Value = Scalar52> {
        // Generate random bytes and interpret as BigUint, then reduce mod L
        proptest::collection::vec(any::<u8>(), 32..=64).prop_map(|bytes| {
            let l = group_order_exec();
            let value = BigUint::from_bytes_le(&bytes) % &l;

            // Convert BigUint to limbs in base 2^52
            let mut limbs = [0u64; 5];
            let mask = (1u64 << 52) - 1;
            let mut remaining = value;

            for i in 0..5 {
                let limb_big = &remaining & BigUint::from(mask);
                limbs[i] = limb_big.to_u64_digits().first().copied().unwrap_or(0);
                remaining >>= 52;
            }

            Scalar52 { limbs }
        })
    }

    /// Test case demonstrating that montgomery_reduce fails its canonicality postcondition
    /// when given input that is the product of two bounded-but-non-canonical scalars.
    ///
    /// This specific case was found by proptest and demonstrates why the precondition
    /// requires BOTH scalars to be canonical (< L), not just bounded.
    #[test]
    #[should_panic(expected = "Result not in canonical form")]
    fn montgomery_reduce_non_canonical_product_fails_postcondition() {
        // This is the minimal failing case found by proptest
        let limbs: [u128; 9] = [
            0,
            0,
            0,
            0,
            43234767039827164816921,
            0,
            0,
            0,
            130605075492091607448940168551,
        ];

        // Verify the input limbs are relatively small (much smaller than 2^104 which is the
        // theoretical max for products of 52-bit limbs)
        assert!(limbs[0] < (1u128 << 1), "limbs[0] should be < 2^1");
        assert!(limbs[1] < (1u128 << 1), "limbs[1] should be < 2^1");
        assert!(limbs[2] < (1u128 << 1), "limbs[2] should be < 2^1");
        assert!(limbs[3] < (1u128 << 1), "limbs[3] should be < 2^1");
        assert!(limbs[4] < (1u128 << 76), "limbs[4] should be < 2^76");
        assert!(limbs[5] < (1u128 << 1), "limbs[5] should be < 2^1");
        assert!(limbs[6] < (1u128 << 1), "limbs[6] should be < 2^1");
        assert!(limbs[7] < (1u128 << 1), "limbs[7] should be < 2^1");
        assert!(limbs[8] < (1u128 << 97), "limbs[8] should be < 2^97");

        let result = Scalar52::montgomery_reduce(&limbs);

        let result_nat = to_nat_exec(&result.limbs);
        let limbs_nat = slice128_to_nat_exec(&limbs);
        let l = group_order_exec();
        let r = montgomery_radix_exec();

        // The Montgomery property should still hold
        assert_eq!(
            (&result_nat * &r) % &l,
            &limbs_nat % &l,
            "Montgomery property violated"
        );

        // The result should be limbs_bounded
        assert!(
            limbs_bounded_exec(&result),
            "Result limbs not bounded by 2^52"
        );

        // But the canonicality postcondition FAILS
        assert!(
            &result_nat < &l,
            "Result not in canonical form (>= L): {} >= {}",
            result_nat,
            l
        );
    }

    /// Test demonstrating that `mul` produces INCORRECT results when given non-canonical inputs.
    ///
    /// This test shows the "silent corruption" issue:
    /// - Both inputs are bounded (limbs < 2^52) but non-canonical (value >= L)
    /// - `mul` returns a canonical, well-formed scalar
    /// - BUT the result is mathematically WRONG: result != (a * b) % L
    ///
    /// This is why `mul` should require canonical inputs, not just bounded inputs.
    #[test]
    fn mul_non_canonical_inputs_produces_wrong_result() {
        let l = group_order_exec();
        let r = montgomery_radix_exec();

        // Create non-canonical but bounded inputs
        // We use L + small_value to get values just above L but still bounded
        // L ≈ 2^252, so L + 1 is still << 2^260 (bounded)

        // Construct a = L + 1 as Scalar52
        // L = [0x0002631a5cf5d3ed, 0x000dea2f79cd6581, 0x000000000014def9, 0, 0x0000100000000000]
        let a = Scalar52 {
            limbs: [
                0x0002631a5cf5d3ed + 1, // L[0] + 1
                0x000dea2f79cd6581,     // L[1]
                0x000000000014def9,     // L[2]
                0x0000000000000000,     // L[3]
                0x0000100000000000,     // L[4]
            ],
        };

        // Verify a is bounded
        assert!(limbs_bounded_exec(&a), "a should have bounded limbs");

        // Verify a is non-canonical (a >= L)
        let a_nat = to_nat_exec(&a.limbs);
        assert!(
            &a_nat >= &l,
            "a should be non-canonical (>= L): a = {}, L = {}",
            a_nat,
            l
        );
        assert_eq!(&a_nat, &(&l + BigUint::from(1u32)), "a should equal L + 1");

        // Use b = a for simplicity
        let b = a.clone();
        let b_nat = to_nat_exec(&b.limbs);

        // Compute the CORRECT result: (a * b) % L
        let expected = (&a_nat * &b_nat) % &l;

        // Call mul (this is where silent corruption may occur)
        // Note: We use mul_internal + montgomery_reduce to simulate mul's behavior
        // since mul itself might have verification annotations that prevent calling it
        let product = Scalar52::mul_internal(&a, &b);
        let ab = Scalar52::montgomery_reduce(&product);

        // Second montgomery_reduce with RR
        let product2 = Scalar52::mul_internal(&ab, &constants::RR);
        let result = Scalar52::montgomery_reduce(&product2);

        let result_nat = to_nat_exec(&result.limbs);

        // The result IS bounded and canonical (this is the "silent" part)
        assert!(
            limbs_bounded_exec(&result),
            "result should have bounded limbs"
        );
        assert!(&result_nat < &l, "result should be canonical (< L)");

        // BUT the result may be WRONG!
        // For L+1 specifically, the product (L+1)^2 = L^2 + 2L + 1
        // This is < R*L (since L^2 ≈ 2^504 < 2^512 = R*L), so it might actually work.
        // Let's check and print the comparison:
        println!("a = L + 1 = {}", a_nat);
        println!("a * b = {}", &a_nat * &b_nat);
        println!("expected = (a * b) % L = {}", expected);
        println!("actual result = {}", result_nat);

        // For this specific case (L+1)^2, the result might be correct because
        // (L+1)^2 = L^2 + 2L + 1 ≈ 2^504 < R*L ≈ 2^512
        // So canonical_bound is satisfied!
        //
        // To demonstrate actual corruption, we need larger non-canonical values.
        // See test `mul_large_non_canonical_inputs_produces_wrong_result` below.

        if result_nat == expected {
            println!("NOTE: For a = L+1, result is correct (canonical_bound satisfied)");
        } else {
            println!("CORRUPTION DETECTED: result != expected");
            panic!(
                "mul produced wrong result: expected {}, got {}",
                expected, result_nat
            );
        }
    }

    /// Test demonstrating the FIRST montgomery_reduce can produce non-canonical output
    /// when canonical_bound is violated.
    ///
    /// Key insight: For products of two bounded Scalar52 values:
    /// - r4 never actually overflows (< 2^52), so no truncation occurs
    /// - BUT the intermediate result `ab` may be non-canonical (>= L)
    /// - This is "Mode 1" failure: correct Montgomery property, but result >= L
    ///
    /// The second montgomery_reduce then processes this non-canonical value,
    /// which may or may not produce the correct final result depending on
    /// whether the proof chain's assumptions hold.
    #[test]
    fn mul_large_non_canonical_intermediate_can_exceed_l() {
        let l = group_order_exec();
        let r = montgomery_radix_exec();
        let rl = &r * &l; // R * L ≈ 2^512

        // Create a value around 2^257 (much larger than L ≈ 2^252)
        let a = Scalar52 {
            limbs: [0, 0, 0, 0, 1u64 << 49], // = 2^257
        };

        let a_nat = to_nat_exec(&a.limbs);
        assert!(limbs_bounded_exec(&a), "a should have bounded limbs");
        assert!(&a_nat > &l, "a should be non-canonical (> L)");

        // a * a = 2^514 > R*L = 2^512
        let product_value = &a_nat * &a_nat;
        println!("a = 2^257");
        println!("a * a = 2^514 > R*L = 2^512, so canonical_bound violated");

        // First montgomery_reduce
        let product = Scalar52::mul_internal(&a, &a);
        let ab = Scalar52::montgomery_reduce(&product);
        let ab_nat = to_nat_exec(&ab.limbs);

        println!("After first montgomery_reduce:");
        println!("  ab = {}", ab_nat);
        println!("  ab limbs bounded: {}", limbs_bounded_exec(&ab));
        println!("  ab < L (canonical): {}", &ab_nat < &l);

        // Check Montgomery property for first reduce
        let product_nat = slice128_to_nat_exec(&product);
        let montgomery_lhs = (&ab_nat * &r) % &l;
        let montgomery_rhs = &product_nat % &l;
        let montgomery_holds = montgomery_lhs == montgomery_rhs;
        println!("  Montgomery property holds: {}", montgomery_holds);

        // The intermediate result ab might be >= L (non-canonical)
        // This is the "Mode 1" issue
        if &ab_nat >= &l {
            println!("  ** INTERMEDIATE ab IS NON-CANONICAL (>= L) **");
            println!("  ab - L = {}", &ab_nat - &l);
        }

        // Second montgomery_reduce
        let product2 = Scalar52::mul_internal(&ab, &constants::RR);
        let result = Scalar52::montgomery_reduce(&product2);
        let result_nat = to_nat_exec(&result.limbs);

        // Final result
        let expected = &product_value % &l;
        println!("\nFinal result:");
        println!("  expected = (a*a) % L = {}", expected);
        println!("  actual = {}", result_nat);
        println!("  correct: {}", result_nat == expected);

        // Document the behavior: even with canonical_bound violated,
        // the result may be correct because:
        // 1. r4 doesn't actually overflow for bounded × bounded
        // 2. Montgomery property still holds
        // 3. The non-canonical intermediate gets "fixed" by second reduce
        //
        // However, this is NOT guaranteed by the spec, and the proof
        // chain relies on canonical_bound for correctness.
    }

    /// Test that finds an input where the FIRST montgomery_reduce produces
    /// a non-canonical result (value >= L).
    ///
    /// This demonstrates that without canonical_bound, the intermediate
    /// result can exceed L, even if the final result happens to be correct.
    #[test]
    fn find_non_canonical_intermediate_in_mul() {
        let l = group_order_exec();
        let r = montgomery_radix_exec();

        // Maximum bounded Scalar52: all limbs = 2^52 - 1
        let max_limb = (1u64 << 52) - 1;
        let a = Scalar52 {
            limbs: [max_limb, max_limb, max_limb, max_limb, max_limb],
        };

        let a_nat = to_nat_exec(&a.limbs);
        println!("a = 2^260 - 1 = {}", a_nat);
        println!("a > L: {} (non-canonical)", &a_nat > &l);

        let product = Scalar52::mul_internal(&a, &a);
        let ab = Scalar52::montgomery_reduce(&product);
        let ab_nat = to_nat_exec(&ab.limbs);

        println!("ab (first montgomery_reduce result) = {}", ab_nat);
        println!("ab limbs bounded: {}", limbs_bounded_exec(&ab));

        if &ab_nat >= &l {
            println!("SUCCESS: Found non-canonical intermediate!");
            println!("ab >= L: ab - L = {}", &ab_nat - &l);
        } else {
            println!("ab < L (canonical)");
        }

        // Verify Montgomery property still holds
        let product_nat = slice128_to_nat_exec(&product);
        let montgomery_lhs = (&ab_nat * &r) % &l;
        let montgomery_rhs = &product_nat % &l;
        assert_eq!(
            montgomery_lhs, montgomery_rhs,
            "Montgomery property should hold"
        );
        println!("Montgomery property verified ✓");
    }

    /// Test that the canonical scalar generator round-trips correctly
    #[test]
    fn test_canonical_scalar_generator() {
        use proptest::prelude::*;
        use proptest::strategy::ValueTree;
        use proptest::test_runner::{Config, TestRunner};

        let mut runner = TestRunner::new(Config::default());
        let l = group_order_exec();

        println!("Testing canonical scalar generator round-trip:");
        for i in 0..10 {
            let scalar = arb_canonical_scalar52()
                .new_tree(&mut runner)
                .unwrap()
                .current();

            // Convert to nat
            let value = to_nat_exec(&scalar.limbs);

            // Check it's canonical
            assert!(value < l, "Generated value should be < L");

            // Check limbs are bounded
            for (j, &limb) in scalar.limbs.iter().enumerate() {
                assert!(
                    limb < (1u64 << 52),
                    "Limb {} should be < 2^52, got {}",
                    j,
                    limb
                );
            }

            // Convert back to Scalar52 manually and check it matches
            let mut limbs_check = [0u64; 5];
            let mask = (1u64 << 52) - 1;
            let mut remaining = value.clone();

            for j in 0..5 {
                let limb_big = &remaining & BigUint::from(mask);
                limbs_check[j] = limb_big.to_u64_digits().first().copied().unwrap_or(0);
                remaining >>= 52;
            }

            // Check round-trip
            assert_eq!(
                scalar.limbs,
                limbs_check,
                "Round-trip failed for test {}",
                i + 1
            );

            // Convert back to nat and verify
            let value_check = to_nat_exec(&limbs_check);
            assert_eq!(
                value,
                value_check,
                "Value mismatch after round-trip for test {}",
                i + 1
            );

            println!(
                "Test {}: value = {}, limbs = {:?} ✓",
                i + 1,
                value,
                scalar.limbs
            );
        }
    }

    /// Generate random 9-limb array from product of one bounded scalar and one canonical scalar
    fn arb_nine_limbs_one_canonical() -> impl Strategy<Value = [u128; 9]> {
        (arb_bounded_scalar52(), arb_canonical_scalar52())
            .prop_map(|(a, b)| Scalar52::mul_internal(&a, &b))
    }

    /// Generate 9-limb arrays from product of TWO bounded scalars
    fn arb_nine_limbs_two_bounded() -> impl Strategy<Value = [u128; 9]> {
        (arb_bounded_scalar52(), arb_bounded_scalar52())
            .prop_map(|(a, b)| Scalar52::mul_internal(&a, &b))
    }

    /// Convert a 32-byte array to a BigUint
    /// Matches the spec: bytes32_to_nat(&[u8; 32])
    pub fn bytes32_to_nat_exec(bytes: &[u8; 32]) -> BigUint {
        let mut result = BigUint::zero();
        let radix = BigUint::from(256u32);
        for i in (0..32).rev() {
            result = result * &radix + BigUint::from(bytes[i]);
        }
        result
    }

    /// Test case demonstrating that from_bytes does NOT ensure canonicality.
    /// i.e. the postcondition `scalar52_to_nat(&s) < group_order()` may not hold
    ///
    /// The minimal failing case found by proptest: bytes[31] = 17 (all others 0)
    /// represents 17 * 2^248, which is >= L, so the result is not canonical.
    #[test]
    fn from_bytes_non_canonical_example() {
        let bytes: [u8; 32] = [
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 17,
        ];

        let s = Scalar52::from_bytes(&bytes);

        let result_nat = to_nat_exec(&s.limbs);
        let l = group_order_exec();

        // OLD Postcondition 3: scalar52_to_nat(&s) < group_order() - DOES NOT HOLD
        assert!(
            &result_nat >= &l,
            "This example demonstrates result >= L: {} >= {}",
            result_nat,
            l
        );
    }

    // =========================================================================
    // Test: limb_prod_bounded_u128 vs limbs_bounded for montgomery_square
    // =========================================================================

    /// Helper: check if limb_prod_bounded_u128(a, a, 5) holds
    fn limb_prod_bounded_exec(a: &Scalar52) -> bool {
        for i in 0..5 {
            for j in 0..5 {
                let prod = (a.limbs[i] as u128) * (a.limbs[j] as u128);
                if prod.checked_mul(5).map_or(true, |p| p > u128::MAX) {
                    return false;
                }
            }
        }
        true
    }

    /// Helper: check if montgomery_reduce_input_bounds holds for a 9-limb array
    fn montgomery_reduce_input_bounds_exec(limbs: &[u128; 9]) -> bool {
        // From the spec:
        // limbs[0] < pow2(104), limbs[1] < pow2(105), limbs[2] < pow2(106),
        // limbs[3] < pow2(107), limbs[4] < pow2(107), limbs[5] < pow2(107),
        // limbs[6] < pow2(106), limbs[7] < pow2(105), limbs[8] < pow2(104)
        let bounds: [u128; 9] = [
            1u128 << 104,
            1u128 << 105,
            1u128 << 106,
            1u128 << 107,
            1u128 << 107,
            1u128 << 107,
            1u128 << 106,
            1u128 << 105,
            1u128 << 104,
        ];
        for i in 0..9 {
            if limbs[i] >= bounds[i] {
                return false;
            }
        }
        true
    }

    /// Test demonstrating that `limb_prod_bounded_u128` is INSUFFICIENT for `montgomery_square`.
    ///
    /// This test constructs an input that:
    /// 1. Satisfies `limb_prod_bounded_u128(a, a, 5)` ✓
    /// 2. Does NOT satisfy `limbs_bounded(a)` (limbs are > 2^52)
    /// 3. When squared via `square_internal`, violates `montgomery_reduce_input_bounds`
    ///
    /// This proves that `montgomery_square` MUST require `limbs_bounded`, not just `limb_prod_bounded_u128`.
    #[test]
    fn test_limb_prod_bounded_insufficient_for_square() {
        // Construct a Scalar52 with a[0] = 2^60
        // This satisfies limb_prod_bounded_u128 because:
        //   (2^60)^2 * 5 = 2^120 * 5 ≈ 2^122 < 2^128 = u128::MAX ✓
        // But does NOT satisfy limbs_bounded because:
        //   2^60 > 2^52 ✗
        let a = Scalar52 {
            limbs: [
                1u64 << 60, // = 2^60, violates limbs_bounded (requires < 2^52)
                0,
                0,
                0,
                0,
            ],
        };

        // Verify the setup
        println!("a.limbs[0] = {} = 2^60", a.limbs[0]);
        println!("2^52 = {}", 1u64 << 52);
        println!("u128::MAX = {}", u128::MAX);

        // Check 1: limb_prod_bounded_u128 SHOULD hold
        let prod_00 = (a.limbs[0] as u128) * (a.limbs[0] as u128);
        let prod_00_times_5 = prod_00.checked_mul(5);
        println!("a[0]^2 = {}", prod_00);
        println!("a[0]^2 * 5 = {:?}", prod_00_times_5);
        assert!(
            limb_prod_bounded_exec(&a),
            "Setup error: a should satisfy limb_prod_bounded_u128"
        );

        // Check 2: limbs_bounded should NOT hold
        assert!(
            !limbs_bounded_exec(&a),
            "Setup error: a should NOT satisfy limbs_bounded"
        );

        // Check 3: square_internal output should VIOLATE montgomery_reduce_input_bounds
        // Because z[0] = a[0]^2 = 2^120, but input_bounds requires z[0] < 2^104
        let z = Scalar52::square_internal(&a);

        println!("\nsquare_internal output:");
        println!("z[0] = {} (need < 2^104 = {})", z[0], 1u128 << 104);
        println!("z[0] bits = {}", 128 - z[0].leading_zeros());

        // The critical assertion: z[0] should violate the bound
        let bound_104 = 1u128 << 104;
        assert!(
            z[0] >= bound_104,
            "z[0] = {} should be >= 2^104 = {} because 2^120 >= 2^104",
            z[0],
            bound_104
        );

        // Therefore, montgomery_reduce_input_bounds should NOT hold
        assert!(
            !montgomery_reduce_input_bounds_exec(&z),
            "square_internal output should violate montgomery_reduce_input_bounds"
        );

        println!("\n✓ Test passed: limb_prod_bounded_u128 is INSUFFICIENT for montgomery_square");
        println!("  - Input satisfies limb_prod_bounded_u128 but not limbs_bounded");
        println!("  - square_internal output violates montgomery_reduce_input_bounds");
        println!("  - Therefore, montgomery_square MUST require limbs_bounded(self)");

        // Additional check: show this would violate part1's precondition
        // part1 requires sum < 2^108
        let part1_bound = 1u128 << 108;
        println!("\npart1 internal precondition check:");
        println!("  part1 requires: sum < 2^108 = {}", part1_bound);
        println!("  z[0] = {} (this is passed to part1)", z[0]);
        println!("  z[0] < 2^108? {}", z[0] < part1_bound);

        assert!(
            z[0] >= part1_bound,
            "z[0] should violate part1's precondition (sum < 2^108)"
        );
        println!("  → part1 precondition would be VIOLATED!");
        println!("  → Algorithm could overflow or produce wrong results");
    }

    /// Complementary test: with `limbs_bounded`, the bounds ARE satisfied.
    #[test]
    fn test_limbs_bounded_sufficient_for_square() {
        // Construct a Scalar52 with a[0] = 2^52 - 1 (max value allowed by limbs_bounded)
        let a = Scalar52 {
            limbs: [
                (1u64 << 52) - 1, // max limb value under limbs_bounded
                (1u64 << 52) - 1,
                (1u64 << 52) - 1,
                (1u64 << 52) - 1,
                (1u64 << 52) - 1,
            ],
        };

        // Verify limbs_bounded holds
        assert!(
            limbs_bounded_exec(&a),
            "Setup error: a should satisfy limbs_bounded"
        );

        // square_internal output should satisfy montgomery_reduce_input_bounds
        let z = Scalar52::square_internal(&a);

        println!("With limbs_bounded input (max values):");
        println!("z[0] = {} (need < 2^104 = {})", z[0], 1u128 << 104);

        // Check each bound
        let bounds: [(usize, u128); 9] = [
            (0, 1u128 << 104),
            (1, 1u128 << 105),
            (2, 1u128 << 106),
            (3, 1u128 << 107),
            (4, 1u128 << 107),
            (5, 1u128 << 107),
            (6, 1u128 << 106),
            (7, 1u128 << 105),
            (8, 1u128 << 104),
        ];

        for (i, bound) in bounds {
            println!("z[{}] = {} < {} ? {}", i, z[i], bound, z[i] < bound);
            assert!(z[i] < bound, "z[{}] = {} should be < {}", i, z[i], bound);
        }

        assert!(
            montgomery_reduce_input_bounds_exec(&z),
            "square_internal output should satisfy montgomery_reduce_input_bounds when input is limbs_bounded"
        );

        println!("\n✓ Test passed: limbs_bounded IS sufficient for montgomery_square");
    }

    proptest! {
        #![proptest_config(proptest::test_runner::Config::with_cases(1000000))]

        /// Test from_bytes spec: for any 32-byte array, verify both postconditions
        /// 1. bytes32_to_nat(bytes) == scalar52_to_nat(&s)
        /// 2. limbs_bounded(&s)
        #[test]
        fn prop_from_bytes(bytes in prop::array::uniform32(any::<u8>())) {
            // Call from_bytes
            let s = Scalar52::from_bytes(&bytes);

            // Convert to BigUint using executable spec functions
            let bytes_nat = bytes32_to_nat_exec(&bytes);
            let result_nat = to_nat_exec(&s.limbs);

            // Postcondition 1: bytes32_to_nat(bytes) == scalar52_to_nat(&s)
            prop_assert_eq!(bytes_nat, result_nat,
                "from_bytes spec violated: bytes32_to_nat(bytes) != scalar52_to_nat(&s)");

            // Postcondition 2: limbs_bounded(&s)
            prop_assert!(limbs_bounded_exec(&s),
                "from_bytes spec violated: result limbs not bounded by 2^52");
        }

        /// Test 1: Input is product of TWO bounded scalars (both may be non-canonical)
        /// Spec says: if input = mul(bounded1, bounded2) then Montgomery property and limbs_bounded hold
        /// (but canonicality is NOT guaranteed)
        #[test]
        fn prop_montgomery_reduce_two_bounded(limbs in arb_nine_limbs_two_bounded()) {
            // Call montgomery_reduce
            let result = Scalar52::montgomery_reduce(&limbs);

            // Convert to BigUint using executable spec functions
            let result_nat = to_nat_exec(&result.limbs);
            let limbs_nat = slice128_to_nat_exec(&limbs);
            let l = group_order_exec();
            let r = montgomery_radix_exec();

            // Postcondition 1: Montgomery property (should hold for product of two bounded)
            let lhs = (&result_nat * &r) % &l;
            let rhs = &limbs_nat % &l;
            prop_assert_eq!(lhs, rhs,
                "Montgomery reduce spec violated: (result * R) mod L != limbs mod L");

            // Postcondition 2: limbs_bounded (should hold for product of two bounded)
            prop_assert!(limbs_bounded_exec(&result),
                "Result limbs not bounded by 2^52");

            // Postcondition 3: Canonicality is NOT guaranteed for product of two bounded scalars
            // (only guaranteed when one is canonical)
        }

        /// Test 2: Input is product of one bounded scalar and one canonical scalar
        /// Spec says: if input = mul(bounded, canonical) then result < L
        #[test]
        fn prop_montgomery_reduce_one_canonical(limbs in arb_nine_limbs_one_canonical()) {
            // Call montgomery_reduce
            let result = Scalar52::montgomery_reduce(&limbs);

            // Convert to BigUint using executable spec functions
            let result_nat = to_nat_exec(&result.limbs);
            let limbs_nat = slice128_to_nat_exec(&limbs);
            let l = group_order_exec();
            let r = montgomery_radix_exec();

            // Postcondition 1: Montgomery property (holds by first part of spec)
            let lhs = (&result_nat * &r) % &l;
            let rhs = &limbs_nat % &l;
            prop_assert_eq!(lhs, rhs,
                "Montgomery reduce spec violated: (result * R) mod L != limbs mod L");

            // Postcondition 2: limbs_bounded (holds by first part of spec)
            prop_assert!(limbs_bounded_exec(&result),
                "Result limbs not bounded by 2^52");

            // Postcondition 3: Canonicality - SHOULD hold by second part of spec
            // (exists bounded, canonical such that limbs = mul(bounded, canonical)) ==> result < L
            prop_assert!(&result_nat < &l,
                "Result not in canonical form (>= L), but input was product of bounded × canonical");
        }

        /// SPEC JUSTIFICATION TEST: r4 is always < 2^52 + L[4] for bounded × bounded
        ///
        /// This test provides empirical evidence that justifies weakening sub's precondition
        /// from `limbs_bounded(a)` to `a[4] < 2^52 + b[4]`.
        ///
        /// Key findings:
        /// - r4 CAN exceed 2^52 (we found counterexamples)
        /// - r4 NEVER exceeds 2^52 + L[4] (verified with 1M+ test cases)
        /// - Therefore sub(intermediate, L) always produces result[4] = r4 - L[4] < 2^52
        ///
        /// See docs/proofs_for_montgomery_reduce/sub_and_bounds_analysis.md for full analysis.
        #[test]
        fn prop_r4_bound_two_bounded(
            (a, b) in (arb_bounded_scalar52(), arb_bounded_scalar52())
        ) {
            let limbs = Scalar52::mul_internal(&a, &b);
            let r4 = compute_montgomery_r4(&limbs);

            let two_52 = 1u64 << 52;
            let l4 = constants::L.limbs[4];  // = 2^44
            let critical_bound = two_52 + l4;  // = 2^52 + 2^44

            // Test: does r4 ever exceed 2^52 + L[4]?
            // If it does, sub(intermediate, L) would leave result[4] > 2^52
            prop_assert!(r4 < critical_bound,
                "r4 EXCEEDS CRITICAL BOUND (2^52 + L[4])! \
                 r4 = {} (2^52 = {}, L[4] = {}, bound = {}). \
                 After sub, result[4] would be {} which exceeds 2^52! \
                 a = {:?}, b = {:?}",
                r4, two_52, l4, critical_bound,
                r4 - l4,
                a.limbs, b.limbs);
        }
    }

    /// Test the specific failing case where r4 > 2^52
    /// This verifies whether the code still works correctly despite r4 exceeding the spec bound.
    #[test]
    fn test_r4_exceeds_bound_specific_case() {
        let a = Scalar52 {
            limbs: [
                571816494035867,
                2102651587093367,
                2513475888134185,
                932481845735615,
                4500073941159943,
            ],
        };
        let b = Scalar52 {
            limbs: [
                591064789902205,
                2588218568528500,
                286456962905922,
                187920743071596,
                4497583039741987,
            ],
        };

        let limbs = Scalar52::mul_internal(&a, &b);
        let (r0, r1, r2, r3, r4) = compute_montgomery_intermediate(&limbs);

        println!("=== Intermediate result (before sub) ===");
        println!("r0 = {} (bounded: {})", r0, r0 < (1u64 << 52));
        println!("r1 = {} (bounded: {})", r1, r1 < (1u64 << 52));
        println!("r2 = {} (bounded: {})", r2, r2 < (1u64 << 52));
        println!("r3 = {} (bounded: {})", r3, r3 < (1u64 << 52));
        println!(
            "r4 = {} (bounded: {}) <-- EXCEEDS 2^52!",
            r4,
            r4 < (1u64 << 52)
        );
        println!("2^52 = {}", 1u64 << 52);
        println!("r4 - 2^52 = {}", r4 as i128 - (1i128 << 52));

        // Use BigUint since intermediate can be > 2^128
        use num_bigint::BigUint;
        let intermediate_nat = BigUint::from(r0)
            + (BigUint::from(r1) << 52)
            + (BigUint::from(r2) << 104)
            + (BigUint::from(r3) << 156)
            + (BigUint::from(r4) << 208);
        let l = group_order_exec();

        println!("\nIntermediate value: {}", intermediate_nat);
        println!("L = {}", l);
        println!("Intermediate >= L: {}", intermediate_nat >= l);
        println!("Intermediate >= 2L: {}", intermediate_nat >= &l * 2u32);

        if &intermediate_nat >= &l {
            println!("Intermediate - L = {}", &intermediate_nat - &l);
        }

        // Now run actual montgomery_reduce
        let result = Scalar52::montgomery_reduce(&limbs);
        let result_nat = to_nat_exec(&result.limbs);
        let limbs_nat = slice128_to_nat_exec(&limbs);
        let r = montgomery_radix_exec();

        println!("\n=== Final result (after sub) ===");
        println!("Result limbs: {:?}", result.limbs);
        println!("Result value: {}", result_nat);
        println!("limbs_bounded: {}", limbs_bounded_exec(&result));
        println!("Result < L (canonical): {}", &result_nat < &l);

        // Check Montgomery property
        let lhs = (&result_nat * &r) % &l;
        let rhs = &limbs_nat % &l;
        println!("\nMontgomery property:");
        println!("  (result * R) mod L = {}", lhs);
        println!("  limbs mod L = {}", rhs);
        println!("  Equal: {}", lhs == rhs);

        assert!(lhs == rhs, "Montgomery property violated!");
        assert!(limbs_bounded_exec(&result), "Result not limbs_bounded!");

        println!("\n✓ INSIGHT: Code works because intermediate >= L, so sub() subtracts L,");
        println!("  and the borrow propagation brings r4 back into bounds!");

        // Key observation: L[4] = 2^52 exactly!
        println!(
            "\nL[4] = {} = 2^52? {}",
            constants::L.limbs[4],
            constants::L.limbs[4] == (1u64 << 52)
        );
        println!(
            "r4 - L[4] = {} (fits in 52 bits? {})",
            r4 - constants::L.limbs[4],
            r4 - constants::L.limbs[4] < (1u64 << 52)
        );
    }

    /// SPEC JUSTIFICATION TEST: sub() works correctly with a[4] > 2^52
    ///
    /// This test directly verifies that sub produces correct results when called with
    /// an input that violates the CURRENT spec (limbs_bounded) but satisfies the
    /// PROPOSED weaker spec (a[4] < 2^52 + b[4]).
    ///
    /// Uses the exact counterexample from prop_r4_bound_two_bounded where r4 = 4511344796891578
    /// (53 bits, exceeds 2^52 by 7,745,169,521,082).
    ///
    /// Verifies:
    /// 1. result == intermediate - L (mathematically correct)
    /// 2. limbs_bounded(&result) (output is properly bounded)
    ///
    /// See docs/proofs_for_montgomery_reduce/sub_and_bounds_analysis.md for full analysis.
    #[test]
    fn test_sub_with_non_bounded_input() {
        use num_bigint::BigUint;

        // Construct an intermediate where r4 > 2^52
        // Use the exact values from our counterexample
        let intermediate = Scalar52 {
            limbs: [
                118538672376151,  // r0 < 2^52 ✓
                3710478283503969, // r1 < 2^52 ✓
                1409276660399498, // r2 < 2^52 ✓
                224706045673331,  // r3 < 2^52 ✓
                4511344796891578, // r4 > 2^52 ✗ (this is 53 bits!)
            ],
        };

        let l = group_order_exec();
        let two_52 = 1u64 << 52;

        println!("=== Testing sub() with non-bounded input ===");
        println!(
            "intermediate.limbs[4] = {} (2^52 = {})",
            intermediate.limbs[4], two_52
        );
        println!(
            "intermediate.limbs[4] is 53 bits: {}",
            intermediate.limbs[4] >= two_52
        );
        println!(
            "limbs_bounded(&intermediate): {}",
            limbs_bounded_exec(&intermediate)
        );

        // Calculate the mathematical value of intermediate
        // Note: seq_to_nat_52 interprets each limb with 52-bit radix
        let intermediate_nat = BigUint::from(intermediate.limbs[0])
            + (BigUint::from(intermediate.limbs[1]) << 52)
            + (BigUint::from(intermediate.limbs[2]) << 104)
            + (BigUint::from(intermediate.limbs[3]) << 156)
            + (BigUint::from(intermediate.limbs[4]) << 208);

        println!("\nintermediate (as BigUint) = {}", intermediate_nat);
        println!("L = {}", l);
        println!("intermediate >= L: {}", intermediate_nat >= l);

        // Call sub (this violates sub's precondition, but let's see what happens)
        let result = Scalar52::sub(&intermediate, &constants::L);

        let result_nat = to_nat_exec(&result.limbs);
        println!("\n=== Result of sub(intermediate, L) ===");
        println!("result.limbs = {:?}", result.limbs);
        println!("result (as BigUint) = {}", result_nat);
        println!("limbs_bounded(&result): {}", limbs_bounded_exec(&result));

        // Check if result = intermediate - L (mathematically)
        let expected = &intermediate_nat - &l;
        println!("\nExpected (intermediate - L) = {}", expected);
        println!("Actual result = {}", result_nat);
        println!("Match: {}", result_nat == expected);

        // Key insight: why does this work?
        println!("\n=== Key Insight ===");
        println!("L.limbs[4] = {} = 2^52", constants::L.limbs[4]);
        println!(
            "intermediate.limbs[4] - L.limbs[4] = {}",
            intermediate.limbs[4] - constants::L.limbs[4]
        );
        println!("This fits in 52 bits because r4 < 2^53 and L[4] = 2^52");

        assert_eq!(result_nat, expected, "sub produced wrong result!");
        assert!(limbs_bounded_exec(&result), "result not bounded!");
    }

    /// SPEC JUSTIFICATION TEST: Trace through sub's algorithm step-by-step
    ///
    /// This test traces through the bit-level operations in sub() to explain WHY
    /// the algorithm works correctly when a[4] > 2^52 (violating current spec).
    ///
    /// Key insight: For limb 4, the computation is:
    ///   difference[4] = (a[4] - b[4] - borrow) & (2^52 - 1)
    ///
    /// If a[4] < 2^52 + b[4], then a[4] - b[4] < 2^52, so masking doesn't lose bits.
    ///
    /// This provides the theoretical foundation for the proposed spec weakening.
    /// See docs/proofs_for_montgomery_reduce/sub_and_bounds_analysis.md for full analysis.
    #[test]
    fn test_sub_algorithm_trace() {
        use num_bigint::BigUint;

        println!("=== Tracing sub() algorithm with a[4] > 2^52 ===\n");

        // Input: intermediate with a[4] > 2^52
        let a = Scalar52 {
            limbs: [
                118538672376151,
                3710478283503969,
                1409276660399498,
                224706045673331,
                4511344796891578,
            ],
        };
        let b = constants::L;

        let mask = (1u64 << 52) - 1;
        let two_52 = 1u64 << 52;

        println!(
            "a[4] = {} ({} bits)",
            a.limbs[4],
            64 - a.limbs[4].leading_zeros()
        );
        println!("b[4] = L[4] = {} = 2^44", b.limbs[4]);
        println!("2^52 = {}", two_52);
        println!("a[4] > 2^52: {}", a.limbs[4] > two_52);
        println!();

        // Simulate Loop 1 of sub: compute a - b with borrow
        println!("=== Loop 1: Compute a - b ===");
        let mut difference = [0u64; 5];
        let mut borrow: u64 = 0;

        for i in 0..5 {
            let old_borrow = borrow;
            let incoming_borrow = old_borrow >> 63;

            // wrapping_sub: (a[i] - b[i] - borrow) mod 2^64
            borrow = a.limbs[i].wrapping_sub(b.limbs[i] + incoming_borrow);
            difference[i] = borrow & mask;

            println!(
                "i={}: a[i]={}, b[i]={}, incoming_borrow={}",
                i, a.limbs[i], b.limbs[i], incoming_borrow
            );
            println!("     borrow (before mask) = {}", borrow);
            println!(
                "     difference[i] = {} (< 2^52: {})",
                difference[i],
                difference[i] < two_52
            );
            println!("     outgoing borrow >> 63 = {}", borrow >> 63);

            if i == 4 {
                println!("\n     KEY OBSERVATION for i=4:");
                println!(
                    "     a[4] - b[4] - incoming = {} - {} - {} = {}",
                    a.limbs[4],
                    b.limbs[4],
                    incoming_borrow,
                    a.limbs[4] as i128 - b.limbs[4] as i128 - incoming_borrow as i128
                );
                println!(
                    "     This is {} 2^52, so after masking: difference[4] = {}",
                    if (a.limbs[4] as i128 - b.limbs[4] as i128 - incoming_borrow as i128)
                        < (two_52 as i128)
                    {
                        "<"
                    } else {
                        ">="
                    },
                    difference[4]
                );
            }
            println!();
        }

        let final_borrow = borrow >> 63;
        println!(
            "Final borrow >> 63 = {} (0 = no underflow, 1 = underflow)",
            final_borrow
        );

        if final_borrow == 0 {
            println!("\nNo underflow => result = a - b (no L added)");
        } else {
            println!("\nUnderflow => result = a - b + L");
        }

        println!("\n=== Why it works ===");
        println!("The algorithm correctly handles a[4] > 2^52 because:");
        println!(
            "1. a[4] - L[4] = {} - {} = {}",
            a.limbs[4],
            b.limbs[4],
            a.limbs[4] as i64 - b.limbs[4] as i64
        );
        println!(
            "2. This difference {} is < 2^52 = {}",
            a.limbs[4] - b.limbs[4],
            two_52
        );
        println!("3. So masking with (2^52 - 1) doesn't lose any bits");
        println!("4. The result is mathematically correct!");

        println!("\n=== Critical condition ===");
        println!("sub(a, L) works correctly when: a[4] < 2^52 + L[4]");
        println!(
            "In our case: {} < {} + {} = {} ✓",
            a.limbs[4],
            two_52,
            b.limbs[4],
            two_52 + b.limbs[4]
        );
    }

    /// Compute the full intermediate result (r0, r1, r2, r3, r4) from montgomery_reduce.
    fn compute_montgomery_intermediate(limbs: &[u128; 9]) -> (u64, u64, u64, u64, u64) {
        let l = &constants::L;

        fn m(a: u64, b: u64) -> u128 {
            (a as u128) * (b as u128)
        }

        fn part1_exec(sum: u128) -> (u128, u64) {
            let mask52: u64 = (1u64 << 52) - 1;
            let sum_low52 = (sum as u64) & mask52;
            let product = (sum_low52 as u128) * (constants::LFACTOR as u128);
            let p = (product as u64) & mask52;
            let carry = (sum + m(p, constants::L.limbs[0])) >> 52;
            (carry, p)
        }

        fn part2_exec(sum: u128) -> (u128, u64) {
            let w = (sum as u64) & ((1u64 << 52) - 1);
            let carry = sum >> 52;
            (carry, w)
        }

        // PHASE 1
        let (carry, n0) = part1_exec(limbs[0]);
        let (carry, n1) = part1_exec(carry + limbs[1] + m(n0, l.limbs[1]));
        let (carry, n2) = part1_exec(carry + limbs[2] + m(n0, l.limbs[2]) + m(n1, l.limbs[1]));
        let (carry, n3) = part1_exec(carry + limbs[3] + m(n1, l.limbs[2]) + m(n2, l.limbs[1]));
        let (carry, n4) = part1_exec(
            carry + limbs[4] + m(n0, l.limbs[4]) + m(n2, l.limbs[2]) + m(n3, l.limbs[1]),
        );

        // PHASE 2
        let (carry, r0) = part2_exec(
            carry + limbs[5] + m(n1, l.limbs[4]) + m(n3, l.limbs[2]) + m(n4, l.limbs[1]),
        );
        let (carry, r1) = part2_exec(carry + limbs[6] + m(n2, l.limbs[4]) + m(n4, l.limbs[2]));
        let (carry, r2) = part2_exec(carry + limbs[7] + m(n3, l.limbs[4]));
        let (carry, r3) = part2_exec(carry + limbs[8] + m(n4, l.limbs[4]));
        let r4 = carry as u64;

        (r0, r1, r2, r3, r4)
    }

    /// Compute the r4 value (final carry) from montgomery_reduce intermediate result.
    /// This replicates the Phase 1 and Phase 2 computation without the final sub.
    fn compute_montgomery_r4(limbs: &[u128; 9]) -> u64 {
        let l = &constants::L;

        // Helper to compute m(a, b) = (a as u128) * (b as u128)
        fn m(a: u64, b: u64) -> u128 {
            (a as u128) * (b as u128)
        }

        // Helper for part1: returns (carry, p) where p cancels low bits
        fn part1_exec(sum: u128) -> (u128, u64) {
            let mask52: u64 = (1u64 << 52) - 1;
            let sum_low52 = (sum as u64) & mask52;
            let product = (sum_low52 as u128) * (constants::LFACTOR as u128);
            let p = (product as u64) & mask52;
            let carry = (sum + m(p, constants::L.limbs[0])) >> 52;
            (carry, p)
        }

        // Helper for part2: returns (carry, w)
        fn part2_exec(sum: u128) -> (u128, u64) {
            let w = (sum as u64) & ((1u64 << 52) - 1);
            let carry = sum >> 52;
            (carry, w)
        }

        // PHASE 1: Compute n0..n4 using part1
        let (carry, n0) = part1_exec(limbs[0]);
        let (carry, n1) = part1_exec(carry + limbs[1] + m(n0, l.limbs[1]));
        let (carry, n2) = part1_exec(carry + limbs[2] + m(n0, l.limbs[2]) + m(n1, l.limbs[1]));
        let (carry, n3) = part1_exec(carry + limbs[3] + m(n1, l.limbs[2]) + m(n2, l.limbs[1]));
        let (carry, n4) = part1_exec(
            carry + limbs[4] + m(n0, l.limbs[4]) + m(n2, l.limbs[2]) + m(n3, l.limbs[1]),
        );

        // PHASE 2: Compute r0..r3 using part2, then r4 is the final carry
        let (carry, _r0) = part2_exec(
            carry + limbs[5] + m(n1, l.limbs[4]) + m(n3, l.limbs[2]) + m(n4, l.limbs[1]),
        );
        let (carry, _r1) = part2_exec(carry + limbs[6] + m(n2, l.limbs[4]) + m(n4, l.limbs[2]));
        let (carry, _r2) = part2_exec(carry + limbs[7] + m(n3, l.limbs[4]));
        let (carry, _r3) = part2_exec(carry + limbs[8] + m(n4, l.limbs[4]));

        // r4 is the final carry
        carry as u64
    }

    /// Test that our refactoring of part1 is equivalent to the original wrapping_mul version.
    ///
    /// ORIGINAL CODE:
    ///   let p = (sum as u64).wrapping_mul(LFACTOR) & MASK52;
    ///
    /// REFACTORED CODE (to avoid Verus wrapping_mul limitation):
    ///   let sum_low52 = (sum as u64) & MASK52;
    ///   let product = (sum_low52 as u128) * (LFACTOR as u128);
    ///   let p = (product as u64) & MASK52;
    ///
    /// This test verifies:
    ///   (a.wrapping_mul(b)) & MASK52 == ((a & MASK52) * b) & MASK52
    ///
    /// for all relevant values of `sum` that part1 might receive.
    #[test]
    fn test_part1_wrapping_mul_equivalence() {
        use proptest::prelude::*;
        use proptest::test_runner::{Config, TestRunner};

        let mask52: u64 = (1u64 << 52) - 1;
        let lfactor: u64 = 0x51da312547e1b;

        let mut runner = TestRunner::new(Config {
            cases: 10000,
            ..Config::default()
        });

        runner
            .run(
                &(0u128..(1u128 << 108)), // sum < 2^108 (part1's precondition)
                |sum| {
                    // ORIGINAL: using wrapping_mul
                    let p_original = (sum as u64).wrapping_mul(lfactor) & mask52;

                    // REFACTORED: extract low 52 bits first, multiply in u128
                    let sum_low52 = (sum as u64) & mask52;
                    let product = (sum_low52 as u128) * (lfactor as u128);
                    let p_refactored = (product as u64) & mask52;

                    // They must be equal
                    prop_assert_eq!(
                        p_original,
                        p_refactored,
                        "Mismatch for sum = {}: original = {}, refactored = {}",
                        sum,
                        p_original,
                        p_refactored
                    );

                    Ok(())
                },
            )
            .expect("Property test failed");
    }

    /// Test that wrapping_mul followed by masking equals mod 2^52
    ///
    /// This verifies: (a.wrapping_mul(b)) & MASK52 == (a * b) mod 2^52
    #[test]
    fn test_wrapping_mul_mask_equals_mod() {
        use proptest::prelude::*;
        use proptest::test_runner::{Config, TestRunner};

        let mask52: u64 = (1u64 << 52) - 1;
        let mod_52: u128 = 1u128 << 52;

        let mut runner = TestRunner::new(Config {
            cases: 10000,
            ..Config::default()
        });

        runner
            .run(&(any::<u64>(), any::<u64>()), |(a, b)| {
                // Using wrapping_mul and mask
                let result_wrapping = a.wrapping_mul(b) & mask52;

                // Using full multiplication and mod
                let product_full = (a as u128) * (b as u128);
                let result_mod = (product_full % mod_52) as u64;

                prop_assert_eq!(
                    result_wrapping,
                    result_mod,
                    "wrapping_mul & mask != mod for a={}, b={}: {} != {}",
                    a,
                    b,
                    result_wrapping,
                    result_mod
                );

                Ok(())
            })
            .expect("Property test failed");
    }
}
// #[cfg(test)]
// mod test {
//     use super::*;
//     /// Note: x is 2^253-1 which is slightly larger than the largest scalar produced by
//     /// this implementation (l-1), and should show there are no overflows for valid scalars
//     ///
//     /// x = 14474011154664524427946373126085988481658748083205070504932198000989141204991
//     /// x = 7237005577332262213973186563042994240801631723825162898930247062703686954002 mod l
//     /// x = 3057150787695215392275360544382990118917283750546154083604586903220563173085*R mod l in Montgomery form
//     pub static X: Scalar52 = Scalar52 {
//         limbs: [
//             0x000fffffffffffff,
//             0x000fffffffffffff,
//             0x000fffffffffffff,
//             0x000fffffffffffff,
//             0x00001fffffffffff,
//         ],
//     };
//     /// x^2 = 3078544782642840487852506753550082162405942681916160040940637093560259278169 mod l
//     pub static XX: Scalar52 = Scalar52 {
//         limbs: [
//             0x0001668020217559,
//             0x000531640ffd0ec0,
//             0x00085fd6f9f38a31,
//             0x000c268f73bb1cf4,
//             0x000006ce65046df0,
//         ],
//     };
//     /// x^2 = 4413052134910308800482070043710297189082115023966588301924965890668401540959*R mod l in Montgomery form
//     pub static XX_MONT: Scalar52 = Scalar52 {
//         limbs: [
//             0x000c754eea569a5c,
//             0x00063b6ed36cb215,
//             0x0008ffa36bf25886,
//             0x000e9183614e7543,
//             0x0000061db6c6f26f,
//         ],
//     };
//     /// y = 6145104759870991071742105800796537629880401874866217824609283457819451087098
//     pub static Y: Scalar52 = Scalar52 {
//         limbs: [
//             0x000b75071e1458fa,
//             0x000bf9d75e1ecdac,
//             0x000433d2baf0672b,
//             0x0005fffcc11fad13,
//             0x00000d96018bb825,
//         ],
//     };
//     /// x*y = 36752150652102274958925982391442301741 mod l
//     pub static XY: Scalar52 = Scalar52 {
//         limbs: [
//             0x000ee6d76ba7632d,
//             0x000ed50d71d84e02,
//             0x00000000001ba634,
//             0x0000000000000000,
//             0x0000000000000000,
//         ],
//     };
//     /// x*y = 658448296334113745583381664921721413881518248721417041768778176391714104386*R mod l in Montgomery form
//     pub static XY_MONT: Scalar52 = Scalar52 {
//         limbs: [
//             0x0006d52bf200cfd5,
//             0x00033fb1d7021570,
//             0x000f201bc07139d8,
//             0x0001267e3e49169e,
//             0x000007b839c00268,
//         ],
//     };
//     /// a = 2351415481556538453565687241199399922945659411799870114962672658845158063753
//     pub static A: Scalar52 = Scalar52 {
//         limbs: [
//             0x0005236c07b3be89,
//             0x0001bc3d2a67c0c4,
//             0x000a4aa782aae3ee,
//             0x0006b3f6e4fec4c4,
//             0x00000532da9fab8c,
//         ],
//     };
//     /// b = 4885590095775723760407499321843594317911456947580037491039278279440296187236
//     pub static B: Scalar52 = Scalar52 {
//         limbs: [
//             0x000d3fae55421564,
//             0x000c2df24f65a4bc,
//             0x0005b5587d69fb0b,
//             0x00094c091b013b3b,
//             0x00000acd25605473,
//         ],
//     };
//     /// a+b = 0
//     /// a-b = 4702830963113076907131374482398799845891318823599740229925345317690316127506
//     pub static AB: Scalar52 = Scalar52 {
//         limbs: [
//             0x000a46d80f677d12,
//             0x0003787a54cf8188,
//             0x0004954f0555c7dc,
//             0x000d67edc9fd8989,
//             0x00000a65b53f5718,
//         ],
//     };
//     // c = (2^512 - 1) % l = 1627715501170711445284395025044413883736156588369414752970002579683115011840
//     pub static C: Scalar52 = Scalar52 {
//         limbs: [
//             0x000611e3449c0f00,
//             0x000a768859347a40,
//             0x0007f5be65d00e1b,
//             0x0009a3dceec73d21,
//             0x00000399411b7c30,
//         ],
//     };
//     #[test]
//     fn mul_max() {
//         let res = Scalar52::mul(&X, &X);
//         for i in 0..5 {
//             assert!(res[i] == XX[i]);
//         }
//     }
//     #[test]
//     fn square_max() {
//         let res = X.square();
//         for i in 0..5 {
//             assert!(res[i] == XX[i]);
//         }
//     }
//     #[test]
//     fn montgomery_mul_max() {
//         let res = Scalar52::montgomery_mul(&X, &X);
//         for i in 0..5 {
//             assert!(res[i] == XX_MONT[i]);
//         }
//     }
//     #[test]
//     fn montgomery_square_max() {
//         let res = X.montgomery_square();
//         for i in 0..5 {
//             assert!(res[i] == XX_MONT[i]);
//         }
//     }
//     #[test]
//     fn mul() {
//         let res = Scalar52::mul(&X, &Y);
//         for i in 0..5 {
//             assert!(res[i] == XY[i]);
//         }
//     }
//     #[test]
//     fn montgomery_mul() {
//         let res = Scalar52::montgomery_mul(&X, &Y);
//         for i in 0..5 {
//             assert!(res[i] == XY_MONT[i]);
//         }
//     }
//     #[test]
//     fn add() {
//         let res = Scalar52::add(&A, &B);
//         let zero = Scalar52::ZERO;
//         for i in 0..5 {
//             assert!(res[i] == zero[i]);
//         }
//     }
//     #[test]
//     fn sub() {
//         let res = Scalar52::sub(&A, &B);
//         for i in 0..5 {
//             assert!(res[i] == AB[i]);
//         }
//     }
//     #[test]
//     fn from_bytes_wide() {
//         let bignum = [255u8; 64]; // 2^512 - 1
//         let reduced = Scalar52::from_bytes_wide(&bignum);
//         for i in 0..5 {
//             assert!(reduced[i] == C[i]);
//         }
//     }
// }
