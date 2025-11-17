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
use super::subtle_assumes::select;
use core::fmt::Debug;
use core::ops::{Index, IndexMut};
use subtle::Choice;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

use crate::constants;

#[allow(unused_imports)]
use crate::lemmas::common_lemmas::bit_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::pow_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::core_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::scalar_byte_lemmas::scalar_to_bytes_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::lemmas::scalar_montgomery_lemmas::lemma_from_montgomery_is_product_with_one;
#[allow(unused_imports)]
use crate::specs::scalar_specs_u64::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
#[allow(unused_imports)]
use vstd::calc;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::bits::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power::*;


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

#[cfg(feature = "zeroize")]
impl Zeroize for Scalar52 {
    fn zeroize(&mut self) {
        self.limbs.zeroize();
    }
}

verus! {

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
    requires
        x < (1u64 << 52),
        y < (1u64 << 52),
    ensures
        z < (1u128 << 104),
        z == x * y,
{
    proof {
        lemma_52_52(x, y);
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
            bytes_to_nat(bytes) == to_nat(&s.limbs),
            limbs_bounded(&s),
            to_nat(&s.limbs) < group_order(),
    {
        let mut words = [0u64;4];
        proof {
            assert(forall |i2: int| 0 <= i2 < 4 ==> words[i2] == 0u64);
        }
        for i in 0..4
            invariant
                0 <= i <= 4,
                forall |i2: int| i <= i2 < 4 ==> words[i2] == 0u64,
                forall |i2: int| 0 <= i2 < i ==> ((words[i2] as nat)
                                                            == bytes_seq_to_nat_clear(
                                                                Seq::new(8, |j: int| bytes[i2*8 + j]), 8)
                                                 )
        {
            proof{
                assert(words[i as int] == 0);
                lemma_pow2_pos(0 as nat)
            }

            for j in 0..8
                invariant
                    0 <= j <= 8 && 0 <= i < 4,
                    words[i as int] < pow2(j as nat * 8),
                    forall |i2: int| i + 1 <= i2 < 4 ==> words[i2] == 0u64,
                    words[i as int] == bytes_seq_to_nat_clear(Seq::new(8, |j2: int| bytes[i as int * 8 + j2]), j as nat),
                    forall |i2: int| 0 <= i2 < i ==> ((words[i2] as nat)
                                                            == bytes_seq_to_nat_clear(
                                                                Seq::new(8, |j: int| bytes[i2*8 + j]), 8)
                                                     )
            {
                proof {
                    assert(i < 4 && j < 8);
                    assert((i as u64) * 8u64 < 32u64);
                    let idx = (i as u64) * 8 + (j as u64);
                    assert(idx < 32);

                    let old_word = words[i as int];
                    let new_byte = bytes[idx] as u64;
                    
                    assert(j < 8);
                    lemma_mul_strict_inequality(j as int, 8, 8);
                    assert((j as int * 8)  < 64);
                    lemma_pow2_strictly_increases(j as nat* 8, 64);
                    
                    assert(1 * pow2(j as nat * 8) == pow2(j as nat * 8));
                    assert(1 * pow2(j as nat * 8) < pow2(64));
                    lemma_u64_pow2_no_overflow(j as nat * 8);
                    
                    let j8 = (j * 8) as u64;
                    
                    assert(old_word < (1u64 << j8)) by {
                        assert(old_word < pow2(j8 as nat));
                        assert(j8 < u64::BITS);
                        assert(1 * pow2(j8 as nat) <= u64::MAX);
                        lemma_u64_shl_is_mul(1, j8);
                        assert((1u64 << j8) == 1 * pow2(j8 as nat));
                    };

                    assert(new_byte <= (u64::MAX >> j8)) by {
                        assert(new_byte <= 255) by (compute);
                        assert((u64::MAX >> (j * 8)) ==  (u64::MAX / (pow2(j8 as nat) as u64))) by {
                            lemma_u64_shr_is_div(u64::MAX, j8);
                        }
                        assert(u64::MAX / (pow2(56) as u64) <= u64::MAX / (pow2(j8 as nat) as u64)) by {
                            assert(j8 <= 56);
                            assert(pow2(j8 as nat) <= pow2(56)) by {
                                lemma_pow_increases(2, j8 as nat, 56);
                                lemma_pow2(j8 as nat);
                                lemma_pow2(56);
                            }
                            lemma_div_is_ordered_by_denominator(u64::MAX as int, pow2(j8 as nat) as int, pow2(56) as int);
                            assert(((u64::MAX as int) / (pow2(56) as int)) <= ((u64::MAX as int) / (pow2(j8 as nat) as int)));
                            lemma_u64_pow2_no_overflow(56);
                        }
                        assert(255 <= u64::MAX / (pow2(56) as u64)) by {
                            lemma_pow2(56);
                            lemma_u64_pow2_no_overflow(56);
                            reveal(pow);
                            assert(255 <= u64::MAX / (pow(2, 56) as u64)) by (compute);
                        }
                    }

                    assert((old_word | (new_byte << (j8))) ==
                           (old_word + (new_byte << (j8)))) by {
                        lemma_bit_or_is_plus(old_word, new_byte, j8 as u64);
                    }
                    
                    let j8next = (j as u64 + 1) * 8 as u64;
                    
                    
                    assert(old_word + (new_byte << j8) == old_word + new_byte * pow2(j8 as nat)) by {
                        assert(new_byte <= 255);
                        assert(pow2(j8 as nat) <= pow2(56)) by {
                            lemma_pow_increases(2, j8 as nat, 56);
                            lemma_pow2(j8 as nat);
                            lemma_pow2(56);
                        }
                        assert(new_byte * pow2(j8 as nat) <= new_byte * pow2(56)) by {
                            if(0 < new_byte) {
                                lemma_mul_left_inequality(new_byte as int, pow2(j8 as nat) as int, pow2(56) as int);
                            } else {
                                assert(0 == new_byte);
                                assert(new_byte * pow2(j8 as nat) == 0) by {
                                    lemma_mul_by_zero_is_zero(pow2(j8 as nat) as int);
                                };
                                assert(new_byte * pow2(56) == 0) by {
                                    lemma_mul_by_zero_is_zero(pow2(56) as int);
                                };
                            }
                        };
                        assert(new_byte * pow2(j8 as nat) <= u64::MAX) by {
                            lemma_mul_inequality(new_byte as int, 255, pow2(56) as int);
                            assert(255 * pow(2, 56) <= u64::MAX) by (compute); 
                            assert(255 * pow2(56) <= u64::MAX) by {
                                lemma_pow2(56);
                            };
                        }
                        lemma_u64_shl_is_mul(new_byte, j8);
                    };

                    assert(old_word + (new_byte << j8) < pow2(j8next as nat)) by {
                        assert((new_byte as int) * pow2(j8 as nat) <= 255 * pow2(j8 as nat)) by {
                            lemma_mul_inequality(new_byte as int, 255, pow2(j8 as nat) as int);
                        }
                        assert(old_word + new_byte * pow2(j8 as nat) <= 256 * pow2(j8 as nat));
                        assert(256 * pow2(j8 as nat) == pow2(8) * pow2(j8 as nat)) by {
                            lemma_pow2(8);
                            assert(256 == pow(2, 8)) by (compute);
                            assert(256 == pow2(8));
                        }
                        assert(256 * pow2(j8 as nat) == pow2(8 + (j8 as nat))) by {
                            lemma_pow2_adds(8, j8 as nat);
                        }
                    }
                    
                    assert(old_word == bytes_seq_to_nat_clear(Seq::new(8, |j2: int| bytes[(i as int) * 8 + j2]), j as nat));
                    
                    assert(bytes_seq_to_nat_clear(Seq::new(8, |j2: int| bytes[(i as int) * 8 + j2]), j as nat) 
                        + pow2((j as nat) * 8) * bytes[(i as int) * 8 + j]
                        == bytes_seq_to_nat_clear(Seq::new(8, |j2: int| bytes[(i as int) * 8 + j2]), (j + 1) as nat)) by {
                        reveal(bytes_seq_to_nat_clear);
                    }
                    
                    assert(bytes_seq_to_nat_clear(Seq::new(8, |j2: int| bytes[(i as int) * 8 + j2]), j as nat) 
                        + bytes[(i as int) * 8 + j] * pow2((j as nat) * 8)
                        == bytes_seq_to_nat_clear(Seq::new(8, |j2: int| bytes[(i as int) * 8 + j2]), (j + 1) as nat)) by {
                        lemma_mul_is_commutative(bytes[(i as int) * 8 + j] as int, pow2((j as nat) * 8) as int);
                    }

                    assert(old_word + new_byte * pow2(j8 as nat) == 
                        bytes_seq_to_nat_clear(Seq::new(8, |j2: int| bytes[(i as int) * 8 + j2]), (j + 1) as nat));
                    
                    assert(old_word + new_byte * pow2(j8 as nat) ==
                            old_word + (new_byte<<j8)) by {
                        }
                }
                words[i] |= (bytes[(i * 8) + j] as u64) << (j * 8);
                proof {
                    assert(words[i as int] < pow2((j as nat + 1) * 8));
                    assert(words[i as int] ==
                           bytes_seq_to_nat_clear(Seq::new(8, |j2: int| bytes[(i as nat) * 8 + j2]), (j + 1) as nat));
                }
            }
            proof{
                assert(words[i as int] == bytes_seq_to_nat_clear(Seq::new(8, |j: int| bytes[i * 8 + j]), 8));
                assert(forall |i2: int| 0 <= i2 < i ==> ((words[i2] as nat)
                                                            == bytes_seq_to_nat_clear(
                                                                Seq::new(8, |j: int| bytes[i2*8 + j]), 8)
                                                     ));
            }
        }
        
        proof{
            // --- word 0 uses bytes 0..7 ---
            assert(forall |i2: int| 0 <= i2 < 4 ==> ((words[i2] as nat)
                                                            == bytes_seq_to_nat_clear(
                                                                Seq::new(8, |j: int| bytes[i2*8 + j]), 8)
                                                 ));

            assert(words[0] ==
                bytes[0] * pow2(0) + bytes[1] * pow2(8) + bytes[2] * pow2(16) + bytes[3] * pow2(24) +
                bytes[4] * pow2(32) + bytes[5] * pow2(40) + bytes[6] * pow2(48) + bytes[7] * pow2(56)
            ) by {
                reveal_with_fuel(bytes_seq_to_nat_clear, 10);
                byte_over_word_is_commutative(bytes[0] as nat, bytes[1] as nat, bytes[2] as nat, bytes[3] as nat,
                                              bytes[4] as nat, bytes[5] as nat, bytes[6] as nat, bytes[7] as nat);
            }

            pow2_distributivity_over_word(words[0] as nat,
                bytes[0] as nat, bytes[1] as nat, bytes[2] as nat, bytes[3] as nat,
                bytes[4] as nat, bytes[5] as nat, bytes[6] as nat, bytes[7] as nat,
                0
            );

            assert(words[1] ==
                bytes[8] * pow2(0) + bytes[9] * pow2(8) + bytes[10] * pow2(16) + bytes[11] * pow2(24) +
                bytes[12] * pow2(32) + bytes[13] * pow2(40) + bytes[14] * pow2(48) + bytes[15] * pow2(56)
            ) by {
                reveal_with_fuel(bytes_seq_to_nat_clear, 10);
                byte_over_word_is_commutative(bytes[8] as nat, bytes[9] as nat, bytes[10] as nat, bytes[11] as nat,
                    bytes[12] as nat, bytes[13] as nat, bytes[14] as nat, bytes[15] as nat);
            }

            pow2_distributivity_over_word(words[1] as nat,
                bytes[8] as nat, bytes[9] as nat, bytes[10] as nat, bytes[11] as nat,
                bytes[12] as nat, bytes[13] as nat, bytes[14] as nat, bytes[15] as nat,
                64
            );

            assert(words[2] ==
                bytes[16] * pow2(0) + bytes[17] * pow2(8) + bytes[18] * pow2(16) + bytes[19] * pow2(24) +
                bytes[20] * pow2(32) + bytes[21] * pow2(40) + bytes[22] * pow2(48) + bytes[23] * pow2(56)
            ) by {
                reveal_with_fuel(bytes_seq_to_nat_clear, 10);
                byte_over_word_is_commutative(bytes[16] as nat, bytes[17] as nat, bytes[18] as nat, bytes[19] as nat,
                    bytes[20] as nat, bytes[21] as nat, bytes[22] as nat, bytes[23] as nat);
            }   
    
            pow2_distributivity_over_word(words[2] as nat,
                bytes[16] as nat, bytes[17] as nat, bytes[18] as nat, bytes[19] as nat,
                bytes[20] as nat, bytes[21] as nat, bytes[22] as nat, bytes[23] as nat,
                128
            );
            
            assert(words[3] ==
                bytes[24] * pow2(0) + bytes[25] * pow2(8) + bytes[26] * pow2(16) + bytes[27] * pow2(24) +
                bytes[28] * pow2(32) + bytes[29] * pow2(40) + bytes[30] * pow2(48) + bytes[31] * pow2(56)
            ) by {
                reveal_with_fuel(bytes_seq_to_nat_clear, 10);
                byte_over_word_is_commutative(bytes[24] as nat, bytes[25] as nat, bytes[26] as nat, bytes[27] as nat,
                    bytes[28] as nat, bytes[29] as nat, bytes[30] as nat, bytes[31] as nat);
            }

            pow2_distributivity_over_word(words[3] as nat,
                bytes[24] as nat, bytes[25] as nat, bytes[26] as nat, bytes[27] as nat,
                bytes[28] as nat, bytes[29] as nat, bytes[30] as nat, bytes[31] as nat,
                192
            );

            reveal(bytes_to_nat);
            reveal_with_fuel(bytes_to_nat_rec, 33);
            reveal(words_to_nat);
            reveal_with_fuel(words_to_nat_gen_u64, 5);

            assert(bytes_to_nat(bytes) == words_to_nat(&words));
        }

        proof {
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
            lemma_u64_pow2_no_overflow(52);
            lemma_u64_pow2_no_overflow(40);
            lemma_u64_pow2_no_overflow(28);
            lemma_u64_pow2_no_overflow(16);

            let word_0_first = words[0] % pow2(52) as u64;
            let word_0_second = words[0] / pow2(52) as u64;
            let word_1_first = words[1] % pow2(40) as u64;
            let word_1_second = words[1] / pow2(40) as u64;
            let word_2_first = words[2] % pow2(28) as u64;
            let word_2_second = words[2] / pow2(28) as u64;
            let word_3_first = words[3] % pow2(16) as u64;
            let word_3_second = words[3] / pow2(16) as u64;
                    
            assert(words[0] == word_0_first + word_0_second * pow2(52)) by {
               lemma_fundamental_div_mod(words[0] as int, pow2(52) as int); 
            }
            assert(words[1] == word_1_first + word_1_second * pow2(40)) by {
               lemma_fundamental_div_mod(words[1] as int, pow2(40) as int); 
            }
            assert(words[2] == word_2_first + word_2_second * pow2(28)) by {
               lemma_fundamental_div_mod(words[2] as int, pow2(28) as int); 
            }
            assert(words[3] == word_3_first + word_3_second * pow2(16)) by {
               lemma_fundamental_div_mod(words[3] as int, pow2(16) as int); 
            }

            assert(mask + 1 == pow2(52)) by {
                lemma_pow2(52);
                assert((pow(2, 52) as u64) == (1u64 << 52)) by (compute);
                assert(pow(2, 52) as u64 == mask + 1);
            }
            assert(low_bits_mask(52) == mask);
            
            let words0 = words[0] as u64;
            let words1 = words[1] as u64;
            let words2 = words[2] as u64;
            let words3 = words[3] as u64;
             
            assert(words0 & mask < (1u64 << 52)) by (bit_vector)
                requires 
                    mask == ((1u64 << 52) - 1)
            ;
            assert(((words0 >> 52) | (words1 << 12)) & mask < (1u64 << 52)) by (bit_vector)
                requires 
                    mask == ((1u64 << 52) - 1)
            ;
            assert(((words1 >> 40) | (words2 << 24)) & mask < (1u64 << 52)) by (bit_vector)
                requires 
                    mask == ((1u64 << 52) - 1)
            ;
            assert(((words2 >> 28) | (words3 << 36)) & mask < (1u64 << 52)) by (bit_vector)
                requires 
                    mask == ((1u64 << 52) - 1)
            ;
            assert((words3 >> 16) & top_mask < (1u64 << 52)) by (bit_vector)
                requires 
                    top_mask == ((1u64 << 48) - 1)
            ;

            assert(s.limbs[0] == word_0_first) by {
                assert(words[0] & mask == words[0] % pow2(52) as u64) by {
                    lemma_u64_low_bits_mask_is_mod(words[0], 52);
                };
            };

            assert(s.limbs[1] == word_0_second + word_1_first * pow2(12)) by {
                assert((((words0>>52) | (words1 << 12)) & mask) ==
                       (words0>>52) + ((words1 &  (((1u64 << 40) - 1u64) as u64)) << 12)) by (bit_vector)
                    requires 
                        mask == ((1u64 << 52) - 1)
                ;

                assert(low_bits_mask(40) == ((1u64 << 40) - 1u64)) by {
                    lemma_pow2(40);
                    assert(pow(2, 40) == (1u64<<40)) by (compute);
                    assert(pow2(40) - 1 == low_bits_mask(40));
                };

                assert(((words0>>52) + ((words1 & (((1u64 << 40) - 1u64) as u64)) << 12)) ==
                    ((words0 / pow2(52) as u64) + ((words1 % pow2(40) as u64) * pow2(12)))
                    ) by {
                    lemma_u64_low_bits_mask_is_mod(words1, 40);

                    assert((words1 % pow2(40) as u64) * pow2(12) < pow2(52)) by {
                        lemma_pow2_pos(40);
                        lemma_mod_division_less_than_divisor(words1 as int, pow2(40) as int);
                        lemma_pow2_pos(12);
                        lemma_mul_strict_inequality((words1 % pow2(40) as u64) as int, pow2(40) as int, pow2(12) as int);
                        assert((words1 % pow2(40) as u64) * pow2(12) < pow2(40) * pow2(12));
                        lemma_pow2_adds(40, 12);
                    }
                    lemma_u64_shl_is_mul(words1 % pow2(40) as u64, 12);
                    lemma_u64_shr_is_div(words0, 52);
                };
    
                assert(s.limbs[1] ==
                       (words0 / pow2(52) as u64) + ((words1 % pow2(40) as u64) * pow2(12)));
            }
            
            assert(s.limbs[2] == word_1_second + word_2_first * pow2(24)) by {
                assert((((words1>>40) | (words2 << 24)) & mask) ==
                       (words1>>40) + ((words2 & (((1u64 << 28) - 1u64) as u64)) << 24)) by (bit_vector)
                    requires 
                        mask == ((1u64 << 52) - 1)
                ;


                assert(low_bits_mask(28) == ((1u64 << 28) - 1u64)) by {
                    lemma_pow2(28);
                    assert(pow(2, 28) == (1u64<<28)) by (compute);
                    assert(pow2(28) - 1 == low_bits_mask(28));
                };

                assert(((words1>>40) + ((words2 & (((1u64 << 28) - 1u64) as u64)) << 24)) ==
                    ((words1 / pow2(40) as u64) + ((words2 % pow2(28) as u64) * pow2(24)))
                    ) by {
                    lemma_u64_low_bits_mask_is_mod(words2, 28);

                    assert((words2 % pow2(28) as u64) * pow2(24) < pow2(52)) by {
                        lemma_pow2_pos(28);
                        lemma_mod_division_less_than_divisor(words2 as int, pow2(28) as int);
                        lemma_pow2_pos(24);
                        lemma_mul_strict_inequality((words2 % pow2(28) as u64) as int, pow2(28) as int, pow2(24) as int);
                        assert((words2 % pow2(28) as u64) * pow2(24) < pow2(28) * pow2(24));
                        lemma_pow2_adds(28, 24);
                    }
                    lemma_u64_shl_is_mul(words2 % pow2(28) as u64, 24);
                    lemma_u64_shr_is_div(words1, 40);
                };
                assert(s.limbs[2] ==
                       (words1 / pow2(40) as u64) + ((words2 % pow2(28) as u64) * pow2(24)));
            }

            assert(s.limbs[3] == word_2_second + word_3_first * pow2(36)) by {
                assert((((words2>>28) | (words3 << 36)) & mask) ==
                        (words2>>28) + ((words3 & (((1u64 << 16) - 1u64) as u64)) << 36)) by (bit_vector)
                    requires
                        mask == ((1u64 << 52) - 1)
                    ;

                assert(low_bits_mask(16) == ((1u64 << 16) - 1u64)) by {
                    lemma_pow2(16);
                    assert(pow(2, 16) == (1u64<<16)) by (compute);
                    assert(pow2(16) - 1 == low_bits_mask(16));
                };

                assert(((words2>>28) + ((words3 & (((1u64 << 16) - 1u64) as u64)) << 36)) ==
                    ((words2 / pow2(28) as u64) + ((words3 % pow2(16) as u64) * pow2(36)))
                ) by {
                    lemma_u64_low_bits_mask_is_mod(words3, 16);

                    assert((words3 % pow2(16) as u64) * pow2(36) < pow2(52)) by {
                        lemma_pow2_pos(16);
                        lemma_mod_division_less_than_divisor(words3 as int, pow2(16) as int);
                        lemma_pow2_pos(36);
                        lemma_mul_strict_inequality((words3 % pow2(16) as u64) as int, pow2(16) as int, pow2(36) as int);
                        assert((words3 % pow2(16) as u64) * pow2(36) < pow2(16) * pow2(36));
                        lemma_pow2_adds(16, 36);
                    }
                    lemma_u64_shl_is_mul(words3 % pow2(16) as u64, 36);
                    lemma_u64_shr_is_div(words2, 28);
                };

                assert(s.limbs[3] ==
                    (words2 / pow2(28) as u64) + ((words3 % pow2(16) as u64) * pow2(36)));
            }

            assert(s.limbs[4] == word_3_second) by {
                assert (words3>>16 & (top_mask) == words3>>16) by (bit_vector)
                    requires
                        top_mask == ((1u64 << 48) - 1u64)
                ;
                lemma_u64_shr_is_div(words3, 16);
            }
            
            reveal(to_nat);
            reveal_with_fuel(seq_to_nat, 10);
            reveal(words_to_nat);
            reveal_with_fuel(words_to_nat_gen_u64, 10);
            
            assert(words_to_nat(&words) == words[0] + words[1] * pow2(64) + words[2] * pow2(128) + words[3] * pow2(192));

            calc!{
                (==)
                    words_to_nat(&words);
                (==) {}
                (words[0] + words[1] * pow2(64) + words[2] * pow2(128) + words[3] * pow2(192)) as nat;
                (==) {}
                (   (word_0_first + word_0_second * pow2(52)) + 
                    (word_1_first + word_1_second * pow2(40)) * pow2(64) + 
                    (word_2_first + word_2_second * pow2(28)) * pow2(128) + 
                    (word_3_first + word_3_second * pow2(16)) * pow2(192)) as nat;
                (==) {
                    lemma_mul_is_distributive_add_other_way(pow2(64) as int, word_1_first as int, word_1_second * pow2(40) as int);
                    lemma_mul_is_associative(word_1_second as int, pow2(40) as int, pow2(64) as int);
                    lemma_pow2_adds(40, 64);

                    lemma_mul_is_distributive_add_other_way(pow2(128) as int, word_2_first as int, word_2_second * pow2(28) as int);
                    lemma_mul_is_associative(word_2_second as int, pow2(28) as int, pow2(128) as int);
                    lemma_pow2_adds(28, 128);

                    lemma_mul_is_distributive_add_other_way(pow2(192) as int, word_3_first as int, word_3_second * pow2(16) as int);
                    lemma_mul_is_associative(word_3_second as int, pow2(16) as int, pow2(192) as int);
                    lemma_pow2_adds(16, 192);
                }
                ( (word_0_first + word_0_second * pow2(52)) + 
                  (word_1_first * pow2(64) + word_1_second * pow2(104)) + 
                  (word_2_first * pow2(128) + word_2_second * pow2(156)) + 
                  (word_3_first * pow2(192) + word_3_second * pow2(208))
                ) as nat;
            }
            let a = s.limbs[0] as int;
            let b = s.limbs[1] as int;
            let c = s.limbs[2] as int;
            let d = s.limbs[3] as int;
            let e = s.limbs[4] as int;

            calc! {
                (==)
                    to_nat(&s.limbs) as int;
                (==) {

                }
                // Start expression
                a + (b + (c + (d + e * (pow2(52) as int)) * (pow2(52) as int)) * (pow2(52) as int)) * (pow2(52) as int);

                // 1) Expand innermost: (d + e*2^52)*2^52
                (==) {
                    lemma_mul_is_distributive_add_other_way(pow2(52) as int, d, e * (pow2(52) as int));
                    lemma_mul_is_associative(e, pow2(52) as int, pow2(52) as int);
                    lemma_pow2_adds(52, 52);
                }
                a + (b + (c + (d * (pow2(52) as int) + e * (pow2(104) as int))) * (pow2(52) as int)) * (pow2(52) as int);

                // 2) Expand next level: (c + (d*2^52 + e*2^104)) * 2^52
                (==) {
                    let T1 = d * (pow2(52) as int) + e * (pow2(104) as int);
                    lemma_mul_is_distributive_add_other_way(pow2(52) as int, c, T1);
                    lemma_mul_is_distributive_add_other_way(pow2(52) as int, d * (pow2(52) as int), e * (pow2(104) as int));
                    lemma_mul_is_associative(d, pow2(52) as int, pow2(52) as int);
                    lemma_pow2_adds(52, 52);
                    lemma_mul_is_associative(e, pow2(104) as int, pow2(52) as int);
                    lemma_pow2_adds(104, 52);
                }
                a + (b + (c * (pow2(52) as int) + d * (pow2(104) as int) + e * (pow2(156) as int))) * (pow2(52) as int);

                // 3) Expand outer level: (b + (c*2^52 + d*2^104 + e*2^156)) * 2^52
                (==) {
                    let U = c * (pow2(52) as int) + d * (pow2(104) as int) + e * (pow2(156) as int);
                    lemma_mul_is_distributive_add_other_way(pow2(52) as int, b, U);
                    let U1 = c * (pow2(52) as int) + d * (pow2(104) as int);
                    lemma_mul_is_distributive_add_other_way(pow2(52) as int, U1, e * (pow2(156) as int));
                    lemma_mul_is_distributive_add_other_way(pow2(52) as int, c * (pow2(52) as int), d * (pow2(104) as int));
                    lemma_mul_is_associative(c, pow2(52) as int, pow2(52) as int);
                    lemma_pow2_adds(52, 52);
                    lemma_mul_is_associative(d, pow2(104) as int, pow2(52) as int);
                    lemma_pow2_adds(104, 52);
                    lemma_mul_is_associative(e, pow2(156) as int, pow2(52) as int);
                    lemma_pow2_adds(156, 52);
                }
                a + b * (pow2(52) as int) + c * (pow2(104) as int) + d * (pow2(156) as int) + e * (pow2(208) as int);

                (==) {}
                word_0_first + 
                    (word_0_second + word_1_first * pow2(12)) * pow2(52) +
                    (word_1_second + word_2_first * pow2(24)) * pow2(104) +
                    (word_2_second + word_3_first * pow2(36)) * pow2(156) + 
                    word_3_second * pow2(208);
                (==) {
                    lemma_mul_is_distributive_add_other_way(pow2(52) as int, word_0_second as int, word_1_first * (pow2(12) as int));
                    lemma_mul_is_associative(word_1_first as int, pow2(12) as int, pow2(52) as int);
                    lemma_pow2_adds(12, 52);
                    assert(pow2(12) * pow2(52) == pow2(64));
                    lemma_mul_is_distributive_add_other_way(pow2(104) as int, word_1_second as int, word_2_first * (pow2(24) as int));
                    lemma_mul_is_associative(word_2_first as int, pow2(24) as int, pow2(104) as int);
                    lemma_pow2_adds(24, 104);
                    assert(pow2(12) * pow2(52) == pow2(64));
                    lemma_mul_is_distributive_add_other_way(pow2(156) as int, word_2_second as int, word_3_first * (pow2(36) as int));
                    lemma_mul_is_associative(word_3_first as int, pow2(36) as int, pow2(156) as int);
                    lemma_pow2_adds(36, 156);
                }
                (word_0_first + 
                 word_0_second * pow2(52) + word_1_first * pow2(64) +
                 word_1_second * pow2(104) + word_2_first * pow2(128) +
                 word_2_second * pow2(156) + word_3_first * pow2(192) + 
                 word_3_second * pow2(208));
            };
            assert(words_to_nat(&words) == to_nat(&s.limbs));
            assert(bytes_to_nat(bytes) == to_nat(&s.limbs));
        }
        
        assume(to_nat(&s.limbs) < group_order()); 

        s
    }

    /// Reduce a 64 byte / 512 bit scalar mod l
    #[rustfmt::skip]  // keep alignment of lo[*] and hi[*] calculations
    pub fn from_bytes_wide(bytes: &[u8; 64]) -> (s: Scalar52)
        ensures
            limbs_bounded(&s),
            to_nat(&s.limbs) % group_order() == bytes_wide_to_nat(bytes) % group_order(),
            // VERIFICATION NOTE: Result is canonical
            to_nat(&s.limbs) < group_order(),
    {
        assume(false);  // TODO: complete the proof
        let mut words = [0u64;8];
        for i in 0..8 {
            for j in 0..8 {
                assume(false);
                words[i] |= (bytes[(i * 8) + j] as u64) << (j * 8);
            }
        }

        let mask = (1u64 << 52) - 1;
        let mut lo = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        let mut hi = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };

        lo[0] = words[0] & mask;
        lo[1] = ((words[0] >> 52) | (words[1] << 12)) & mask;
        lo[2] = ((words[1] >> 40) | (words[2] << 24)) & mask;
        lo[3] = ((words[2] >> 28) | (words[3] << 36)) & mask;
        lo[4] = ((words[3] >> 16) | (words[4] << 48)) & mask;
        hi[0] = (words[4] >> 4) & mask;
        hi[1] = ((words[4] >> 56) | (words[5] << 8)) & mask;
        hi[2] = ((words[5] >> 44) | (words[6] << 20)) & mask;
        hi[3] = ((words[6] >> 32) | (words[7] << 32)) & mask;
        hi[4] = words[7] >> 20;

        lo = Scalar52::montgomery_mul(&lo, &constants::R);  // (lo * R) / R = lo
        hi = Scalar52::montgomery_mul(&hi, &constants::RR);  // (hi * R^2) / R = hi * R

        Scalar52::add(&hi, &lo)
    }

    /// Pack the limbs of this `Scalar52` into 32 bytes
    #[rustfmt::skip]  // keep alignment of s[*] calculations
    #[allow(clippy::identity_op)]
    #[allow(clippy::wrong_self_convention)]
    pub fn as_bytes(self) -> (s: [u8; 32])
        requires
            limbs_bounded(&self),
        ensures
            bytes_to_nat(&s) == to_nat(&self.limbs) % pow2(256),
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
            to_nat(&a.limbs) < group_order(),
            to_nat(&b.limbs) < group_order(),
        ensures
            to_nat(&s.limbs) == (to_nat(&a.limbs) + to_nat(&b.limbs)) % group_order(),
            // VERIFICATION NOTE: Result is canonical
            to_nat(&s.limbs) < group_order(),
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
        assert(group_order() > to_nat(&sum.limbs) - group_order() >= -group_order());
        proof {
            lemma_l_equals_group_order();
        }
        proof {
            lemma_mod_sub_multiples_vanish(to_nat(&sum.limbs) as int, group_order() as int);
        }
        Scalar52::sub(&sum, &constants::L)
    }

    // VERIFICATION NOTE: refactored sub function from Dalek upstream
    #[allow(dead_code)]
    pub fn sub_new(a: &Scalar52, b: &Scalar52) -> (s: Scalar52)
        requires
            limbs_bounded(a),
            limbs_bounded(b),
            -group_order() <= to_nat(&a.limbs) - to_nat(&b.limbs) < group_order(),
        ensures
            to_nat(&s.limbs) == (to_nat(&a.limbs) - to_nat(&b.limbs)) % (group_order() as int),
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
            to_nat(&old(self).limbs) + group_order() < pow2(260),
        ensures
    // The mathematical value modulo group_order doesn't change (since L = group_order)

            to_nat(&self.limbs) % group_order() == to_nat(&old(self).limbs) % group_order(),
            // VERIFICATION NOTE: expression below unsupported by Verus
            //limbs_bounded(&self),
            // Meaning of conditional addition
            super::subtle_assumes::choice_is_true(condition) ==> to_nat(&self.limbs) == to_nat(
                &old(self).limbs,
            ) + group_order(),
            !super::subtle_assumes::choice_is_true(condition) ==> to_nat(&self.limbs) == to_nat(
                &old(self).limbs,
            ),
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
            assume(to_nat(&self.limbs) % group_order() == to_nat(&old(self).limbs) % group_order());
            //   assume(limbs_bounded(&self));
            assume(super::subtle_assumes::choice_is_true(condition) ==> to_nat(&self.limbs)
                == to_nat(&old(self).limbs) + group_order());
            assume(!super::subtle_assumes::choice_is_true(condition) ==> to_nat(&self.limbs)
                == to_nat(&old(self).limbs));
        }

        carry
    }

    /// Compute `a - b` (mod l)
    pub fn sub(a: &Scalar52, b: &Scalar52) -> (s: Scalar52)
        requires
            limbs_bounded(a),
            limbs_bounded(b),
            // Without the following condition, all we can prove is something like:
            // to_nat(&a.limbs) >= to_nat(&b.limbs) ==> to_nat(&s.limbs) == to_nat(&a.limbs) - to_nat(&b.limbs),
            // to_nat(&a.limbs) < to_nat(&b.limbs) ==> to_nat(&s.limbs) == (to_nat(&a.limbs) - to_nat(&b.limbs) + pow2(260) + group_order()) % (pow2(260) as int),
            // In the 2nd case, `sub` doesn't always do subtraction mod group_order
            -group_order() <= to_nat(&a.limbs) - to_nat(&b.limbs) < group_order(),
        ensures
            to_nat(&s.limbs) == (to_nat(&a.limbs) - to_nat(&b.limbs)) % (group_order() as int),
            limbs_bounded(&s),
            // VERIFICATION NOTE: Result is in canonical form
            to_nat(&s.limbs) < group_order(),
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
                limbs_bounded(a),
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
            lemma_sub_correct_after_loops(difference, carry, a, b, difference_after_loop1, borrow);
        }
        difference
    }

    /// Compute `a * b`
    #[inline(always)]
    #[rustfmt::skip]  // keep alignment of z[*] calculations
    pub(crate) fn mul_internal(a: &Scalar52, b: &Scalar52) -> (z: [u128; 9])
        requires
            limbs_bounded(a),
            limbs_bounded(b),
        ensures
            slice128_to_nat(&z) == to_nat(&a.limbs) * to_nat(&b.limbs),
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
            limbs_bounded(a),
        ensures
            slice128_to_nat(&z) == to_nat(&a.limbs) * to_nat(&a.limbs),
            spec_mul_internal(a, a) == z,
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
        }

        z
    }

    /// Compute `limbs/R` (mod l), where R is the Montgomery modulus 2^260
    #[inline(always)]
    #[rustfmt::skip]  // keep alignment of n* and r* calculations
    pub(crate) fn montgomery_reduce(limbs: &[u128; 9]) -> (result:
        Scalar52)
    // If the input is the product of 2 bounded scalars, we get 2 postconditions.
    // If the 2nd scalar is also canonical, we unlock a 3rd postcondition.
    // Not all calling code needs the 3rd postcondition.
    // Note: This spec is not yet confirmed because the function is unproved.
    // The spec is checked by prop_montgomery_reduce_two_bounded and prop_montgomery_reduce_one_canonical.
    // If you edit this spec, please update the proptests.
    // Once this function and all deps are proved, you can remove those proptests,
    // and montgomery_reduce_non_canonical_product_fails_postcondition,
    // and test_canonical_scalar_generator (if it's then unused)

        ensures
            (exists|bounded1: &Scalar52, bounded2: &Scalar52|
                limbs_bounded(bounded1) && limbs_bounded(bounded2) && spec_mul_internal(
                    bounded1,
                    bounded2,
                ) == limbs) ==> ((to_nat(&result.limbs) * montgomery_radix()) % group_order()
                == slice128_to_nat(limbs) % group_order() && limbs_bounded(&result)),
            (exists|bounded: &Scalar52, canonical: &Scalar52|
                limbs_bounded(bounded) && limbs_bounded(canonical) && to_nat(&canonical.limbs)
                    < group_order() && spec_mul_internal(bounded, canonical) == limbs) ==> to_nat(
                &result.limbs,
            ) < group_order(),
    {
        assume(false);  // TODO: Add proofs

        // note: l[3] is zero, so its multiples can be skipped
        let l = &constants::L;

        // the first half computes the Montgomery adjustment factor n, and begins adding n*l to make limbs divisible by R
        let (carry, n0) = Self::part1(limbs[0]);
        let (carry, n1) = Self::part1(carry + limbs[1] + m(n0, l.limbs[1]));
        let (carry, n2) = Self::part1(carry + limbs[2] + m(n0, l.limbs[2]) + m(n1, l.limbs[1]));
        let (carry, n3) = Self::part1(carry + limbs[3] + m(n1, l.limbs[2]) + m(n2, l.limbs[1]));
        let (carry, n4) = Self::part1(
            carry + limbs[4] + m(n0, l.limbs[4]) + m(n2, l.limbs[2]) + m(n3, l.limbs[1]),
        );

        // limbs is divisible by R now, so we can divide by R by simply storing the upper half as the result
        let (carry, r0) = Self::part2(
            carry + limbs[5] + m(n1, l.limbs[4]) + m(n3, l.limbs[2]) + m(n4, l.limbs[1]),
        );
        let (carry, r1) = Self::part2(carry + limbs[6] + m(n2, l.limbs[4]) + m(n4, l.limbs[2]));
        let (carry, r2) = Self::part2(carry + limbs[7] + m(n3, l.limbs[4]));
        let (carry, r3) = Self::part2(carry + limbs[8] + m(n4, l.limbs[4]));
        let r4 = carry as u64;

        // result may be >= l, so attempt to subtract l
        Scalar52::sub(&Scalar52 { limbs: [r0, r1, r2, r3, r4] }, l)
    }

    /// Helper function for Montgomery reduction
    /// VER NOTE: spec validation needed concurrent with proof for montgomery_reduce
    #[inline(always)]
    fn part1(sum: u128) -> (res: (u128, u64))
        ensures
            ({
                let carry = res.0;
                let p = res.1;
                &&& p < (1u64 << 52)  // VER NOTE: p is bounded by 52 bits
                // VER NOTE: The sum plus p*L[0] equals carry shifted left by 52 bits (i.e., divisible by 2^52)
                &&& sum + (p as u128) * (constants::L.limbs[0] as u128) == carry << 52
            }),
    {
        assert((1u64 << 52) > 1) by (bit_vector);
        assert((1u64 << 52) - 1 > 0);
        let p = (sum as u64).wrapping_mul(constants::LFACTOR) & ((1u64 << 52) - 1);
        proof {
            let piece1 = (sum as u64).wrapping_mul(constants::LFACTOR) as u64;
            let piece2 = ((1u64 << 52) - 1) as u64;
            assert(p == piece1 & piece2);
            assert(piece1 & piece2 < (1u64 << 52)) by (bit_vector)
                requires
                    piece2 == ((1u64 << 52) - 1),
            ;
        }
        assert(p < (1u64 << 52));
        assert(constants::L.limbs[0] == 0x0002631a5cf5d3ed);
        assert(0x0002631a5cf5d3ed < (1u64 << 52)) by (bit_vector);
        assert(constants::L.limbs[0] < (1u64 << 52));
        // Going to need a precondition on sum to ensure it's small enough
        // This bound may not be the right bound
        assume(sum + p * constants::L.limbs[0] < ((2 as u64) << 63));
        let carry = (sum + m(p, constants::L.limbs[0])) >> 52;
        // Is this actually true? Not sure that the right shift and left shift cancel.
        assume(sum + (p as u128) * (constants::L.limbs[0] as u128) == carry << 52);
        (carry, p)
    }

    /// Helper function for Montgomery reduction
    /// VER NOTE: spec validation needed concurrent with proof for montgomery_reduce
    #[inline(always)]
    fn part2(sum: u128) -> (res: (u128, u64))
        ensures
            ({
                let carry = res.0;
                let w = res.1;
                &&& w < (1u64
                    << 52)  // VER NOTE: w is bounded by 52 bits (lower limb)
                // VER NOTE: The sum equals w plus carry shifted left by 52 bits
                &&& sum == (w as u128) + (carry << 52)
            }),
    {
        assume(false);  // TODO: Add proofs
        let w = (sum as u64) & ((1u64 << 52) - 1);
        let carry = sum >> 52;
        (carry, w)
    }

    /// Compute `a * b` (mod l)
    #[inline(never)]
    pub fn mul(a: &Scalar52, b: &Scalar52) -> (result: Scalar52)
        requires
            limbs_bounded(a),
            limbs_bounded(b),
        ensures
            to_nat(&result.limbs) % group_order() == (to_nat(&a.limbs) * to_nat(&b.limbs))
                % group_order(),
            // VER NOTE: Result has bounded limbs from montgomery_reduce
            limbs_bounded(&result),
            // VER NOTE: Result is canonical from montgomery_reduce
            to_nat(&result.limbs) < group_order(),
    {
        assume(false);  // TODO: Add proofs
        let ab = Scalar52::montgomery_reduce(&Scalar52::mul_internal(a, b));
        Scalar52::montgomery_reduce(&Scalar52::mul_internal(&ab, &constants::RR))
    }

    /// Compute `a^2` (mod l)
    #[inline(never)]
    #[allow(dead_code)]  // XXX we don't expose square() via the Scalar API
    pub fn square(&self) -> (result: Scalar52)
        requires
            limbs_bounded(self),
        ensures
            to_nat(&result.limbs) == (to_nat(&self.limbs) * to_nat(&self.limbs)) % group_order(),
    {
        proof {
            lemma_rr_limbs_bounded();
        }

        // We only know limbs_bounded, so this triggers the weaker part of the
        // montgomery_reduce spec
        let aa = Scalar52::montgomery_reduce(&Scalar52::square_internal(self));

        assert((to_nat(&aa.limbs) * montgomery_radix()) % group_order() == (to_nat(&self.limbs)
            * to_nat(&self.limbs)) % group_order());

        // square_internal ensures
        // ensures
        //     slice128_to_nat(&z) == to_nat(&a.limbs) * to_nat(&a.limbs),

        // We know RR < group_order, so this triggers the stronger part of the
        // montgomery_reduce spec, which is what this function's postcondition wants
        let result = Scalar52::montgomery_reduce(&Scalar52::mul_internal(&aa, &constants::RR));

        assert((to_nat(&result.limbs) * montgomery_radix()) % group_order() == (to_nat(&aa.limbs)
            * to_nat(&constants::RR.limbs)) % group_order());

        proof {
            // 1. prove (to_nat(&constants::RR.limbs) % group_order() == (montgomery_radix()*montgomery_radix()) % group_order()
            lemma_rr_equals_spec(constants::RR);

            // 2. Reduce to (to_nat(&result.limbs)) % group_order() == (to_nat(&self.limbs) * to_nat(&self.limbs)) % group_order()
            lemma_cancel_mul_montgomery_mod(
                to_nat(&result.limbs),
                to_nat(&aa.limbs),
                to_nat(&constants::RR.limbs),
            );

            // 3. allows us to assert (to_nat(&result.limbs)) % group_order() == (to_nat(&result.limbs))
            //  true from montgomery_reduce postcondition
            lemma_small_mod((to_nat(&result.limbs)), group_order())
        }

        assert((to_nat(&result.limbs)) % group_order() == (to_nat(&aa.limbs) * montgomery_radix())
            % group_order());

        result
    }

    /// Compute `(a * b) / R` (mod l), where R is the Montgomery modulus 2^260
    #[inline(never)]
    pub fn montgomery_mul(a: &Scalar52, b: &Scalar52) -> (result: Scalar52)
        requires
            limbs_bounded(a),
            limbs_bounded(b),
        ensures
            limbs_bounded(&result),
            (to_nat(&result.limbs) * montgomery_radix()) % group_order() == (to_nat(&a.limbs)
                * to_nat(&b.limbs)) % group_order(),
    {
        Scalar52::montgomery_reduce(&Scalar52::mul_internal(a, b))
    }

    /// Compute `(a^2) / R` (mod l) in Montgomery form, where R is the Montgomery modulus 2^260
    #[inline(never)]
    pub fn montgomery_square(&self) -> (result: Scalar52)
        requires
            limbs_bounded(self),
        ensures
            limbs_bounded(&result),
            (to_nat(&result.limbs) * montgomery_radix()) % group_order() == (to_nat(&self.limbs)
                * to_nat(&self.limbs)) % group_order(),
    {
        Scalar52::montgomery_reduce(&Scalar52::square_internal(self))
    }

    /// Puts a Scalar52 in to Montgomery form, i.e. computes `a*R (mod l)`
    #[inline(never)]
    pub fn as_montgomery(&self) -> (result: Scalar52)
        requires
            limbs_bounded(self),
        ensures
            limbs_bounded(&result),
            to_nat(&result.limbs) % group_order() == (to_nat(&self.limbs) * montgomery_radix())
                % group_order(),
    {
        proof {
            lemma_rr_limbs_bounded();
        }
        let result = Scalar52::montgomery_mul(self, &constants::RR);
        assume(to_nat(&result.limbs) % group_order() == (to_nat(&self.limbs) * montgomery_radix())
            % group_order());
        result
    }

    /// Takes a Scalar52 out of Montgomery form, i.e. computes `a/R (mod l)`
    #[allow(clippy::wrong_self_convention)]
    #[inline(never)]
    pub fn from_montgomery(&self) -> (result: Scalar52)
        requires
            limbs_bounded(self),
        ensures
            limbs_bounded(&result),
            (to_nat(&result.limbs) * montgomery_radix()) % group_order() == to_nat(&self.limbs)
                % group_order(),
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
            lemma_from_montgomery_is_product_with_one(self, &limbs);
        }
        let result = Scalar52::montgomery_reduce(&limbs);
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
    /// Matches the spec: to_nat(&[u64; 5])
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

    proptest! {
        #![proptest_config(proptest::test_runner::Config::with_cases(1000000))]

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
