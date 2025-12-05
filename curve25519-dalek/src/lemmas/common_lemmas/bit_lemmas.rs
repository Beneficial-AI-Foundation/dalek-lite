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
        #[doc = "Proof that for any x of type "]
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

// Proofs that bitwise disjunction for N-bit integers equals addition iff for some `n` one factor 
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

// TODO: in mask_lemmas, generalize lemma_low_bits_masks_fit_u64!
lemma_distribute_over_bit_or!(lemma_u64_distribute_over_bit_or, lemma_low_bits_masks_fit_u64, u64);

verus! {

pub proof fn lemma_bitops_lifted(a: u64, b: u64, s: nat, k: nat)
    requires
        a < pow2(s),
        a + b * pow2(s) <= u64::MAX,
        s < 64,
        k < 64,
    ensures
        (a + b * pow2(s)) as nat / pow2(k) == (a as nat) / pow2(k) + (b * pow2(s)) as nat / pow2(k),
        (a + b * pow2(s)) as nat % pow2(k) == (a as nat) % pow2(k) + (b * pow2(s)) as nat % pow2(k),
{
    let pk = pow2(k);
    let pk64 = pk as u64;

    let ps = pow2(s);

    let s64 = s as u64;
    let k64 = k as u64;

    let x = a;
    let y = (b * ps) as u64;

    assert(0 < pow2(k) <= u64::MAX) by {
        lemma_pow2_pos(k);
        lemma_pow2_le_max64(k);
    }

    assert(b * ps == b << s64) by {
        lemma_u64_shl_is_mul(b, s as u64);
    }

    assert(b <= (u64::MAX >> s64)) by {
        assert(b * ps <= (u64::MAX));  // x + y <= C => y <= C for x,y >= 0
        assert((b << s64) >> s64 <= u64::MAX >> s64) by (bit_vector);
        assert(b == (b << s64) >> s64) by {
            lemma_left_right_shift(b, s64, s64);
            lemma_shl_zero_is_id(b);
        }
    }

    assert(x < 1u64 << s64) by {
        lemma_shift_is_pow2(s);
    }

    assert(x + y == x | y) by {
        lemma_u64_bit_or_is_plus(a, b, s64);
    }

    let xory = x | y;
    let lbm = (low_bits_mask(k) as u64);

    assert(xory >> k64 == (x >> k64) | (y >> k64) && xory & lbm == (x & lbm) | (y & lbm)) by {
        lemma_u64_distribute_over_bit_or(x, y, k64);
    }

    assert((a + b * ps) as nat / pk == (a as nat) / pk + (b * ps) as nat / pk) by {
        assert(xory >> k64 == xory / pk64) by {
            lemma_u64_shr_is_div(xory, k64);
        }
        assert(x >> k64 == x / pk64) by {
            lemma_u64_shr_is_div(x, k64);
        }
        assert(y >> k64 == y / pk64) by {
            lemma_u64_shr_is_div(y, k64);
        }

        assert((x / pk64) | (y / pk64) == (x / pk64) + (y / pk64)) by {
            if (s >= k) {
                let d = (s64 - k64) as u64;
                assert(y / pk64 == (b << s64) >> k64);
                assert((b << s64) >> k64 == b << d) by {
                    lemma_left_right_shift(b, s64, k64);
                }

                assert(b <= u64::MAX >> d) by {
                    assert(b <= u64::MAX >> s64);  // known
                    assert(u64::MAX >> s64 <= u64::MAX >> d) by {
                        lemma_shr_nonincreasing(u64::MAX, d as nat, s);
                    }
                }

                assert(x / pk64 < 1u64 << d) by {
                    assert(x < pow2(s));  // known
                    assert(x < pow2(d as nat) * pow2(k)) by {
                        lemma_pow2_adds(d as nat, k);
                    }
                    assert(pow2(k) > 0);  // known

                    assert(x as nat / pow2(k) < pow2(d as nat)) by {
                        lemma_multiply_divide_lt(x as int, pow2(k) as int, pow2(d as nat) as int);
                    }

                    assert(pow2(d as nat) == 1u64 << d) by {
                        lemma_shift_is_pow2(d as nat);
                    }
                }

                assert((x / pk64) | (b << d) == (x / pk64) + (b << d)) by {
                    lemma_u64_bit_or_is_plus(x / pk64, b, d);
                }
            } else {
                // s < k
                assert(x / pk64 == 0) by {
                    assert(pow2(s) < pow2(k)) by {
                        lemma_pow2_strictly_increases(s, k);
                    }
                    lemma_basic_div(x as int, pk64 as int);
                }

                assert(0 | (y / pk64) == (y / pk64)) by {
                    lemma_u64_bitwise_or_zero_is_id(y / pk64);
                }
            }

        }
    }

    assert((a + b * ps) as nat % pk == (a as nat) % pk + (b * ps) as nat % pk) by {
        assert(xory & lbm == xory % pk64) by {
            lemma_u64_low_bits_mask_is_mod(xory, k);
        }
        assert(x & lbm == x % pk64) by {
            lemma_u64_low_bits_mask_is_mod(x, k);
        }
        assert(y & lbm == y % pk64) by {
            lemma_u64_low_bits_mask_is_mod(y, k);
        }

        assert((x % pk64) | (y % pk64) == (x % pk64) + (y % pk64)) by {
            if (s >= k) {
                let d = (s - k) as nat;
                assert(y % pk64 == 0) by {
                    assert(y == pow2(k) * (b * pow2(d))) by {
                        lemma_pow2_adds(d, k);
                        lemma_mul_is_associative(b as int, pow2(d) as int, pow2(k) as int);
                        lemma_mul_is_commutative((b * pow2(d)) as int, pow2(k) as int);
                    }
                    assert(y as nat % pow2(k) == 0) by {
                        lemma_mod_multiples_basic((b * pow2(d)) as int, pow2(k) as int);
                    }
                }
                assert((x % pk64) | 0 == (x % pk64)) by {
                    lemma_u64_bitwise_or_zero_is_id(x % pk64);
                }
            } else {
                // s < k
                let d = (k - s) as nat;
                let b_n = b as nat;

                assert(pow2(d) > 0) by {
                    lemma_pow2_pos(d);
                }

                assert(x & lbm < 1u64 << s64) by {
                    assert(x & lbm <= x) by (bit_vector);
                }

                assert(y % pk64 == (b_n % pow2(d)) * pow2(s)) by {
                    lemma_pow2_mul_mod(b_n, s, k);
                }

                assert(b_n % pow2(d) <= b) by {
                    lemma_mod_decreases(b as nat, pow2(d) as nat);
                }

                assert((x & lbm) | ((b_n % pow2(d)) * pow2(s)) as u64 == (x & lbm) + ((b_n % pow2(
                    d,
                )) * pow2(s))) by {
                    assert(((b_n % pow2(d)) * pow2(s)) == (((b_n % pow2(d)) as u64) << s64)) by {
                        lemma_u64_shl_is_mul((b_n % pow2(d)) as u64, s64);
                    }
                    lemma_u64_bit_or_is_plus(x & lbm, (b_n % pow2(d)) as u64, s64);
                }
            }
        }
    }
}

} // verus!
