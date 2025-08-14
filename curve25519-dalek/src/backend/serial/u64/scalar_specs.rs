#[allow(unused_imports)]
use super::scalar::Scalar52;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {
pub open spec fn seq_to_nat(limbs: Seq<nat>) -> nat
decreases limbs.len()
{
    if limbs.len() == 0 {
        0
    } else {
        limbs[0] + seq_to_nat(limbs.subrange(1, limbs.len() as int)) * pow2(52)
    }
}

pub open spec fn slice128_to_nat(limbs: &[u128]) -> nat
{
    seq_to_nat(limbs@.map(|i, x| x as nat))
}

pub open spec fn seq_u64_to_nat(limbs: Seq<u64>) -> nat
{
    seq_to_nat(limbs.map(|i, x| x as nat))
}

pub open spec fn to_nat(limbs: &[u64]) -> nat
{
    seq_to_nat(limbs@.map(|i, x| x as nat))
}

pub open spec fn nine_limbs_to_nat_aux(limbs: &[u128; 9]) -> nat {
    (limbs[0] as nat) +
    (limbs[1] as nat) * pow2(52) +
    (limbs[2] as nat) * pow2(104) +
    (limbs[3] as nat) * pow2(156) +
    (limbs[4] as nat) * pow2(208) +
    (limbs[5] as nat) * pow2(260) +
    (limbs[6] as nat) * pow2(312) +
    (limbs[7] as nat) * pow2(364) +
    (limbs[8] as nat) * pow2(416)
}

pub open spec fn five_limbs_to_nat_aux(limbs: [u64; 5]) -> nat {
    (limbs[0] as nat) +
    pow2(52) * (limbs[1] as nat) +
    pow2(104) * (limbs[2] as nat) +
    pow2(156) * (limbs[3] as nat) +
    pow2(208) * (limbs[4] as nat)
}

// Modular reduction of to_nat mod L
spec fn to_scalar(limbs: &[u64; 5]) -> nat {
    to_nat(limbs) % group_order()
}

/// natural value of a 256 bit bitstring represented as array of 32 bytes
pub open spec fn bytes_to_nat(bytes: &[u8; 32]) -> nat {
    // Convert bytes to nat in little-endian order using recursive helper
    bytes_to_nat_rec(bytes, 0)
}

pub open spec fn bytes_to_nat_rec(bytes: &[u8; 32], index: int) -> nat
decreases 32 - index
{
    if index >= 32 {
        0
    } else {
        (bytes[index] as nat) * pow2((index * 8) as nat) + bytes_to_nat_rec(bytes, index + 1)
    }
}

/// natural value of a 512 bit bitstring represented as array of 64 bytes
pub open spec fn bytes_wide_to_nat(bytes: &[u8; 64]) -> nat {
    // Convert bytes to nat in little-endian order using recursive helper
    bytes_wide_to_nat_rec(bytes, 0)
}

pub open spec fn bytes_wide_to_nat_rec(bytes: &[u8; 64], index: int) -> nat
decreases 64 - index
{
    if index >= 64 {
        0
    } else {
        (bytes[index] as nat) * pow2((index * 8) as nat) + bytes_wide_to_nat_rec(bytes, index + 1)
    }
}

// Generic function to convert array of words to natural number
// Takes: array of words, number of words, bits per word
// Note: This is a specification function that works with concrete types
pub open spec fn words_to_nat_gen_u64(words: &[u64], num_words: int, bits_per_word: int) -> nat
decreases num_words
{
    if num_words <= 0 {
        0
    } else {
        let word_value = (words[num_words - 1] as nat) * pow2(((num_words - 1) * bits_per_word) as nat);
        word_value + words_to_nat_gen_u64(words, num_words - 1, bits_per_word)
    }
}

pub open spec fn words_to_nat_gen_u32(words: &[u32], num_words: int, bits_per_word: int) -> nat
decreases num_words
{
    if num_words <= 0 {
        0
    } else {
        let word_value = (words[num_words - 1] as nat) * pow2(((num_words - 1) * bits_per_word) as nat);
        word_value + words_to_nat_gen_u32(words, num_words - 1, bits_per_word)
    }
}

// natural value of a 256 bit bitstring represented as an array of 4 words of 64 bits
// Now implemented using the generic function
pub open spec fn words_to_nat(words: &[u64; 4]) -> nat {
    words_to_nat_gen_u64(words, 4, 64)
}

// Group order: the value of L as a natural number
pub open spec fn group_order() -> nat {
    pow2(252) + 27742317777372353535851937790883648493nat
}

// Montgomery radix R = 2^260
pub open spec fn montgomery_radix() -> nat {
    pow2(260)
}

// Check that all limbs of a Scalar52 are properly bounded (< 2^52)
pub open spec fn limbs_bounded(s: &Scalar52) -> bool {
    forall|i: int| 0 <= i < 5 ==> s.limbs[i] < (1u64 << 52)
}

// ===== Elliptic Curve Point Specifications =====

// Field prime for curve25519: p = 2^255 - 19
pub open spec fn field_prime() -> nat {
    pow2(255) - 19
}

// Montgomery curve coefficient A = 486662 for curve25519
pub open spec fn curve_a() -> nat {
    486662
}

// Montgomery curve coefficient B = 1 for curve25519
pub open spec fn curve_b() -> nat {
    1
}

// Point representation on the elliptic curve
pub enum PointSpec {
    Zero,  // Point at infinity / identity element
    Affine(nat, nat),  // (x, y) coordinates as naturals
}

// Field operations modulo p
pub open spec fn field_add(a: nat, b: nat) -> nat {
    (a + b) % field_prime()
}

pub open spec fn field_sub(a: nat, b: nat) -> nat {
    if a >= b {
        (a - b) % field_prime()
    } else {
        ((field_prime() - b) + a) % field_prime()
    }
}

pub open spec fn field_mul(a: nat, b: nat) -> nat {
    (a * b) % field_prime()
}

// Extended GCD for computing modular inverse
pub open spec fn extended_gcd(a: int, b: int) -> (int, int, int)
    decreases b.abs()
{
    if b == 0 {
        (a, 1, 0)
    } else {
        let (g, x1, y1) = extended_gcd(b, a % b);
        (g, y1, x1 - (a / b) * y1)
    }
}

// Modular inverse using extended GCD
pub open spec fn field_inv(a: nat) -> nat 
    recommends a % field_prime() != 0
{
    let (g, x, y) = extended_gcd(a as int, field_prime() as int);
    if x >= 0 {
        x as nat % field_prime()
    } else {
        ((x + field_prime() as int) as nat) % field_prime()
    }
}

pub open spec fn field_div(a: nat, b: nat) -> nat
    recommends b % field_prime() != 0
{
    field_mul(a, field_inv(b))
}

// Check if a point is on the Montgomery curve: B*y^2 = x^3 + A*x^2 + x
pub open spec fn is_on_curve(p: PointSpec) -> bool {
    match p {
        PointSpec::Zero => true,
        PointSpec::Affine(x, y) => {
            let x_mod = x % field_prime();
            let y_mod = y % field_prime();
            let lhs = field_mul(curve_b(), field_mul(y_mod, y_mod));
            let x_squared = field_mul(x_mod, x_mod);
            let x_cubed = field_mul(x_squared, x_mod);
            let ax_squared = field_mul(curve_a(), x_squared);
            let rhs = field_add(field_add(x_cubed, ax_squared), x_mod);
            lhs == rhs
        }
    }
}

// Elliptic curve point addition for Montgomery curves
pub open spec fn ec_add(p: PointSpec, q: PointSpec) -> PointSpec
    recommends is_on_curve(p) && is_on_curve(q)
{
    match (p, q) {
        (PointSpec::Zero, _) => q,
        (_, PointSpec::Zero) => p,
        (PointSpec::Affine(x_p, y_p), PointSpec::Affine(x_q, y_q)) => {
            let x_p_mod = x_p % field_prime();
            let y_p_mod = y_p % field_prime();
            let x_q_mod = x_q % field_prime();
            let y_q_mod = y_q % field_prime();
            
            if x_p_mod == x_q_mod {
                if y_p_mod == y_q_mod {
                    // Point doubling case (P = Q)
                    if y_p_mod == 0 {
                        PointSpec::Zero
                    } else {
                        // s = (3*x_p^2 + 2*A*x_p + 1) / (2*B*y_p)
                        let x_p_squared = field_mul(x_p_mod, x_p_mod);
                        let three_x_p_squared = field_mul(3, x_p_squared);
                        let two_a_x_p = field_mul(field_mul(2, curve_a()), x_p_mod);
                        let numerator = field_add(field_add(three_x_p_squared, two_a_x_p), 1);
                        let two_b_y_p = field_mul(field_mul(2, curve_b()), y_p_mod);
                        let s = field_div(numerator, two_b_y_p);
                        
                        // x_r = B*s^2 - A - 2*x_p
                        let s_squared = field_mul(s, s);
                        let b_s_squared = field_mul(curve_b(), s_squared);
                        let two_x_p = field_mul(2, x_p_mod);
                        let x_r = field_sub(field_sub(b_s_squared, curve_a()), two_x_p);
                        
                        // y_r = s*(x_p - x_r) - y_p
                        let x_diff = field_sub(x_p_mod, x_r);
                        let s_x_diff = field_mul(s, x_diff);
                        let y_r = field_sub(s_x_diff, y_p_mod);
                        
                        PointSpec::Affine(x_r, y_r)
                    }
                } else {
                    // y_p = -y_q (mod p), so P + Q = O
                    PointSpec::Zero
                }
            } else {
                // General case: P != Q
                // s = (y_q - y_p) / (x_q - x_p)
                let y_diff = field_sub(y_q_mod, y_p_mod);
                let x_diff = field_sub(x_q_mod, x_p_mod);
                let s = field_div(y_diff, x_diff);
                
                // x_r = B*s^2 - A - x_p - x_q
                let s_squared = field_mul(s, s);
                let b_s_squared = field_mul(curve_b(), s_squared);
                let x_sum = field_add(x_p_mod, x_q_mod);
                let x_r = field_sub(field_sub(b_s_squared, curve_a()), x_sum);
                
                // y_r = s*(x_p - x_r) - y_p
                let x_diff = field_sub(x_p_mod, x_r);
                let s_x_diff = field_mul(s, x_diff);
                let y_r = field_sub(s_x_diff, y_p_mod);
                
                PointSpec::Affine(x_r, y_r)
            }
        }
    }
}

// Point negation
pub open spec fn ec_neg(p: PointSpec) -> PointSpec {
    match p {
        PointSpec::Zero => PointSpec::Zero,
        PointSpec::Affine(x, y) => PointSpec::Affine(x, field_sub(0, y))
    }
}

// Scalar multiplication (repeated addition)
pub open spec fn ec_scalar_mul(k: nat, p: PointSpec) -> PointSpec
    recommends is_on_curve(p)
    decreases k
{
    if k == 0 {
        PointSpec::Zero
    } else if k == 1 {
        p
    } else {
        ec_add(p, ec_scalar_mul(k - 1, p))
    }
}

} // verus!
