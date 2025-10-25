#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::mul_lemmas::*;
use super::pow_lemmas::*;

verus! {


// Specialization of lemma_u64_shl_is_mul for x = 1
pub proof fn shift_is_pow2(k: nat)
    requires
        k < 64,
    ensures
        (1u64 << k) == pow2(k)
{
    pow2_le_max64(k);
    lemma_u64_shl_is_mul(1u64, k as u64);
}

// v << 0 == v for all v
pub broadcast proof fn shl_zero_is_id(v: u64)
    ensures
        #![trigger v << 0]
        v << 0 == v
{
    assert(v << 0 == v) by (bit_vector);
}

// v << (a + b) == (v << a) << b
pub proof fn shl_decomposition(v: u64, a: nat, b: nat)
    requires
        (a + b) < 64,
        v * pow2(a + b) <= u64::MAX
    ensures
        (v << (a + b)) == ((v << a) << b)
{
    if (a == 0 || b == 0) {
        broadcast use shl_zero_is_id;
    }
    else {
        // 2^(a + b) == 2^a * 2^b
        lemma_pow2_adds(a, b);
        // 2^a < 2^(a + b) ...
        lemma_pow2_strictly_increases(a, a + b);
        // ..., which implies v * 2^a < v * 2^(a + b) <= u64::MAX
        mul_le(v as nat, v as nat, pow2(a), pow2(a + b));
        // v << a + b = v * 2^(a+b)
        lemma_u64_shl_is_mul(v, (a + b) as u64);
        // v << a = v * 2^a
        lemma_u64_shl_is_mul(v, a as u64);
        // (v * 2^a) * 2^b = v * (2^a * 2^b)
        lemma_mul_is_associative(v as int, pow2(a) as int, pow2(b) as int);
        // (v * 2^a) << b = (v * 2^a) * 2^b
        lemma_u64_shl_is_mul((v * pow2(a)) as u64, b as u64);
    }
}

// [<<] preserves [<=] (u64 version)
pub proof fn lemma_shl_le_u64(a: u64, b: u64, k: nat)
    requires
        a <= b,
        k < 64,
        (b * pow2(k)) <= u64::MAX,
    ensures
        (a << k) <= (b << k)
{
    mul_le(a as nat, b as nat, pow2(k), pow2(k));
    lemma_u64_shl_is_mul(a, k as u64);
    lemma_u64_shl_is_mul(b, k as u64);
}

// // If a <= b then v << a <= v << b (up to overflow)
pub proof fn shl_nondecreasing(v: u64, a: nat, b: nat)
    requires
        a <= b < 64,
        v * pow2(b) <= u64::MAX
    ensures
        (v << a) <= (v << b)
{
    lemma2_to64(); // pow2(0)

    if (a == b) {
        // trivial
    }
    else if (a == 0) {
        // a != b <=> b > 0
        lemma_pow2_strictly_increases(0, b);
        lemma_u64_shl_is_mul(v, 0);
        lemma_u64_shl_is_mul(v, b as u64);
        mul_le(v as nat, v as nat, pow2(0), pow2(b));
    }
    else {
        // if a != 0 and a != b then 0 < d < b
        let d = b - a;

        // v << b = (v << (b - a)) << a
        shl_decomposition(v, d as nat, a);

        assert(v << d == v * pow2(d as nat)) by {
            // we need the precond v * pow2(d) < M
            lemma_pow2_strictly_increases(d as nat, b);
            mul_le(v as nat, v as nat, pow2(d as nat), pow2(b));
            lemma_u64_shl_is_mul(v, d as u64);
        }

        assert(v <= v << d) by {
            shl_zero_is_id(v);
            lemma_u64_shl_is_mul(v, 0);
            lemma_pow2_strictly_increases(0, d as nat);
            mul_le(v as nat, v as nat, pow2(0), pow2(d as nat));
        }

        lemma_pow2_adds(a, d as nat);

        assert( (v << (d as u64)) * pow2(a) <= u64::MAX ) by {
            lemma_mul_is_associative(v as int, pow2(d as nat) as int, pow2(a) as int);
        }

        // [v <= v << d] => [(v << a) <= (v << d) << a]
        lemma_shl_le_u64(v, v << (d as u64), a);
    }
}

// v >> 0 == v for all v
pub broadcast proof fn shr_zero_is_id(v: u64)
    ensures
        #![trigger v >> 0]
        v >> 0 == v
{
    assert(v >> 0 == v) by (bit_vector);
}

// v >> (a + b) == (v >> a) >> b
pub proof fn shr_decomposition(v: u64, a: nat, b: nat)
    requires
        (a + b) < 64
    ensures
        (v >> (a + b)) == ((v >> a) >> b)
{
    if (a == 0 || b == 0) {
        broadcast use shr_zero_is_id;
    }
    else {
        lemma2_to64_rest(); // pow2(64)
        lemma_pow2_strictly_increases(a, a + b);
        lemma_pow2_strictly_increases(b, a + b);
        lemma_pow2_strictly_increases(a + b, 64); // pow2(a + b) fits in u64

        // 2^(a + b) == 2^a * 2^b
        lemma_pow2_adds(a, b);
        // v >> a + b = v / 2^(a+b)
        lemma_u64_shr_is_div(v, (a + b) as u64);
        // v >> a = v / 2^a
        lemma_u64_shr_is_div(v, a as u64);
        // (v / 2^a) << b = (v / 2^a) / 2^b
        lemma_u64_shr_is_div((v / (pow2(a) as u64)) as u64, b as u64);

        // 2^k > 0
        lemma_pow2_pos(a);
        lemma_pow2_pos(b);

        // v / 2^a / 2^b = v / 2^(a + b)
        lemma_div_denominator(v as int, pow2(a) as int, pow2(b) as int);
    }
}

// [>>] preserves [<=] (u64 version)
pub proof fn lemma_shr_le_u64(a: u64, b: u64, k: nat)
    requires
        a <= b,
        k < 64
    ensures
        (a >> k) <= (b >> k)
{
    lemma_pow2_pos(k);
    lemma_u64_shr_is_div(a, k as u64);
    lemma_u64_shr_is_div(b, k as u64);
    lemma_div_is_ordered(a as int, b as int, pow2(k) as int);
}

// If a <= b then v >> a >= v >> b
pub proof fn shr_nonincreasing(v: u64, a: nat, b: nat)
    requires
        a <= b <= 64
    ensures
        v >> b <= v >> a
{
    if (b == 64) {
        assert(v >> 64 == 0) by (bit_vector);
    }
    else {
        let d = (b - a) as u64;
        // v >> b = (v >> (b - a)) >> a
        shr_decomposition(v, d as nat, a);
        assert(v >> d <= v) by (bit_vector);
        // a <= b => a >> x <= b >> x
        lemma_shr_le_u64(v >> d, v, a);
    }
}

// u64::MAX = 2^64 - 1
// u64::MAX >> k = 2^(64 - k) - 1
// 1u64 << (64 - k) = 2^(64 - k)
pub proof fn lemma_u64_max_shifting(k:nat)
    requires
        1 <= k < 64
    ensures
        u64::MAX >> k < 1u64 << (64 - k)
    decreases 64-k
{
    let M = u64::MAX;

    // recursion base case
    if (k == 63){
        assert(u64::MAX >> 63 < 1u64 << 1) by (compute);
    }
    else {
        // M >> (k + 1) < 1 << (63 - k)
        lemma_u64_max_shifting(k + 1);

        // M >> (k + 1) = (M >> k) >> 1
        shr_decomposition(M, k, 1);

        // precondition
        lemma2_to64_rest(); // pow2(63)
        lemma_pow2_strictly_increases((63 - k) as nat, (64 - k) as nat);

        assert(1u64 * pow2((64 - k) as nat) <= 1u64 * pow2(63)) by {
            if (k == 1) {
                // 64 - k = 63
                // tautology
            }
            else {
                // 64 - k < 63
                lemma_pow2_strictly_increases((64 - k) as nat, 63);
            }
            mul_le(1u64 as nat, 1u64 as nat, pow2((64 - k) as nat), pow2(63));
        }
        assert( 1u64 * pow2(63) <= u64::MAX) by (compute);

        // 1 << 64 - k = (1 << 63 - k) << 1
        shl_decomposition(1u64, (63 - k) as nat, 1);

        // (M >> k) >> 1 = (M >> k) / pow2(1);
        lemma_u64_shr_is_div( M >> k, 1);

        // lemma_u64_shl_is_mul(x, n) precondition: x * pow2(n) <= u64::MAX
        assert((1u64 << ((63 - k))) * pow2(1) <= u64::MAX) by {
            shift_is_pow2((63 - k) as nat);
            lemma_pow2_adds((63-k) as nat, 1);
        }

        // (1 << 63 - k) << 1 = (1 << 63 - k) * pow2(1);
        lemma_u64_shl_is_mul( 1u64 << ((63 - k)), 1);

        lemma2_to64(); // pow2(1) = 2

        assert((1u64 << ((64 - k) as u64)) / 2 == (1u64 << ((63 - k) as u64))) by {
            lemma_div_multiples_vanish((1u64 << (63 - k) as u64) as int, 2);
        }
    }
}

pub proof fn left_right_shift(v: u64, sl: u64, sr: u64)
    requires
        sr <= sl < 64,
        v * pow2(sl as nat) <= u64::MAX
    ensures
        (v << sl) >> sr == v << (sl - sr)
{
    let d = (sl - sr) as nat;

    assert(v << sl == v * pow2(sl as nat)) by {
        lemma_u64_shl_is_mul(v, sl);
    }

    assert(pow2(sl as nat) == pow2(d) * pow2(sr as nat)) by {
        lemma_pow2_adds(d, sr as nat);
    }

    let w = (v * pow2(sl as nat)) as nat;

    assert(w as u64 >> sr == w / pow2(sr as nat)) by {
        lemma_u64_shr_is_div(w as u64, sr);
    }

    assert(w ==  pow2(sr as nat) * (v * pow2(d))) by {
        lemma_mul_is_associative(v as int, pow2(d) as int, pow2(sr as nat) as int);
    }

    assert(pow2(sr as nat) > 0) by {
        lemma_pow2_pos(sr as nat);
    }

    assert( w / pow2(sr as nat) == v * pow2(d) ) by {
        lemma_div_multiples_vanish((v * pow2(d)) as int, pow2(sr as nat) as int);
    }

    assert(v * pow2(d) == v << (d as u64)) by {
        lemma_u64_shl_is_mul(v, d as u64);
    }
}

// Corollary of lemma_u64_max_shifting, since for any
// v: u64 it holds that v <= u64::MAX and >> preserves [<=]
pub proof fn shifted_lt(v: u64, k: nat)
    requires
        1 <= k <= 64
    ensures
        v >> k < 1u64 << (64 - k)
{
    if (k == 64) {
        assert( v >> 64 == 0) by (bit_vector);
        shl_zero_is_id(1u64);
    }
    else {
        // (v >> k) <= (u64::MAX >> k)
        lemma_shr_le_u64(v, u64::MAX, k);
        // u64::MAX >> k < 1u64 << (64 - k)
        lemma_u64_max_shifting(k);
    }
}

fn main() {}

}
