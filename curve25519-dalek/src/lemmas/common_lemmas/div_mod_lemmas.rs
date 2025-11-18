#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

verus! {

pub proof fn lemma_div_and_mod(ai: u64, bi: u64, v: u64, k: nat)
    requires
        k < 64,
        ai == v >> k,
        bi == v & (low_bits_mask(k) as u64),
    ensures
        ai == v / (pow2(k) as u64),
        bi == v % (pow2(k) as u64),
        v == ai * pow2(k) + bi,
{
    lemma2_to64();
    lemma2_to64_rest();  // pow2(63) = 0x8000000000000000

    // v >> k = v / pow2(k);
    lemma_u64_shr_is_div(v, k as u64);

    // v & low_bits_mask(k) = v % pow2(k);
    lemma_u64_low_bits_mask_is_mod(v, k);

    // 0 < pow2(k) <= u64::MAX
    lemma_pow2_pos(k);
    assert(pow2(k) <= u64::MAX) by {
        if (k < 63) {
            lemma_pow2_strictly_increases(k, 63);
        }
    }

    // v = (pow2(k) * (v / pow2(k)) + (v % pow2(k)))
    lemma_fundamental_div_mod(v as int, pow2(k) as int);
}

// Combination of mod lemmas, (b +- a * m) % m = b % m
pub proof fn lemma_mod_sum_factor(a: int, b: int, m: int)
    requires
        m > 0,
    ensures
        (a * m + b) % m == b % m,
{
    // (a * m + b) % m == ((a * m) % m + b % m) % m
    lemma_add_mod_noop(a * m, b, m);
    // (a * m) % m == 0
    lemma_mod_multiples_basic(a, m);
    // b % m % m = b % m
    lemma_mod_twice(b, m);
}

pub proof fn lemma_mod_diff_factor(a: int, b: int, m: int)
    requires
        m > 0,
    ensures
        (b - a * m) % m == b % m,
{
    // (b - a * m) % m == (b % m - (a * m) % m) % m
    lemma_sub_mod_noop(b, a * m, m);
    // (a * m) % m == 0
    lemma_mod_multiples_basic(a, m);
    // b % m % m = b % m
    lemma_mod_twice(b, m);
}

pub proof fn lemma_div_of_sum(a: nat, b: nat, k: nat)
    requires
        (a % k) + (b % k) < k  // also implies k != 0
        ,
    ensures
        (a + b) / k == a / k + b / k,
{
    let a0 = a / k;
    let b0 = b / k;

    assert(a == k * a0 + (a % k)) by {
        lemma_fundamental_div_mod(a as int, k as int);
    }

    assert(b == k * b0 + (b % k)) by {
        lemma_fundamental_div_mod(b as int, k as int);
    }

    assert(a + b == k * (a0 + b0) + (a % k) + (b % k)) by {
        lemma_mul_is_distributive_add(k as int, a0 as int, b0 as int);
    }

    lemma_div_multiples_vanish_fancy((a0 + b0) as int, ((a % k) + (b % k)) as int, k as int);
}

/// Helper lemma: Division with strict upper bound
/// If x < a * b and a > 0, then x / a < b
pub proof fn lemma_div_strictly_bounded(x: int, a: int, b: int)
    requires
        a > 0,
        b >= 0,
        x < a * b,
    ensures
        x / a < b,
{
    // (b * a) / a == b
    lemma_div_by_multiple(b, a);
    // x < b * a && a > 0 => x / a < (b * a) / a
    lemma_div_by_multiple_is_strongly_ordered(x, a * b, b, a);
}

/// Helper lemma: if a * b <= c and b > 0, then a <= c / b
pub proof fn lemma_mul_le_implies_div_le(a: nat, b: nat, c: nat)
    requires
        b > 0,
        a * b <= c,
    ensures
        a <= c / b,
{
    lemma_div_is_ordered((a * b) as int, c as int, b as int);
    lemma_div_by_multiple(a as int, b as int);
}

pub proof fn lemma_u8_cast_is_mod_256(x: u64)
    ensures
        (x as u8) == (x as nat) % 256,
{
    assert(x as nat % 256 == x % 256);
    assert((x as u8) == x % 256) by (bit_vector);
}

/// If low < d, then (low + mid * d) / d == mid
pub proof fn lemma_div_aligned_sum(low: nat, mid: nat, d: nat)
    requires
        d > 0,
        low < d,
    ensures
        (low + mid * d) / d == mid,
{
    // Rewrite: low + mid * d = low + d * mid
    assert(low + mid * d == low + d * mid) by {
        lemma_mul_is_commutative(mid as int, d as int);
    }

    // Since low < d, we have low / d == 0
    lemma_basic_div(low as int, d as int);
    assert(low / d == 0);

    // Use the identity: (a + b·d) / d = a/d + b when d > 0
    lemma_div_multiples_vanish(mid as int, d as int);
    // This gives: (d * mid) / d == mid

    // Now combine using nonlinear_arith
    assert((low + d * mid) / d == mid) by (nonlinear_arith)
        requires
            d > 0,
            low < d,
            low / d == 0,
            d * mid / d == mid,
    {}
}

/// Helper: If x is divisible by d*k, then x is divisible by d
///
/// Mathematical property: Divisibility transitivity
/// If (d·k) | x, then d | x
pub proof fn lemma_mod_factor_divisible(x: nat, d: nat, k: nat)
    requires
        d > 0,
        k > 0,
        x % (d * k) == 0,
    ensures
        x % d == 0,
{
    // If x % (d * k) == 0, then x = q * (d * k) for some q
    // Therefore x = q * d * k = (q * k) * d, so x % d == 0
    // First, show that d * k > 0
    lemma_mul_increases(d as int, k as int);
    assert(d * k > 0);

    lemma_fundamental_div_mod(x as int, (d * k) as int);
    let q = x / (d * k);
    assert(x == (d * k) * q);

    // Rewrite: x = (d * k) * q = d * (k * q)
    lemma_mul_is_associative((d * k) as int, q as int, 1int);
    lemma_mul_is_associative(d as int, k as int, q as int);
    assert(x == d * (k * q));

    // Since x = d * (k * q), we have x % d == 0
    // This is because x is a multiple of d
    lemma_mod_multiples_basic((k * q) as int, d as int);
    assert(((k * q) * d) % d == 0);
    assert(x % d == 0);
}

/// Helper: Sum of two numbers both divisible by d is divisible by d
///
/// Mathematical property: Closure of divisibility under addition
/// If d | a and d | b, then d | (a + b)
pub proof fn lemma_mod_sum_both_divisible(a: nat, b: nat, d: nat)
    requires
        d > 0,
        a % d == 0,
        b % d == 0,
    ensures
        (a + b) % d == 0,
{
    // a = d * q1, b = d * q2
    // a + b = d * q1 + d * q2 = d * (q1 + q2)
    lemma_fundamental_div_mod(a as int, d as int);
    lemma_fundamental_div_mod(b as int, d as int);
    let q1 = a / d;
    let q2 = b / d;
    assert(a == d * q1);
    assert(b == d * q2);
    assert(a + b == d * q1 + d * q2);
    assert(a + b == d * (q1 + q2)) by {
        lemma_mul_is_distributive_add(d as int, q1 as int, q2 as int);
    }
    // Since a + b = d * (q1 + q2), we have (a + b) % d == 0
    lemma_mod_multiples_basic((q1 + q2) as int, d as int);
    assert(((q1 + q2) * d) % d == 0);
    assert((d * (q1 + q2)) % d == 0) by {
        lemma_mul_is_commutative((q1 + q2) as int, d as int);
    }
}

/// Helper: Divisibility factorization
///
/// If n is divisible by (a·b), then (n/a) is divisible by b.
/// Proof: n = q·(a·b) = (q·b)·a, so n/a = q·b, thus (n/a) % b = 0
///
/// Mathematical property: Divisibility distribution across division
pub proof fn lemma_divisibility_factor(n: nat, a: nat, b: nat)
    requires
        n % (a * b) == 0,
        a > 0,
        b > 0,
    ensures
        (n / a) % b == 0,
{
    // Establish a * b > 0
    lemma_mul_strictly_positive(a as int, b as int);

    // Since n % (a·b) = 0, we have n = q·(a·b) for some q
    let q = n / (a * b);
    lemma_fundamental_div_mod(n as int, (a * b) as int);
    // This gives us: n == (a * b) * (n / (a * b)) + (n % (a * b))
    assert(n == (a * b) * q + (n % (a * b)));
    assert(n == (a * b) * q);  // Since n % (a * b) == 0

    // Rewrite using associativity: n = q·a·b
    assert(n == q * a * b) by {
        lemma_mul_is_associative((a * b) as int, q as int, 1);
        lemma_mul_is_commutative((a * b) as int, q as int);
        lemma_mul_is_associative(q as int, a as int, b as int);
    }

    // Further rewrite: n = (q·b)·a
    assert(n == (q * b) * a) by {
        lemma_mul_is_associative(q as int, b as int, a as int);
        lemma_mul_is_commutative(b as int, a as int);
    }

    // Divide by a: n/a = q·b
    // We have n = (q*b) * a, so n/a = q*b
    // lemma_div_multiples_vanish gives (d * x) / d == x, so we need a * (q*b)
    assert(n / a == q * b) by {
        assert(n == (q * b) * a);
        assert((q * b) * a == a * (q * b)) by {
            lemma_mul_is_commutative((q * b) as int, a as int);
        }
        lemma_div_multiples_vanish((q * b) as int, a as int);
        // This gives: (a * (q*b)) / a == q*b
        assert((a * (q * b)) / a == q * b);
        assert(n / a == q * b);
    }

    // Therefore: (n/a) % b = (q·b) % b = 0
    lemma_mod_multiples_basic(q as int, b as int);
    assert((q * b) % b == 0);
    assert((n / a) % b == 0);
}

} // verus!
