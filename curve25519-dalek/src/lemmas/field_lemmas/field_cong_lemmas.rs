//! Congruence modulo p over the integers.
//!
//! These lemmas move a nested `field_*` expression to an integer polynomial
//! that is congruent to it modulo p. A long field identity then becomes one
//! polynomial identity, which `nonlinear_arith` checks, plus multiples of
//! hypotheses that are congruent to zero.
//!
//! Each `lemma_cong_f*` lemma lifts one field operation. It takes integer
//! polynomials that are congruent to the arguments and returns the congruence
//! for the result. Apply them bottom up over an expression tree.
#![allow(unused_imports)]
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use crate::specs::primality_specs::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

/// a ≡ b (mod p), over the integers.
pub open spec fn cong(a: int, b: int) -> bool {
    a % (p() as int) == b % (p() as int)
}

pub proof fn lemma_cong_p_facts()
    ensures
        p() > 128,
        p() % 2 == 1,
        !cong(2, 0),
        !cong(4, 0),
{
    p_gt_2();
    lemma_p_is_odd();
    pow255_gt_19();
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma_pow2_strictly_increases(8, 255);
    lemma_small_mod(0, p());
    lemma_small_mod(2, p());
    lemma_small_mod(4, p());
}

pub proof fn lemma_cong_add(a: int, b: int, a2: int, b2: int)
    requires
        cong(a, a2),
        cong(b, b2),
    ensures
        cong(a + b, a2 + b2),
{
    p_gt_2();
    let m = p() as int;
    lemma_add_mod_noop(a, b, m);
    lemma_add_mod_noop(a2, b2, m);
}

pub proof fn lemma_cong_sub(a: int, b: int, a2: int, b2: int)
    requires
        cong(a, a2),
        cong(b, b2),
    ensures
        cong(a - b, a2 - b2),
{
    p_gt_2();
    let m = p() as int;
    lemma_sub_mod_noop(a, b, m);
    lemma_sub_mod_noop(a2, b2, m);
}

pub proof fn lemma_cong_mul(a: int, b: int, a2: int, b2: int)
    requires
        cong(a, a2),
        cong(b, b2),
    ensures
        cong(a * b, a2 * b2),
{
    p_gt_2();
    let m = p() as int;
    lemma_mul_mod_noop(a, b, m);
    lemma_mul_mod_noop(a2, b2, m);
}

pub proof fn lemma_cong_neg(a: int, a2: int)
    requires
        cong(a, a2),
    ensures
        cong(-a, -a2),
{
    lemma_cong_sub(0, a, 0, a2);
    assert(0 - a == -a);
    assert(0 - a2 == -a2);
}

/// If h ≡ 0, then g + q·h ≡ g.
pub proof fn lemma_cong_add_multiple(g: int, q: int, h: int)
    requires
        cong(h, 0),
    ensures
        cong(g + q * h, g),
{
    lemma_cong_mul(q, h, q, 0);
    assert(q * 0 == 0);
    lemma_cong_add(g, q * h, g, 0);
}

pub proof fn lemma_cong_fmul(a: nat, b: nat, a2: int, b2: int)
    requires
        cong(a as int, a2),
        cong(b as int, b2),
    ensures
        cong(field_mul(a, b) as int, a2 * b2),
{
    p_gt_2();
    lemma_mod_twice((a * b) as int, p() as int);
    lemma_cong_mul(a as int, b as int, a2, b2);
}

pub proof fn lemma_cong_fsquare(a: nat, a2: int)
    requires
        cong(a as int, a2),
    ensures
        cong(field_square(a) as int, a2 * a2),
{
    p_gt_2();
    lemma_mod_twice((a * a) as int, p() as int);
    lemma_cong_mul(a as int, a as int, a2, a2);
}

pub proof fn lemma_cong_fadd(a: nat, b: nat, a2: int, b2: int)
    requires
        cong(a as int, a2),
        cong(b as int, b2),
    ensures
        cong(field_add(a, b) as int, a2 + b2),
{
    p_gt_2();
    lemma_mod_twice((a + b) as int, p() as int);
    lemma_cong_add(a as int, b as int, a2, b2);
}

pub proof fn lemma_cong_fsub(a: nat, b: nat, a2: int, b2: int)
    requires
        cong(a as int, a2),
        cong(b as int, b2),
    ensures
        cong(field_sub(a, b) as int, a2 - b2),
{
    p_gt_2();
    let m = p() as int;
    let ca = (a % p()) as int;
    let cb = (b % p()) as int;
    lemma_mod_bound(a as int, m);
    lemma_mod_bound(b as int, m);
    let s = ca + m - cb;
    assert(s >= 0);
    lemma_mod_twice(a as int, m);
    lemma_mod_twice(b as int, m);
    // field_sub(a, b) == s % m
    lemma_mod_twice(s, m);
    // s ≡ ca - cb ≡ a - b
    assert(s == (ca - cb) + 1 * m);
    lemma_mod_multiples_vanish(1, ca - cb, m);
    lemma_cong_sub(ca, cb, a as int, b as int);
    lemma_cong_sub(a as int, b as int, a2, b2);
}

pub proof fn lemma_cong_fneg(a: nat, a2: int)
    requires
        cong(a as int, a2),
    ensures
        cong(field_neg(a) as int, -a2),
{
    p_gt_2();
    let m = p() as int;
    let ca = (a % p()) as int;
    lemma_mod_bound(a as int, m);
    lemma_mod_twice(a as int, m);
    let s = m - ca;
    lemma_mod_twice(s, m);
    assert(s == -ca + 1 * m);
    lemma_mod_multiples_vanish(1, -ca, m);
    lemma_cong_neg(ca, a as int);
    lemma_cong_neg(a as int, a2);
}

/// Two reduced values that are congruent are equal.
pub proof fn lemma_cong_canonical_eq(a: nat, b: nat)
    requires
        a < p(),
        b < p(),
        cong(a as int, b as int),
    ensures
        a == b,
{
    lemma_small_mod(a, p());
    lemma_small_mod(b, p());
}

/// For a reduced value, a ≡ 0 iff a == 0.
pub proof fn lemma_cong_canonical_zero(a: nat)
    requires
        a < p(),
    ensures
        cong(a as int, 0) <==> a == 0,
{
    p_gt_2();
    lemma_small_mod(a, p());
    lemma_small_mod(0, p());
}

/// field_inv(z) · z ≡ 1 when z ≢ 0.
pub proof fn lemma_cong_inv(z: nat)
    requires
        !cong(z as int, 0),
    ensures
        cong((field_inv(z) * z) as int, 1),
        field_inv(z) < p(),
{
    p_gt_2();
    lemma_small_mod(0, p());
    assert(z % p() != 0);
    field_inv_property(z);
    let zi = field_inv(z);
    let cz = field_canonical(z);
    lemma_mod_twice(z as int, p() as int);
    lemma_cong_fmul(cz, zi, z as int, zi as int);
    lemma_small_mod(1, p());
}

/// Euclid: a·b ≡ 0 implies a ≡ 0 or b ≡ 0.
pub proof fn lemma_cong_mul_zero(a: int, b: int)
    requires
        cong(a * b, 0),
    ensures
        cong(a, 0) || cong(b, 0),
{
    p_gt_2();
    let m = p() as int;
    let ca = (a % m) as nat;
    let cb = (b % m) as nat;
    lemma_mod_bound(a, m);
    lemma_mod_bound(b, m);
    lemma_mod_twice(a, m);
    lemma_mod_twice(b, m);
    lemma_cong_mul(ca as int, cb as int, a, b);
    lemma_small_mod(0, p());
    if ca % p() != 0 && cb % p() != 0 {
        crate::lemmas::field_lemmas::field_algebra_lemmas::lemma_nonzero_product(ca, cb);
        lemma_mod_bound((ca * cb) as int, m);
        assert(false);
    }
    lemma_small_mod(ca, p());
    lemma_small_mod(cb, p());
}

/// a ≢ 0 and b ≢ 0 imply a·b ≢ 0.
pub proof fn lemma_cong_mul_nonzero(a: int, b: int)
    requires
        !cong(a, 0),
        !cong(b, 0),
    ensures
        !cong(a * b, 0),
{
    if cong(a * b, 0) {
        lemma_cong_mul_zero(a, b);
    }
}

/// Cancel a nonzero factor: a·b ≡ a·c and a ≢ 0 imply b ≡ c.
pub proof fn lemma_cong_cancel(a: int, b: int, c: int)
    requires
        cong(a * b, a * c),
        !cong(a, 0),
    ensures
        cong(b, c),
{
    lemma_cong_sub(a * b, a * c, a * c, a * c);
    assert(a * b - a * c == a * (b - c)) by (nonlinear_arith);
    assert(a * c - a * c == 0);
    lemma_cong_mul_zero(a, b - c);
    lemma_cong_add(b - c, c, 0, c);
}

/// If h1 ≡ 0 and h2 ≡ 0, then q1·h1 + q2·h2 ≡ 0.
pub proof fn lemma_cong_combo2(q1: int, h1: int, q2: int, h2: int)
    requires
        cong(h1, 0),
        cong(h2, 0),
    ensures
        cong(q1 * h1 + q2 * h2, 0),
{
    lemma_cong_add_multiple(0, q1, h1);
    lemma_cong_add_multiple(q1 * h1, q2, h2);
}

/// If h1, h2, h3 ≡ 0, then q1·h1 + q2·h2 + q3·h3 ≡ 0.
pub proof fn lemma_cong_combo3(q1: int, h1: int, q2: int, h2: int, q3: int, h3: int)
    requires
        cong(h1, 0),
        cong(h2, 0),
        cong(h3, 0),
    ensures
        cong(q1 * h1 + q2 * h2 + q3 * h3, 0),
{
    lemma_cong_combo2(q1, h1, q2, h2);
    lemma_cong_add_multiple(q1 * h1 + q2 * h2, q3, h3);
}

/// a − b ≡ 0 iff a ≡ b.
pub proof fn lemma_cong_diff_zero(a: int, b: int)
    ensures
        cong(a - b, 0) <==> cong(a, b),
{
    if cong(a - b, 0) {
        lemma_cong_add(a - b, b, 0, b);
    }
    if cong(a, b) {
        lemma_cong_sub(a, b, b, b);
    }
}

/// A reduced nonzero value v has exactly one of v and p − v even.
pub proof fn lemma_neg_parity(v: nat)
    requires
        0 < v < p(),
    ensures
        field_neg(v) == (p() - v) as nat,
        is_negative(v) <==> !is_negative(field_neg(v)),
        field_neg(v) != 0,
{
    p_gt_2();
    lemma_p_is_odd();
    lemma_small_mod(v, p());
    lemma_small_mod((p() - v) as nat, p());
}

// =============================================================================
// Congruence helpers
// =============================================================================
/// cong(0, e) is false for e = ±1.
pub proof fn lemma_cong_zero_pm_one(e: int)
    requires
        e == 1 || e == -1,
    ensures
        !cong(0, e),
{
    lemma_cong_p_facts();
    lemma_small_mod(0, p());
    lemma_small_mod(1, p());
    if cong(0, e) && e == -1 {
        lemma_cong_neg(0, -1);
    }
}

// =============================================================================
// Division
// =============================================================================
/// If v ≡ a·z and zi·z ≡ 1, then field_mul(v, zi) ≡ a.
pub proof fn lemma_cong_div_z(v: nat, a: int, zi: nat, z: int)
    requires
        cong(v as int, a * z),
        cong((zi as int) * z, 1),
    ensures
        cong(field_mul(v, zi) as int, a),
{
    lemma_cong_fmul(v, zi, a * z, zi as int);
    assert(a * z * (zi as int) == a * ((zi as int) * z)) by (nonlinear_arith);
    lemma_cong_mul(a, (zi as int) * z, a, 1);
}

} // verus!
