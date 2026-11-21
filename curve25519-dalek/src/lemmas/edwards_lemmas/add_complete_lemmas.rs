//! Completeness and closure of twisted Edwards addition.
//!
//! Main result: `lemma_edwards_add_complete_cong`. For two points on the
//! curve, with t = d·x1x2·y1y2:
//! 1. 1 + t ≢ 0 and 1 − t ≢ 0 (completeness).
//! 2. `edwards_add(x1, y1, x2, y2)` is on the curve (closure).
//!
//! Completeness: Bernstein and Lange, "Faster addition and doubling on
//! elliptic curves" (2007), Theorem 3.3, with the rotation u = i·x. It uses
//! that d is not a square.
//!
//! Closure: with Nx = x1y2 + y1x2, Ny = y1y2 + x1x2, U = y1² − x1²,
//! V = y2² − x2², A = d·x1²y1² and B = d·x2²y2², the cleared curve polynomial
//! of the sum is F = q1·c1 + q2·c2, where c1 and c2 are the curve
//! polynomials of the inputs and
//! q1 = (1 + A·B)·V − B·(U + 1 + A), q2 = 1 − A·V + A²·B.
//!
//! All algebra uses `field_cong_lemmas`: field expressions are lifted to
//! integer polynomials congruent to them mod p.
#![allow(unused_imports)]
use crate::backend::serial::u64::constants::EDWARDS_D;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::field_lemmas::field_cong_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::lemmas::ristretto_lemmas::compress_roundtrip_lemmas::{
    curve_poly, d_int, lemma_curve_cong, lemma_edwards_add_cong, lemma_edwards_d_not_square,
    lemma_mul_assoc4, lemma_sq_mul, lemma_sqrt_m1_cong,
};
use crate::specs::edwards_specs::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// Ring identities
// =============================================================================
// The proofs below are mechanical. Each product of sums is expanded by one
// `lemma_dist_K_L` call and small monomial steps, because Z3's nonlinear
// mode does not expand products of sums reliably.
/// Ny² − Nx² = U·V for the addition numerators.
proof fn lemma_id_add_num_diff(x1: int, y1: int, x2: int, y2: int)
    ensures
        (y1 * y2 + x1 * x2) * (y1 * y2 + x1 * x2) - (x1 * y2 + y1 * x2) * (x1 * y2 + y1 * x2) == (y1
            * y1 - x1 * x1) * (y2 * y2 - x2 * x2),
{
    lemma_dist_2_2(
        (x1 * x2),
        (y1 * y2),
        (x1 * x2),
        (y1 * y2),
        (y1 * y2 + x1 * x2),
        (y1 * y2 + x1 * x2),
    );
    assert(((x1 * x2)) * ((x1 * x2)) == (x1 * x1 * x2 * x2)) by (nonlinear_arith);
    assert(((x1 * x2)) * ((y1 * y2)) == (x1 * x2 * y1 * y2)) by (nonlinear_arith);
    assert(((y1 * y2)) * ((x1 * x2)) == (x1 * x2 * y1 * y2)) by (nonlinear_arith);
    assert(((y1 * y2)) * ((y1 * y2)) == (y1 * y1 * y2 * y2)) by (nonlinear_arith);
    lemma_dist_2_2(
        (x1 * y2),
        (x2 * y1),
        (x1 * y2),
        (x2 * y1),
        (x1 * y2 + y1 * x2),
        (x1 * y2 + y1 * x2),
    );
    assert(((x1 * y2)) * ((x1 * y2)) == (x1 * x1 * y2 * y2)) by (nonlinear_arith);
    assert(((x1 * y2)) * ((x2 * y1)) == (x1 * x2 * y1 * y2)) by (nonlinear_arith);
    assert(((x2 * y1)) * ((x1 * y2)) == (x1 * x2 * y1 * y2)) by (nonlinear_arith);
    assert(((x2 * y1)) * ((x2 * y1)) == (x2 * x2 * y1 * y1)) by (nonlinear_arith);
    lemma_dist_2_2(
        (-(x1 * x1)),
        (y1 * y1),
        (-(x2 * x2)),
        (y2 * y2),
        (y1 * y1 - x1 * x1),
        (y2 * y2 - x2 * x2),
    );
    assert(((-(x1 * x1))) * ((-(x2 * x2))) == (x1 * x1 * x2 * x2)) by (nonlinear_arith);
    assert(((-(x1 * x1))) * ((y2 * y2)) == (-(x1 * x1 * y2 * y2))) by (nonlinear_arith);
    assert(((y1 * y1)) * ((-(x2 * x2))) == (-(x2 * x2 * y1 * y1))) by (nonlinear_arith);
    assert(((y1 * y1)) * ((y2 * y2)) == (y1 * y1 * y2 * y2)) by (nonlinear_arith);
}

/// Nx² + Ny² = s1·s2 + 4·(x1x2)·(y1y2).
proof fn lemma_id_add_num_sum(x1: int, y1: int, x2: int, y2: int)
    ensures
        (x1 * y2 + y1 * x2) * (x1 * y2 + y1 * x2) + (y1 * y2 + x1 * x2) * (y1 * y2 + x1 * x2) == (x1
            * x1 + y1 * y1) * (x2 * x2 + y2 * y2) + 4 * ((x1 * x2) * (y1 * y2)),
{
    lemma_dist_2_2(
        (x1 * y2),
        (x2 * y1),
        (x1 * y2),
        (x2 * y1),
        (x1 * y2 + y1 * x2),
        (x1 * y2 + y1 * x2),
    );
    assert(((x1 * y2)) * ((x1 * y2)) == (x1 * x1 * y2 * y2)) by (nonlinear_arith);
    assert(((x1 * y2)) * ((x2 * y1)) == (x1 * x2 * y1 * y2)) by (nonlinear_arith);
    assert(((x2 * y1)) * ((x1 * y2)) == (x1 * x2 * y1 * y2)) by (nonlinear_arith);
    assert(((x2 * y1)) * ((x2 * y1)) == (x2 * x2 * y1 * y1)) by (nonlinear_arith);
    lemma_dist_2_2(
        (x1 * x2),
        (y1 * y2),
        (x1 * x2),
        (y1 * y2),
        (y1 * y2 + x1 * x2),
        (y1 * y2 + x1 * x2),
    );
    assert(((x1 * x2)) * ((x1 * x2)) == (x1 * x1 * x2 * x2)) by (nonlinear_arith);
    assert(((x1 * x2)) * ((y1 * y2)) == (x1 * x2 * y1 * y2)) by (nonlinear_arith);
    assert(((y1 * y2)) * ((x1 * x2)) == (x1 * x2 * y1 * y2)) by (nonlinear_arith);
    assert(((y1 * y2)) * ((y1 * y2)) == (y1 * y1 * y2 * y2)) by (nonlinear_arith);
    lemma_dist_2_2(
        (x1 * x1),
        (y1 * y1),
        (x2 * x2),
        (y2 * y2),
        (x1 * x1 + y1 * y1),
        (x2 * x2 + y2 * y2),
    );
    assert(((x1 * x1)) * ((x2 * x2)) == (x1 * x1 * x2 * x2)) by (nonlinear_arith);
    assert(((x1 * x1)) * ((y2 * y2)) == (x1 * x1 * y2 * y2)) by (nonlinear_arith);
    assert(((y1 * y1)) * ((x2 * x2)) == (x2 * x2 * y1 * y1)) by (nonlinear_arith);
    assert(((y1 * y1)) * ((y2 * y2)) == (y1 * y1 * y2 * y2)) by (nonlinear_arith);
    lemma_dist_1_1((x1 * x2), (y1 * y2), (x1 * x2), (y1 * y2));
    assert(((x1 * x2)) * ((y1 * y2)) == (x1 * x2 * y1 * y2)) by (nonlinear_arith);
}

/// Nx·Ny = p1·s2 + p2·s1.
proof fn lemma_id_add_num_prod(x1: int, y1: int, x2: int, y2: int)
    ensures
        (x1 * y2 + y1 * x2) * (y1 * y2 + x1 * x2) == (x1 * y1) * (x2 * x2 + y2 * y2) + (x2 * y2) * (
        x1 * x1 + y1 * y1),
{
    lemma_dist_2_2(
        (x1 * y2),
        (x2 * y1),
        (x1 * x2),
        (y1 * y2),
        (x1 * y2 + y1 * x2),
        (y1 * y2 + x1 * x2),
    );
    assert(((x1 * y2)) * ((x1 * x2)) == (x1 * x1 * x2 * y2)) by (nonlinear_arith);
    assert(((x1 * y2)) * ((y1 * y2)) == (x1 * y1 * y2 * y2)) by (nonlinear_arith);
    assert(((x2 * y1)) * ((x1 * x2)) == (x1 * x2 * x2 * y1)) by (nonlinear_arith);
    assert(((x2 * y1)) * ((y1 * y2)) == (x2 * y1 * y1 * y2)) by (nonlinear_arith);
    lemma_dist_1_2((x1 * y1), (x2 * x2), (y2 * y2), (x1 * y1), (x2 * x2 + y2 * y2));
    assert(((x1 * y1)) * ((x2 * x2)) == (x1 * x2 * x2 * y1)) by (nonlinear_arith);
    assert(((x1 * y1)) * ((y2 * y2)) == (x1 * y1 * y2 * y2)) by (nonlinear_arith);
    lemma_dist_1_2((x2 * y2), (x1 * x1), (y1 * y1), (x2 * y2), (x1 * x1 + y1 * y1));
    assert(((x2 * y2)) * ((x1 * x1)) == (x1 * x1 * x2 * y2)) by (nonlinear_arith);
    assert(((x2 * y2)) * ((y1 * y1)) == (x2 * y1 * y1 * y2)) by (nonlinear_arith);
}

/// (a·b)·(c·e) = (a·c)·(b·e).
proof fn lemma_id_swap4(a: int, b: int, c: int, e: int)
    ensures
        (a * b) * (c * e) == (a * c) * (b * e),
{
    lemma_dist_1_1((a * b), (c * e), (a * b), (c * e));
    assert(((a * b)) * ((c * e)) == (a * b * c * e)) by (nonlinear_arith);
    lemma_dist_1_1((a * c), (b * e), (a * c), (b * e));
    assert(((a * c)) * ((b * e)) == (a * b * c * e)) by (nonlinear_arith);
}

/// d·(p1·s2 + p2·s1)² in terms of A = d·p1², B = d·p2² and T = d·p1·p2, plus two terms that vanish on the curve.
proof fn lemma_id_add_d_prod(d: int, p1: int, p2: int, s1: int, s2: int, u: int, v: int)
    ensures
        d * ((p1 * s2 + p2 * s1) * (p1 * s2 + p2 * s1)) == (d * (p1 * p1)) * (v * v) + (d * (p2
            * p2)) * (u * u) + 2 * (d * (p1 * p2)) * (s1 * s2 + 4 * (p1 * p2)) + (d * (p1 * p1)) * (
        s2 * s2 - v * v - 4 * (p2 * p2)) + (d * (p2 * p2)) * (s1 * s1 - u * u - 4 * (p1 * p1)),
{
    lemma_dist_2_2(
        (p1 * s2),
        (p2 * s1),
        (p1 * s2),
        (p2 * s1),
        (p1 * s2 + p2 * s1),
        (p1 * s2 + p2 * s1),
    );
    assert(((p1 * s2)) * ((p1 * s2)) == (p1 * p1 * s2 * s2)) by (nonlinear_arith);
    assert(((p1 * s2)) * ((p2 * s1)) == (p1 * p2 * s1 * s2)) by (nonlinear_arith);
    assert(((p2 * s1)) * ((p1 * s2)) == (p1 * p2 * s1 * s2)) by (nonlinear_arith);
    assert(((p2 * s1)) * ((p2 * s1)) == (p2 * p2 * s1 * s1)) by (nonlinear_arith);
    lemma_dist_1_3(
        (d),
        (p1 * p1 * s2 * s2),
        (2 * (p1 * p2 * s1 * s2)),
        (p2 * p2 * s1 * s1),
        (d),
        ((p1 * s2 + p2 * s1) * (p1 * s2 + p2 * s1)),
    );
    assert(((d)) * ((p1 * p1 * s2 * s2)) == (d * p1 * p1 * s2 * s2)) by (nonlinear_arith);
    assert(((d)) * ((2 * (p1 * p2 * s1 * s2))) == (2 * (d * p1 * p2 * s1 * s2)))
        by (nonlinear_arith);
    assert(((d)) * ((p2 * p2 * s1 * s1)) == (d * p2 * p2 * s1 * s1)) by (nonlinear_arith);
    lemma_dist_1_1((d), (p1 * p1), (d), (p1 * p1));
    assert(((d)) * ((p1 * p1)) == (d * p1 * p1)) by (nonlinear_arith);
    lemma_dist_1_1((d * p1 * p1), (v * v), (d * (p1 * p1)), (v * v));
    assert(((d * p1 * p1)) * ((v * v)) == (d * p1 * p1 * v * v)) by (nonlinear_arith);
    lemma_dist_1_1((d), (p2 * p2), (d), (p2 * p2));
    assert(((d)) * ((p2 * p2)) == (d * p2 * p2)) by (nonlinear_arith);
    lemma_dist_1_1((d * p2 * p2), (u * u), (d * (p2 * p2)), (u * u));
    assert(((d * p2 * p2)) * ((u * u)) == (d * p2 * p2 * u * u)) by (nonlinear_arith);
    lemma_dist_1_1((d), (p1 * p2), (d), (p1 * p2));
    assert(((d)) * ((p1 * p2)) == (d * p1 * p2)) by (nonlinear_arith);
    lemma_dist_1_2(
        (2 * (d * p1 * p2)),
        (4 * (p1 * p2)),
        (s1 * s2),
        (2 * (d * (p1 * p2))),
        (s1 * s2 + 4 * (p1 * p2)),
    );
    assert(((2 * (d * p1 * p2))) * ((4 * (p1 * p2))) == (8 * (d * p1 * p1 * p2 * p2)))
        by (nonlinear_arith);
    assert(((2 * (d * p1 * p2))) * ((s1 * s2)) == (2 * (d * p1 * p2 * s1 * s2)))
        by (nonlinear_arith);
    lemma_dist_1_1((d), (p1 * p1), (d), (p1 * p1));
    assert(((d)) * ((p1 * p1)) == (d * p1 * p1)) by (nonlinear_arith);
    lemma_dist_1_3(
        (d * p1 * p1),
        (-(4 * (p2 * p2))),
        (s2 * s2),
        (-(v * v)),
        (d * (p1 * p1)),
        (s2 * s2 - v * v - 4 * (p2 * p2)),
    );
    assert(((d * p1 * p1)) * ((-(4 * (p2 * p2)))) == (-(4 * (d * p1 * p1 * p2 * p2))))
        by (nonlinear_arith);
    assert(((d * p1 * p1)) * ((s2 * s2)) == (d * p1 * p1 * s2 * s2)) by (nonlinear_arith);
    assert(((d * p1 * p1)) * ((-(v * v))) == (-(d * p1 * p1 * v * v))) by (nonlinear_arith);
    lemma_dist_1_1((d), (p2 * p2), (d), (p2 * p2));
    assert(((d)) * ((p2 * p2)) == (d * p2 * p2)) by (nonlinear_arith);
    lemma_dist_1_3(
        (d * p2 * p2),
        (-(4 * (p1 * p1))),
        (s1 * s1),
        (-(u * u)),
        (d * (p2 * p2)),
        (s1 * s1 - u * u - 4 * (p1 * p1)),
    );
    assert(((d * p2 * p2)) * ((-(4 * (p1 * p1)))) == (-(4 * (d * p1 * p1 * p2 * p2))))
        by (nonlinear_arith);
    assert(((d * p2 * p2)) * ((s1 * s1)) == (d * p2 * p2 * s1 * s1)) by (nonlinear_arith);
    assert(((d * p2 * p2)) * ((-(u * u))) == (-(d * p2 * p2 * u * u))) by (nonlinear_arith);
}

/// s² = U² + 4·p², with s = x² + y², U = y² − x², p = x·y.
proof fn lemma_id_sum_sq_rel(x: int, y: int)
    ensures
        (x * x + y * y) * (x * x + y * y) - (y * y - x * x) * (y * y - x * x) - 4 * ((x * y) * (x
            * y)) == 0,
{
    lemma_dist_2_2((x * x), (y * y), (x * x), (y * y), (x * x + y * y), (x * x + y * y));
    assert(((x * x)) * ((x * x)) == (x * x * x * x)) by (nonlinear_arith);
    assert(((x * x)) * ((y * y)) == (x * x * y * y)) by (nonlinear_arith);
    assert(((y * y)) * ((x * x)) == (x * x * y * y)) by (nonlinear_arith);
    assert(((y * y)) * ((y * y)) == (y * y * y * y)) by (nonlinear_arith);
    lemma_dist_2_2((-(x * x)), (y * y), (-(x * x)), (y * y), (y * y - x * x), (y * y - x * x));
    assert(((-(x * x))) * ((-(x * x))) == (x * x * x * x)) by (nonlinear_arith);
    assert(((-(x * x))) * ((y * y)) == (-(x * x * y * y))) by (nonlinear_arith);
    assert(((y * y)) * ((-(x * x))) == (-(x * x * y * y))) by (nonlinear_arith);
    assert(((y * y)) * ((y * y)) == (y * y * y * y)) by (nonlinear_arith);
    lemma_dist_1_1((x * y), (x * y), (x * y), (x * y));
    assert(((x * y)) * ((x * y)) == (x * x * y * y)) by (nonlinear_arith);
}

/// The cleared curve polynomial of the sum, in t = T, xx = Nx² and yy = Ny².
proof fn lemma_id_add_cleared(t: int, xx: int, yy: int)
    ensures
        (1 + t) * (1 + t) * yy - (1 - t) * (1 - t) * xx - ((1 + t) * (1 - t)) * ((1 + t) * (1 - t))
            == (1 + t * t) * (yy - xx) + 2 * t * (xx + yy) - (1 - t * t) * (1 - t * t),
{
    lemma_dist_2_2(1, (t), 1, (t), (1 + t), (1 + t));
    assert((1) * (1) == 1) by (nonlinear_arith);
    assert((1) * ((t)) == (t)) by (nonlinear_arith);
    assert(((t)) * (1) == (t)) by (nonlinear_arith);
    assert(((t)) * ((t)) == (t * t)) by (nonlinear_arith);
    lemma_dist_3_1(1, (2 * (t)), (t * t), (yy), ((1 + t) * (1 + t)), (yy));
    assert((1) * ((yy)) == (yy)) by (nonlinear_arith);
    assert(((2 * (t))) * ((yy)) == (2 * (t * yy))) by (nonlinear_arith);
    assert(((t * t)) * ((yy)) == (t * t * yy)) by (nonlinear_arith);
    lemma_dist_2_2(1, (-(t)), 1, (-(t)), (1 - t), (1 - t));
    assert((1) * (1) == 1) by (nonlinear_arith);
    assert((1) * ((-(t))) == (-(t))) by (nonlinear_arith);
    assert(((-(t))) * (1) == (-(t))) by (nonlinear_arith);
    assert(((-(t))) * ((-(t))) == (t * t)) by (nonlinear_arith);
    lemma_dist_3_1(1, (-(2 * (t))), (t * t), (xx), ((1 - t) * (1 - t)), (xx));
    assert((1) * ((xx)) == (xx)) by (nonlinear_arith);
    assert(((-(2 * (t)))) * ((xx)) == (-(2 * (t * xx)))) by (nonlinear_arith);
    assert(((t * t)) * ((xx)) == (t * t * xx)) by (nonlinear_arith);
    lemma_dist_2_2(1, (t), 1, (-(t)), (1 + t), (1 - t));
    assert((1) * (1) == 1) by (nonlinear_arith);
    assert((1) * ((-(t))) == (-(t))) by (nonlinear_arith);
    assert(((t)) * (1) == (t)) by (nonlinear_arith);
    assert(((t)) * ((-(t))) == (-(t * t))) by (nonlinear_arith);
    lemma_dist_2_2(1, (t), 1, (-(t)), (1 + t), (1 - t));
    assert((1) * (1) == 1) by (nonlinear_arith);
    assert((1) * ((-(t))) == (-(t))) by (nonlinear_arith);
    assert(((t)) * (1) == (t)) by (nonlinear_arith);
    assert(((t)) * ((-(t))) == (-(t * t))) by (nonlinear_arith);
    lemma_dist_2_2(1, (-(t * t)), 1, (-(t * t)), ((1 + t) * (1 - t)), ((1 + t) * (1 - t)));
    assert((1) * (1) == 1) by (nonlinear_arith);
    assert((1) * ((-(t * t))) == (-(t * t))) by (nonlinear_arith);
    assert(((-(t * t))) * (1) == (-(t * t))) by (nonlinear_arith);
    assert(((-(t * t))) * ((-(t * t))) == (t * t * t * t)) by (nonlinear_arith);
    lemma_dist_2_2(1, (t * t), (-(xx)), (yy), (1 + t * t), (yy - xx));
    assert((1) * ((-(xx))) == (-(xx))) by (nonlinear_arith);
    assert((1) * ((yy)) == (yy)) by (nonlinear_arith);
    assert(((t * t)) * ((-(xx))) == (-(t * t * xx))) by (nonlinear_arith);
    assert(((t * t)) * ((yy)) == (t * t * yy)) by (nonlinear_arith);
    lemma_dist_1_2((2 * (t)), (xx), (yy), (2 * t), (xx + yy));
    assert(((2 * (t))) * ((xx)) == (2 * (t * xx))) by (nonlinear_arith);
    assert(((2 * (t))) * ((yy)) == (2 * (t * yy))) by (nonlinear_arith);
    lemma_dist_2_2(1, (-(t * t)), 1, (-(t * t)), (1 - t * t), (1 - t * t));
    assert((1) * (1) == 1) by (nonlinear_arith);
    assert((1) * ((-(t * t))) == (-(t * t))) by (nonlinear_arith);
    assert(((-(t * t))) * (1) == (-(t * t))) by (nonlinear_arith);
    assert(((-(t * t))) * ((-(t * t))) == (t * t * t * t)) by (nonlinear_arith);
}

/// The closure certificate: F = q1·c1 + q2·c2 + (t² − a·b)·K.
proof fn lemma_id_add_certificate(u: int, v: int, a: int, b: int, t: int)
    ensures
        (1 + t * t) * (u * v) - a * (v * v) - b * (u * u) - (1 - t * t) * (1 - t * t) == ((1 + a
            * b) * v - b * (u + 1 + a)) * (u - 1 - a) + (1 - a * v + a * a * b) * (v - 1 - b) + (t
            * t - a * b) * (u * v + 2 - t * t - a * b),
{
    lemma_dist_2_1(1, (t * t), (u * v), (1 + t * t), (u * v));
    assert((1) * ((u * v)) == (u * v)) by (nonlinear_arith);
    assert(((t * t)) * ((u * v)) == (t * t * u * v)) by (nonlinear_arith);
    lemma_dist_1_1((a), (v * v), (a), (v * v));
    assert(((a)) * ((v * v)) == (a * v * v)) by (nonlinear_arith);
    lemma_dist_1_1((b), (u * u), (b), (u * u));
    assert(((b)) * ((u * u)) == (b * u * u)) by (nonlinear_arith);
    lemma_dist_2_2(1, (-(t * t)), 1, (-(t * t)), (1 - t * t), (1 - t * t));
    assert((1) * (1) == 1) by (nonlinear_arith);
    assert((1) * ((-(t * t))) == (-(t * t))) by (nonlinear_arith);
    assert(((-(t * t))) * (1) == (-(t * t))) by (nonlinear_arith);
    assert(((-(t * t))) * ((-(t * t))) == (t * t * t * t)) by (nonlinear_arith);
    lemma_dist_2_1(1, (a * b), (v), (1 + a * b), (v));
    assert((1) * ((v)) == (v)) by (nonlinear_arith);
    assert(((a * b)) * ((v)) == (a * b * v)) by (nonlinear_arith);
    lemma_dist_1_3((b), 1, (a), (u), (b), (u + 1 + a));
    assert(((b)) * (1) == (b)) by (nonlinear_arith);
    assert(((b)) * ((a)) == (a * b)) by (nonlinear_arith);
    assert(((b)) * ((u)) == (b * u)) by (nonlinear_arith);
    lemma_dist_5_3(
        (-(a * b)),
        (a * b * v),
        (-(b)),
        (-(b * u)),
        (v),
        (-1),
        (-(a)),
        (u),
        ((1 + a * b) * v - b * (u + 1 + a)),
        (u - 1 - a),
    );
    assert(((-(a * b))) * ((-1)) == (a * b)) by (nonlinear_arith);
    assert(((-(a * b))) * ((-(a))) == (a * a * b)) by (nonlinear_arith);
    assert(((-(a * b))) * ((u)) == (-(a * b * u))) by (nonlinear_arith);
    assert(((a * b * v)) * ((-1)) == (-(a * b * v))) by (nonlinear_arith);
    assert(((a * b * v)) * ((-(a))) == (-(a * a * b * v))) by (nonlinear_arith);
    assert(((a * b * v)) * ((u)) == (a * b * u * v)) by (nonlinear_arith);
    assert(((-(b))) * ((-1)) == (b)) by (nonlinear_arith);
    assert(((-(b))) * ((-(a))) == (a * b)) by (nonlinear_arith);
    assert(((-(b))) * ((u)) == (-(b * u))) by (nonlinear_arith);
    assert(((-(b * u))) * ((-1)) == (b * u)) by (nonlinear_arith);
    assert(((-(b * u))) * ((-(a))) == (a * b * u)) by (nonlinear_arith);
    assert(((-(b * u))) * ((u)) == (-(b * u * u))) by (nonlinear_arith);
    assert(((v)) * ((-1)) == (-(v))) by (nonlinear_arith);
    assert(((v)) * ((-(a))) == (-(a * v))) by (nonlinear_arith);
    assert(((v)) * ((u)) == (u * v)) by (nonlinear_arith);
    lemma_dist_3_3(
        1,
        (a * a * b),
        (-(a * v)),
        (-1),
        (-(b)),
        (v),
        (1 - a * v + a * a * b),
        (v - 1 - b),
    );
    assert((1) * ((-1)) == (-1)) by (nonlinear_arith);
    assert((1) * ((-(b))) == (-(b))) by (nonlinear_arith);
    assert((1) * ((v)) == (v)) by (nonlinear_arith);
    assert(((a * a * b)) * ((-1)) == (-(a * a * b))) by (nonlinear_arith);
    assert(((a * a * b)) * ((-(b))) == (-(a * a * b * b))) by (nonlinear_arith);
    assert(((a * a * b)) * ((v)) == (a * a * b * v)) by (nonlinear_arith);
    assert(((-(a * v))) * ((-1)) == (a * v)) by (nonlinear_arith);
    assert(((-(a * v))) * ((-(b))) == (a * b * v)) by (nonlinear_arith);
    assert(((-(a * v))) * ((v)) == (-(a * v * v))) by (nonlinear_arith);
    lemma_dist_2_4(
        (-(a * b)),
        (t * t),
        2,
        (-(a * b)),
        (-(t * t)),
        (u * v),
        (t * t - a * b),
        (u * v + 2 - t * t - a * b),
    );
    assert(((-(a * b))) * (2) == (-(2 * (a * b)))) by (nonlinear_arith);
    assert(((-(a * b))) * ((-(a * b))) == (a * a * b * b)) by (nonlinear_arith);
    assert(((-(a * b))) * ((-(t * t))) == (a * b * t * t)) by (nonlinear_arith);
    assert(((-(a * b))) * ((u * v)) == (-(a * b * u * v))) by (nonlinear_arith);
    assert(((t * t)) * (2) == (2 * (t * t))) by (nonlinear_arith);
    assert(((t * t)) * ((-(a * b))) == (-(a * b * t * t))) by (nonlinear_arith);
    assert(((t * t)) * ((-(t * t))) == (-(t * t * t * t))) by (nonlinear_arith);
    assert(((t * t)) * ((u * v)) == (t * t * u * v)) by (nonlinear_arith);
}

/// (−d)·((−a)·b) = d·(a·b).
proof fn lemma_id_neg_neg(d: int, a: int, b: int)
    ensures
        (-d) * ((-a) * b) == d * (a * b),
{
    lemma_dist_1_1((-(a)), (b), (-a), (b));
    assert(((-(a))) * ((b)) == (-(a * b))) by (nonlinear_arith);
    lemma_dist_1_1((-(d)), (-(a * b)), (-d), (-a * b));
    assert(((-(d))) * ((-(a * b))) == (a * b * d)) by (nonlinear_arith);
    lemma_dist_1_1((d), (a * b), (d), (a * b));
    assert(((d)) * ((a * b)) == (a * b * d)) by (nonlinear_arith);
}

/// (u + s·y)² with q = u·y, for s = 1 and s = −1.
proof fn lemma_id_sq_plus(u: int, y: int)
    ensures
        (u + y) * (u + y) == u * u + 2 * (u * y) + y * y,
{
    lemma_dist_2_2((u), (y), (u), (y), (u + y), (u + y));
    assert(((u)) * ((u)) == (u * u)) by (nonlinear_arith);
    assert(((u)) * ((y)) == (u * y)) by (nonlinear_arith);
    assert(((y)) * ((u)) == (u * y)) by (nonlinear_arith);
    assert(((y)) * ((y)) == (y * y)) by (nonlinear_arith);
}

proof fn lemma_id_sq_minus(u: int, y: int)
    ensures
        (u - y) * (u - y) == u * u - 2 * (u * y) + y * y,
{
    lemma_dist_2_2((u), (-(y)), (u), (-(y)), (u - y), (u - y));
    assert(((u)) * ((u)) == (u * u)) by (nonlinear_arith);
    assert(((u)) * ((-(y))) == (-(u * y))) by (nonlinear_arith);
    assert(((-(y))) * ((u)) == (-(u * y))) by (nonlinear_arith);
    assert(((-(y))) * ((-(y))) == (y * y)) by (nonlinear_arith);
}

/// Denominator certificate for s = 1, ε = 1 (P = u1·y1, Q = u2·y2, k = dp·P·Q).
#[verifier::rlimit(30)]
proof fn lemma_id_denom_cert_pp(u1: int, y1: int, u2: int, y2: int, dp: int, pp: int, qq: int)
    ensures
        dp * (pp * pp) * (u2 * u2 + 2 * qq + y2 * y2) - (u1 * u1 + 2 * pp + y1 * y1) == dp * (pp
            * pp) * (u2 * u2 + y2 * y2 - 1 - dp * (qq * qq)) - (u1 * u1 + y1 * y1 - 1 - dp * (pp
            * pp)) + (dp * (pp * qq) - 1) * (dp * (pp * qq) + 1 + 2 * pp),
{
    lemma_dist_1_1((dp), (pp * pp), (dp), (pp * pp));
    assert(((dp)) * ((pp * pp)) == (dp * pp * pp)) by (nonlinear_arith);
    lemma_dist_1_3(
        (dp * pp * pp),
        (2 * (qq)),
        (u2 * u2),
        (y2 * y2),
        (dp * (pp * pp)),
        (u2 * u2 + 2 * qq + y2 * y2),
    );
    assert(((dp * pp * pp)) * ((2 * (qq))) == (2 * (dp * pp * pp * qq))) by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((u2 * u2)) == (dp * pp * pp * u2 * u2)) by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((y2 * y2)) == (dp * pp * pp * y2 * y2)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (pp * pp), (dp), (pp * pp));
    assert(((dp)) * ((pp * pp)) == (dp * pp * pp)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (qq * qq), (dp), (qq * qq));
    assert(((dp)) * ((qq * qq)) == (dp * qq * qq)) by (nonlinear_arith);
    lemma_dist_1_4(
        (dp * pp * pp),
        (-1),
        (-(dp * qq * qq)),
        (u2 * u2),
        (y2 * y2),
        (dp * (pp * pp)),
        (u2 * u2 + y2 * y2 - 1 - dp * (qq * qq)),
    );
    assert(((dp * pp * pp)) * ((-1)) == (-(dp * pp * pp))) by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((-(dp * qq * qq))) == (-(dp * dp * pp * pp * qq * qq)))
        by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((u2 * u2)) == (dp * pp * pp * u2 * u2)) by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((y2 * y2)) == (dp * pp * pp * y2 * y2)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (pp * pp), (dp), (pp * pp));
    assert(((dp)) * ((pp * pp)) == (dp * pp * pp)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (pp * qq), (dp), (pp * qq));
    assert(((dp)) * ((pp * qq)) == (dp * pp * qq)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (pp * qq), (dp), (pp * qq));
    assert(((dp)) * ((pp * qq)) == (dp * pp * qq)) by (nonlinear_arith);
    lemma_dist_2_3(
        (-1),
        (dp * pp * qq),
        1,
        (dp * pp * qq),
        (2 * (pp)),
        (dp * (pp * qq) - 1),
        (dp * (pp * qq) + 1 + 2 * pp),
    );
    assert(((-1)) * (1) == (-1)) by (nonlinear_arith);
    assert(((-1)) * ((dp * pp * qq)) == (-(dp * pp * qq))) by (nonlinear_arith);
    assert(((-1)) * ((2 * (pp))) == (-(2 * (pp)))) by (nonlinear_arith);
    assert(((dp * pp * qq)) * (1) == (dp * pp * qq)) by (nonlinear_arith);
    assert(((dp * pp * qq)) * ((dp * pp * qq)) == (dp * dp * pp * pp * qq * qq))
        by (nonlinear_arith);
    assert(((dp * pp * qq)) * ((2 * (pp))) == (2 * (dp * pp * pp * qq))) by (nonlinear_arith);
}

/// Denominator certificate for s = 1, ε = -1 (P = u1·y1, Q = u2·y2, k = dp·P·Q).
#[verifier::rlimit(30)]
proof fn lemma_id_denom_cert_pm(u1: int, y1: int, u2: int, y2: int, dp: int, pp: int, qq: int)
    ensures
        dp * (pp * pp) * (u2 * u2 + 2 * qq + y2 * y2) - (u1 * u1 - 2 * pp + y1 * y1) == dp * (pp
            * pp) * (u2 * u2 + y2 * y2 - 1 - dp * (qq * qq)) - (u1 * u1 + y1 * y1 - 1 - dp * (pp
            * pp)) + (dp * (pp * qq) + 1) * (dp * (pp * qq) - 1 + 2 * pp),
{
    lemma_dist_1_1((dp), (pp * pp), (dp), (pp * pp));
    assert(((dp)) * ((pp * pp)) == (dp * pp * pp)) by (nonlinear_arith);
    lemma_dist_1_3(
        (dp * pp * pp),
        (2 * (qq)),
        (u2 * u2),
        (y2 * y2),
        (dp * (pp * pp)),
        (u2 * u2 + 2 * qq + y2 * y2),
    );
    assert(((dp * pp * pp)) * ((2 * (qq))) == (2 * (dp * pp * pp * qq))) by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((u2 * u2)) == (dp * pp * pp * u2 * u2)) by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((y2 * y2)) == (dp * pp * pp * y2 * y2)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (pp * pp), (dp), (pp * pp));
    assert(((dp)) * ((pp * pp)) == (dp * pp * pp)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (qq * qq), (dp), (qq * qq));
    assert(((dp)) * ((qq * qq)) == (dp * qq * qq)) by (nonlinear_arith);
    lemma_dist_1_4(
        (dp * pp * pp),
        (-1),
        (-(dp * qq * qq)),
        (u2 * u2),
        (y2 * y2),
        (dp * (pp * pp)),
        (u2 * u2 + y2 * y2 - 1 - dp * (qq * qq)),
    );
    assert(((dp * pp * pp)) * ((-1)) == (-(dp * pp * pp))) by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((-(dp * qq * qq))) == (-(dp * dp * pp * pp * qq * qq)))
        by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((u2 * u2)) == (dp * pp * pp * u2 * u2)) by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((y2 * y2)) == (dp * pp * pp * y2 * y2)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (pp * pp), (dp), (pp * pp));
    assert(((dp)) * ((pp * pp)) == (dp * pp * pp)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (pp * qq), (dp), (pp * qq));
    assert(((dp)) * ((pp * qq)) == (dp * pp * qq)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (pp * qq), (dp), (pp * qq));
    assert(((dp)) * ((pp * qq)) == (dp * pp * qq)) by (nonlinear_arith);
    lemma_dist_2_3(
        1,
        (dp * pp * qq),
        (-1),
        (dp * pp * qq),
        (2 * (pp)),
        (dp * (pp * qq) + 1),
        (dp * (pp * qq) - 1 + 2 * pp),
    );
    assert((1) * ((-1)) == (-1)) by (nonlinear_arith);
    assert((1) * ((dp * pp * qq)) == (dp * pp * qq)) by (nonlinear_arith);
    assert((1) * ((2 * (pp))) == (2 * (pp))) by (nonlinear_arith);
    assert(((dp * pp * qq)) * ((-1)) == (-(dp * pp * qq))) by (nonlinear_arith);
    assert(((dp * pp * qq)) * ((dp * pp * qq)) == (dp * dp * pp * pp * qq * qq))
        by (nonlinear_arith);
    assert(((dp * pp * qq)) * ((2 * (pp))) == (2 * (dp * pp * pp * qq))) by (nonlinear_arith);
}

/// Denominator certificate for s = -1, ε = 1 (P = u1·y1, Q = u2·y2, k = dp·P·Q).
#[verifier::rlimit(30)]
proof fn lemma_id_denom_cert_mp(u1: int, y1: int, u2: int, y2: int, dp: int, pp: int, qq: int)
    ensures
        dp * (pp * pp) * (u2 * u2 - 2 * qq + y2 * y2) - (u1 * u1 - 2 * pp + y1 * y1) == dp * (pp
            * pp) * (u2 * u2 + y2 * y2 - 1 - dp * (qq * qq)) - (u1 * u1 + y1 * y1 - 1 - dp * (pp
            * pp)) + (dp * (pp * qq) - 1) * (dp * (pp * qq) + 1 - 2 * pp),
{
    lemma_dist_1_1((dp), (pp * pp), (dp), (pp * pp));
    assert(((dp)) * ((pp * pp)) == (dp * pp * pp)) by (nonlinear_arith);
    lemma_dist_1_3(
        (dp * pp * pp),
        (-(2 * (qq))),
        (u2 * u2),
        (y2 * y2),
        (dp * (pp * pp)),
        (u2 * u2 - 2 * qq + y2 * y2),
    );
    assert(((dp * pp * pp)) * ((-(2 * (qq)))) == (-(2 * (dp * pp * pp * qq)))) by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((u2 * u2)) == (dp * pp * pp * u2 * u2)) by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((y2 * y2)) == (dp * pp * pp * y2 * y2)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (pp * pp), (dp), (pp * pp));
    assert(((dp)) * ((pp * pp)) == (dp * pp * pp)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (qq * qq), (dp), (qq * qq));
    assert(((dp)) * ((qq * qq)) == (dp * qq * qq)) by (nonlinear_arith);
    lemma_dist_1_4(
        (dp * pp * pp),
        (-1),
        (-(dp * qq * qq)),
        (u2 * u2),
        (y2 * y2),
        (dp * (pp * pp)),
        (u2 * u2 + y2 * y2 - 1 - dp * (qq * qq)),
    );
    assert(((dp * pp * pp)) * ((-1)) == (-(dp * pp * pp))) by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((-(dp * qq * qq))) == (-(dp * dp * pp * pp * qq * qq)))
        by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((u2 * u2)) == (dp * pp * pp * u2 * u2)) by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((y2 * y2)) == (dp * pp * pp * y2 * y2)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (pp * pp), (dp), (pp * pp));
    assert(((dp)) * ((pp * pp)) == (dp * pp * pp)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (pp * qq), (dp), (pp * qq));
    assert(((dp)) * ((pp * qq)) == (dp * pp * qq)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (pp * qq), (dp), (pp * qq));
    assert(((dp)) * ((pp * qq)) == (dp * pp * qq)) by (nonlinear_arith);
    lemma_dist_2_3(
        (-1),
        (dp * pp * qq),
        1,
        (dp * pp * qq),
        (-(2 * (pp))),
        (dp * (pp * qq) - 1),
        (dp * (pp * qq) + 1 - 2 * pp),
    );
    assert(((-1)) * (1) == (-1)) by (nonlinear_arith);
    assert(((-1)) * ((dp * pp * qq)) == (-(dp * pp * qq))) by (nonlinear_arith);
    assert(((-1)) * ((-(2 * (pp)))) == (2 * (pp))) by (nonlinear_arith);
    assert(((dp * pp * qq)) * (1) == (dp * pp * qq)) by (nonlinear_arith);
    assert(((dp * pp * qq)) * ((dp * pp * qq)) == (dp * dp * pp * pp * qq * qq))
        by (nonlinear_arith);
    assert(((dp * pp * qq)) * ((-(2 * (pp)))) == (-(2 * (dp * pp * pp * qq)))) by (nonlinear_arith);
}

/// Denominator certificate for s = -1, ε = -1 (P = u1·y1, Q = u2·y2, k = dp·P·Q).
#[verifier::rlimit(30)]
proof fn lemma_id_denom_cert_mm(u1: int, y1: int, u2: int, y2: int, dp: int, pp: int, qq: int)
    ensures
        dp * (pp * pp) * (u2 * u2 - 2 * qq + y2 * y2) - (u1 * u1 + 2 * pp + y1 * y1) == dp * (pp
            * pp) * (u2 * u2 + y2 * y2 - 1 - dp * (qq * qq)) - (u1 * u1 + y1 * y1 - 1 - dp * (pp
            * pp)) + (dp * (pp * qq) + 1) * (dp * (pp * qq) - 1 - 2 * pp),
{
    lemma_dist_1_1((dp), (pp * pp), (dp), (pp * pp));
    assert(((dp)) * ((pp * pp)) == (dp * pp * pp)) by (nonlinear_arith);
    lemma_dist_1_3(
        (dp * pp * pp),
        (-(2 * (qq))),
        (u2 * u2),
        (y2 * y2),
        (dp * (pp * pp)),
        (u2 * u2 - 2 * qq + y2 * y2),
    );
    assert(((dp * pp * pp)) * ((-(2 * (qq)))) == (-(2 * (dp * pp * pp * qq)))) by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((u2 * u2)) == (dp * pp * pp * u2 * u2)) by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((y2 * y2)) == (dp * pp * pp * y2 * y2)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (pp * pp), (dp), (pp * pp));
    assert(((dp)) * ((pp * pp)) == (dp * pp * pp)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (qq * qq), (dp), (qq * qq));
    assert(((dp)) * ((qq * qq)) == (dp * qq * qq)) by (nonlinear_arith);
    lemma_dist_1_4(
        (dp * pp * pp),
        (-1),
        (-(dp * qq * qq)),
        (u2 * u2),
        (y2 * y2),
        (dp * (pp * pp)),
        (u2 * u2 + y2 * y2 - 1 - dp * (qq * qq)),
    );
    assert(((dp * pp * pp)) * ((-1)) == (-(dp * pp * pp))) by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((-(dp * qq * qq))) == (-(dp * dp * pp * pp * qq * qq)))
        by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((u2 * u2)) == (dp * pp * pp * u2 * u2)) by (nonlinear_arith);
    assert(((dp * pp * pp)) * ((y2 * y2)) == (dp * pp * pp * y2 * y2)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (pp * pp), (dp), (pp * pp));
    assert(((dp)) * ((pp * pp)) == (dp * pp * pp)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (pp * qq), (dp), (pp * qq));
    assert(((dp)) * ((pp * qq)) == (dp * pp * qq)) by (nonlinear_arith);
    lemma_dist_1_1((dp), (pp * qq), (dp), (pp * qq));
    assert(((dp)) * ((pp * qq)) == (dp * pp * qq)) by (nonlinear_arith);
    lemma_dist_2_3(
        1,
        (dp * pp * qq),
        (-1),
        (dp * pp * qq),
        (-(2 * (pp))),
        (dp * (pp * qq) + 1),
        (dp * (pp * qq) - 1 - 2 * pp),
    );
    assert((1) * ((-1)) == (-1)) by (nonlinear_arith);
    assert((1) * ((dp * pp * qq)) == (dp * pp * qq)) by (nonlinear_arith);
    assert((1) * ((-(2 * (pp)))) == (-(2 * (pp)))) by (nonlinear_arith);
    assert(((dp * pp * qq)) * ((-1)) == (-(dp * pp * qq))) by (nonlinear_arith);
    assert(((dp * pp * qq)) * ((dp * pp * qq)) == (dp * dp * pp * pp * qq * qq))
        by (nonlinear_arith);
    assert(((dp * pp * qq)) * ((-(2 * (pp)))) == (-(2 * (dp * pp * pp * qq)))) by (nonlinear_arith);
}

/// (p0 + ... + p0)·(q0 + ... + q0) expanded.
proof fn lemma_dist_1_1(p0: int, q0: int, pp: int, qq: int)
    requires
        pp == p0,
        qq == q0,
    ensures
        pp * qq == p0 * q0,
{
    lemma_mul_eq(pp, p0, qq, q0);
}

/// (p0 + ... + p0)·(q0 + ... + q1) expanded.
proof fn lemma_dist_1_2(p0: int, q0: int, q1: int, pp: int, qq: int)
    requires
        pp == p0,
        qq == q0 + q1,
    ensures
        pp * qq == p0 * q0 + p0 * q1,
{
    lemma_mul_eq(pp, p0, qq, (q0 + q1));
    lemma_dist_l(p0, q0, q1);
}

/// (p0 + ... + p0)·(q0 + ... + q2) expanded.
proof fn lemma_dist_1_3(p0: int, q0: int, q1: int, q2: int, pp: int, qq: int)
    requires
        pp == p0,
        qq == q0 + q1 + q2,
    ensures
        pp * qq == p0 * q0 + p0 * q1 + p0 * q2,
{
    lemma_mul_eq(pp, p0, qq, ((q0 + q1) + q2));
    lemma_dist_l(p0, (q0 + q1), q2);
    lemma_dist_l(p0, q0, q1);
}

/// (p0 + ... + p0)·(q0 + ... + q3) expanded.
proof fn lemma_dist_1_4(p0: int, q0: int, q1: int, q2: int, q3: int, pp: int, qq: int)
    requires
        pp == p0,
        qq == q0 + q1 + q2 + q3,
    ensures
        pp * qq == p0 * q0 + p0 * q1 + p0 * q2 + p0 * q3,
{
    lemma_mul_eq(pp, p0, qq, (((q0 + q1) + q2) + q3));
    lemma_dist_l(p0, ((q0 + q1) + q2), q3);
    lemma_dist_l(p0, (q0 + q1), q2);
    lemma_dist_l(p0, q0, q1);
}

/// (p0 + ... + p1)·(q0 + ... + q0) expanded.
proof fn lemma_dist_2_1(p0: int, p1: int, q0: int, pp: int, qq: int)
    requires
        pp == p0 + p1,
        qq == q0,
    ensures
        pp * qq == p0 * q0 + p1 * q0,
{
    lemma_mul_eq(pp, (p0 + p1), qq, q0);
    lemma_dist_r(p0, p1, q0);
}

/// (p0 + ... + p1)·(q0 + ... + q1) expanded.
proof fn lemma_dist_2_2(p0: int, p1: int, q0: int, q1: int, pp: int, qq: int)
    requires
        pp == p0 + p1,
        qq == q0 + q1,
    ensures
        pp * qq == p0 * q0 + p0 * q1 + p1 * q0 + p1 * q1,
{
    lemma_mul_eq(pp, (p0 + p1), qq, (q0 + q1));
    lemma_dist_r(p0, p1, (q0 + q1));
    lemma_dist_l(p0, q0, q1);
    lemma_dist_l(p1, q0, q1);
}

/// (p0 + ... + p1)·(q0 + ... + q2) expanded.
proof fn lemma_dist_2_3(p0: int, p1: int, q0: int, q1: int, q2: int, pp: int, qq: int)
    requires
        pp == p0 + p1,
        qq == q0 + q1 + q2,
    ensures
        pp * qq == p0 * q0 + p0 * q1 + p0 * q2 + p1 * q0 + p1 * q1 + p1 * q2,
{
    lemma_mul_eq(pp, (p0 + p1), qq, ((q0 + q1) + q2));
    lemma_dist_r(p0, p1, ((q0 + q1) + q2));
    lemma_dist_l(p0, (q0 + q1), q2);
    lemma_dist_l(p0, q0, q1);
    lemma_dist_l(p1, (q0 + q1), q2);
    lemma_dist_l(p1, q0, q1);
}

/// (p0 + ... + p1)·(q0 + ... + q3) expanded.
proof fn lemma_dist_2_4(p0: int, p1: int, q0: int, q1: int, q2: int, q3: int, pp: int, qq: int)
    requires
        pp == p0 + p1,
        qq == q0 + q1 + q2 + q3,
    ensures
        pp * qq == p0 * q0 + p0 * q1 + p0 * q2 + p0 * q3 + p1 * q0 + p1 * q1 + p1 * q2 + p1 * q3,
{
    lemma_mul_eq(pp, (p0 + p1), qq, (((q0 + q1) + q2) + q3));
    lemma_dist_r(p0, p1, (((q0 + q1) + q2) + q3));
    lemma_dist_l(p0, ((q0 + q1) + q2), q3);
    lemma_dist_l(p0, (q0 + q1), q2);
    lemma_dist_l(p0, q0, q1);
    lemma_dist_l(p1, ((q0 + q1) + q2), q3);
    lemma_dist_l(p1, (q0 + q1), q2);
    lemma_dist_l(p1, q0, q1);
}

/// (p0 + ... + p2)·(q0 + ... + q0) expanded.
proof fn lemma_dist_3_1(p0: int, p1: int, p2: int, q0: int, pp: int, qq: int)
    requires
        pp == p0 + p1 + p2,
        qq == q0,
    ensures
        pp * qq == p0 * q0 + p1 * q0 + p2 * q0,
{
    lemma_mul_eq(pp, ((p0 + p1) + p2), qq, q0);
    lemma_dist_r((p0 + p1), p2, q0);
    lemma_dist_r(p0, p1, q0);
}

/// (p0 + ... + p2)·(q0 + ... + q2) expanded.
proof fn lemma_dist_3_3(p0: int, p1: int, p2: int, q0: int, q1: int, q2: int, pp: int, qq: int)
    requires
        pp == p0 + p1 + p2,
        qq == q0 + q1 + q2,
    ensures
        pp * qq == p0 * q0 + p0 * q1 + p0 * q2 + p1 * q0 + p1 * q1 + p1 * q2 + p2 * q0 + p2 * q1
            + p2 * q2,
{
    lemma_mul_eq(pp, ((p0 + p1) + p2), qq, ((q0 + q1) + q2));
    lemma_dist_r((p0 + p1), p2, ((q0 + q1) + q2));
    lemma_dist_r(p0, p1, ((q0 + q1) + q2));
    lemma_dist_l(p0, (q0 + q1), q2);
    lemma_dist_l(p0, q0, q1);
    lemma_dist_l(p1, (q0 + q1), q2);
    lemma_dist_l(p1, q0, q1);
    lemma_dist_l(p2, (q0 + q1), q2);
    lemma_dist_l(p2, q0, q1);
}

/// (p0 + ... + p4)·(q0 + ... + q2) expanded.
proof fn lemma_dist_5_3(
    p0: int,
    p1: int,
    p2: int,
    p3: int,
    p4: int,
    q0: int,
    q1: int,
    q2: int,
    pp: int,
    qq: int,
)
    requires
        pp == p0 + p1 + p2 + p3 + p4,
        qq == q0 + q1 + q2,
    ensures
        pp * qq == p0 * q0 + p0 * q1 + p0 * q2 + p1 * q0 + p1 * q1 + p1 * q2 + p2 * q0 + p2 * q1
            + p2 * q2 + p3 * q0 + p3 * q1 + p3 * q2 + p4 * q0 + p4 * q1 + p4 * q2,
{
    lemma_mul_eq(pp, ((((p0 + p1) + p2) + p3) + p4), qq, ((q0 + q1) + q2));
    lemma_dist_r((((p0 + p1) + p2) + p3), p4, ((q0 + q1) + q2));
    lemma_dist_r(((p0 + p1) + p2), p3, ((q0 + q1) + q2));
    lemma_dist_r((p0 + p1), p2, ((q0 + q1) + q2));
    lemma_dist_r(p0, p1, ((q0 + q1) + q2));
    lemma_dist_l(p0, (q0 + q1), q2);
    lemma_dist_l(p0, q0, q1);
    lemma_dist_l(p1, (q0 + q1), q2);
    lemma_dist_l(p1, q0, q1);
    lemma_dist_l(p2, (q0 + q1), q2);
    lemma_dist_l(p2, q0, q1);
    lemma_dist_l(p3, (q0 + q1), q2);
    lemma_dist_l(p3, q0, q1);
    lemma_dist_l(p4, (q0 + q1), q2);
    lemma_dist_l(p4, q0, q1);
}

/// Clearing the denominators of the sum: with a = 1 + T, b = 1 − T,
/// r = x3·a and q = y3·b, (a·b)²·curve_poly(x3, y3) = a²q² − b²r² − (ab)² − d·r²q².
proof fn lemma_id_clear_denominators(x3: int, y3: int, a: int, b: int, d: int)
    ensures
        ({
            let r = x3 * a;
            let q = y3 * b;
            (a * b) * (a * b) * (y3 * y3 - x3 * x3 - 1 - d * (x3 * x3 * (y3 * y3))) == a * a * (q
                * q) - b * b * (r * r) - (a * b) * (a * b) - d * (r * r * (q * q))
        }),
{
    let r = x3 * a;
    let q = y3 * b;
    let n = (a * b) * (a * b);
    assert(n * (y3 * y3) == a * a * (q * q)) by (nonlinear_arith)
        requires
            n == (a * b) * (a * b),
            q == y3 * b,
    ;
    assert(n * (x3 * x3) == b * b * (r * r)) by (nonlinear_arith)
        requires
            n == (a * b) * (a * b),
            r == x3 * a,
    ;
    assert(n * (d * (x3 * x3 * (y3 * y3))) == d * (r * r * (q * q))) by (nonlinear_arith)
        requires
            n == (a * b) * (a * b),
            r == x3 * a,
            q == y3 * b,
    ;
    assert(n * (y3 * y3 - x3 * x3 - 1 - d * (x3 * x3 * (y3 * y3))) == n * (y3 * y3) - n * (x3 * x3)
        - n - n * (d * (x3 * x3 * (y3 * y3)))) by (nonlinear_arith);
}

// =============================================================================
// Glue helpers
// =============================================================================
/// (a + b)·c = a·c + b·c.
proof fn lemma_dist_r(a: int, b: int, c: int)
    ensures
        (a + b) * c == a * c + b * c,
{
    assert((a + b) * c == a * c + b * c) by (nonlinear_arith);
}

/// a·(b + c) = a·b + a·c.
proof fn lemma_dist_l(a: int, b: int, c: int)
    ensures
        a * (b + c) == a * b + a * c,
{
    assert(a * (b + c) == a * b + a * c) by (nonlinear_arith);
}

/// Equal factors give equal products.
proof fn lemma_mul_eq(a: int, b: int, c: int, e: int)
    requires
        a == b,
        c == e,
    ensures
        a * c == b * e,
{
}

/// A zero factor gives a zero product.
proof fn lemma_mul_zero_factor(z: int, k: int)
    requires
        z == 0,
    ensures
        z * k == 0,
        k * z == 0,
{
    assert(z * k == 0 && k * z == 0) by (nonlinear_arith)
        requires
            z == 0,
    ;
}

/// (−1)·t = −t, and (−1)·(−t) = t.
proof fn lemma_neg_one_mul(t: int)
    ensures
        (-1) * t == -t,
        (-1) * (-t) == t,
{
    assert((-1) * t == -t && (-1) * (-t) == t) by (nonlinear_arith);
}

/// cong(·, 0) moves across an equality.
proof fn lemma_cong_eq_zero(a: int, b: int)
    requires
        a == b,
        cong(b, 0),
    ensures
        cong(a, 0),
{
}

// =============================================================================
// Closure
// =============================================================================
/// T² = A·B, with T = d·(x1x2)·(y1y2), A = d·x1²y1² and B = d·x2²y2².
proof fn lemma_add_t_square(x1: int, y1: int, x2: int, y2: int, d: int)
    ensures
        (d * ((x1 * x2) * (y1 * y2))) * (d * ((x1 * x2) * (y1 * y2))) == (d * (x1 * x1 * (y1 * y1)))
            * (d * (x2 * x2 * (y2 * y2))),
{
    let q = (x1 * x2) * (y1 * y2);
    let r1 = x1 * x1 * (y1 * y1);
    let r2 = x2 * x2 * (y2 * y2);
    lemma_sq_mul(d, q);
    lemma_sq_mul(x1 * x2, y1 * y2);
    lemma_sq_mul(x1, x2);
    lemma_sq_mul(y1, y2);
    lemma_mul_eq(
        (x1 * x2) * (x1 * x2),
        (x1 * x1) * (x2 * x2),
        (y1 * y2) * (y1 * y2),
        (y1 * y1) * (y2 * y2),
    );
    lemma_id_swap4(x1 * x1, x2 * x2, y1 * y1, y2 * y2);
    lemma_id_swap4(d, r1, d, r2);
    lemma_mul_eq(d * d, d * d, q * q, r1 * r2);
}

/// d·Nx²·Ny² = A·V² + B·U² + 2·T·(Nx² + Ny²).
proof fn lemma_add_d_num_square(x1: int, y1: int, x2: int, y2: int, d: int)
    ensures
        ({
            let nx = x1 * y2 + y1 * x2;
            let ny = y1 * y2 + x1 * x2;
            let u = y1 * y1 - x1 * x1;
            let v = y2 * y2 - x2 * x2;
            d * (nx * nx * (ny * ny)) == (d * (x1 * x1 * (y1 * y1))) * (v * v) + (d * (x2 * x2 * (y2
                * y2))) * (u * u) + 2 * (d * ((x1 * x2) * (y1 * y2))) * (nx * nx + ny * ny)
        }),
{
    let nx = x1 * y2 + y1 * x2;
    let ny = y1 * y2 + x1 * x2;
    let u = y1 * y1 - x1 * x1;
    let v = y2 * y2 - x2 * x2;
    let p1 = x1 * y1;
    let p2 = x2 * y2;
    let s1 = x1 * x1 + y1 * y1;
    let s2 = x2 * x2 + y2 * y2;
    let m = p1 * s2 + p2 * s1;
    // d·Nx²·Ny² = d·(Nx·Ny)² = d·m².
    lemma_sq_mul(nx, ny);
    lemma_id_add_num_prod(x1, y1, x2, y2);
    lemma_mul_eq(nx * ny, m, nx * ny, m);
    lemma_mul_eq(d, d, nx * nx * (ny * ny), m * m);
    lemma_id_add_d_prod(d, p1, p2, s1, s2, u, v);
    // The two terms that vanish.
    lemma_id_sum_sq_rel(x1, y1);
    lemma_id_sum_sq_rel(x2, y2);
    lemma_mul_zero_factor(s2 * s2 - v * v - 4 * (p2 * p2), d * (p1 * p1));
    lemma_mul_zero_factor(s1 * s1 - u * u - 4 * (p1 * p1), d * (p2 * p2));
    // d·p1² = A and d·p2² = B.
    lemma_sq_mul(x1, y1);
    lemma_sq_mul(x2, y2);
    lemma_mul_eq(d, d, p1 * p1, x1 * x1 * (y1 * y1));
    lemma_mul_eq(d, d, p2 * p2, x2 * x2 * (y2 * y2));
    lemma_mul_eq(d * (p1 * p1), d * (x1 * x1 * (y1 * y1)), v * v, v * v);
    lemma_mul_eq(d * (p2 * p2), d * (x2 * x2 * (y2 * y2)), u * u, u * u);
    // d·p1·p2 = T and s1·s2 + 4·p1·p2 = Nx² + Ny².
    lemma_id_swap4(x1, y1, x2, y2);
    lemma_mul_eq(d, d, p1 * p2, (x1 * x2) * (y1 * y2));
    lemma_id_add_num_sum(x1, y1, x2, y2);
    lemma_mul_eq(
        2 * (d * (p1 * p2)),
        2 * (d * ((x1 * x2) * (y1 * y2))),
        s1 * s2 + 4 * (p1 * p2),
        nx * nx + ny * ny,
    );
}

/// Closure: if both points are on the curve and 1 ± t ≢ 0, the sum is on the curve.
pub proof fn lemma_edwards_add_closure_cong(x1: nat, y1: nat, x2: nat, y2: nat)
    requires
        is_on_edwards_curve(x1, y1),
        is_on_edwards_curve(x2, y2),
        !cong(1 + d_int() * (((x1 as int) * (x2 as int)) * ((y1 as int) * (y2 as int))), 0),
        !cong(1 - d_int() * (((x1 as int) * (x2 as int)) * ((y1 as int) * (y2 as int))), 0),
    ensures
        is_on_edwards_curve(edwards_add(x1, y1, x2, y2).0, edwards_add(x1, y1, x2, y2).1),
{
    lemma_cong_p_facts();
    let (X1, Y1, X2, Y2) = (x1 as int, y1 as int, x2 as int, y2 as int);
    let D = d_int();
    let T = D * ((X1 * X2) * (Y1 * Y2));
    let nx = X1 * Y2 + Y1 * X2;
    let ny = Y1 * Y2 + X1 * X2;
    let u = Y1 * Y1 - X1 * X1;
    let v = Y2 * Y2 - X2 * X2;
    let a = D * (X1 * X1 * (Y1 * Y1));
    let b = D * (X2 * X2 * (Y2 * Y2));
    lemma_edwards_add_cong(x1, y1, x2, y2);
    let (x3, y3) = edwards_add(x1, y1, x2, y2);
    let (X3, Y3) = (x3 as int, y3 as int);
    let r = X3 * (1 + T);
    let q = Y3 * (1 - T);
    assert(cong(r, nx));
    assert(cong(q, ny));

    // N·curve_poly(x3, y3) = fr, and fr ≡ fn.
    let n = ((1 + T) * (1 - T)) * ((1 + T) * (1 - T));
    let cp3 = curve_poly(X3, Y3);
    lemma_id_clear_denominators(X3, Y3, 1 + T, 1 - T, D);
    let fr = (1 + T) * (1 + T) * (q * q) - (1 - T) * (1 - T) * (r * r) - ((1 + T) * (1 - T)) * ((1
        + T) * (1 - T)) - D * (r * r * (q * q));
    assert(n * cp3 == fr);
    let fnn = (1 + T) * (1 + T) * (ny * ny) - (1 - T) * (1 - T) * (nx * nx) - ((1 + T) * (1 - T))
        * ((1 + T) * (1 - T)) - D * (nx * nx * (ny * ny));
    lemma_cong_mul(q, q, ny, ny);
    lemma_cong_mul(r, r, nx, nx);
    lemma_cong_refl((1 + T) * (1 + T));
    lemma_cong_refl((1 - T) * (1 - T));
    lemma_cong_refl(((1 + T) * (1 - T)) * ((1 + T) * (1 - T)));
    lemma_cong_refl(D);
    lemma_cong_mul((1 + T) * (1 + T), q * q, (1 + T) * (1 + T), ny * ny);
    lemma_cong_mul((1 - T) * (1 - T), r * r, (1 - T) * (1 - T), nx * nx);
    lemma_cong_mul(r * r, q * q, nx * nx, ny * ny);
    lemma_cong_mul(D, r * r * (q * q), D, nx * nx * (ny * ny));
    lemma_cong_sub(
        (1 + T) * (1 + T) * (q * q),
        (1 - T) * (1 - T) * (r * r),
        (1 + T) * (1 + T) * (ny * ny),
        (1 - T) * (1 - T) * (nx * nx),
    );
    lemma_cong_sub(
        (1 + T) * (1 + T) * (q * q) - (1 - T) * (1 - T) * (r * r),
        ((1 + T) * (1 - T)) * ((1 + T) * (1 - T)),
        (1 + T) * (1 + T) * (ny * ny) - (1 - T) * (1 - T) * (nx * nx),
        ((1 + T) * (1 - T)) * ((1 + T) * (1 - T)),
    );
    lemma_cong_sub(
        (1 + T) * (1 + T) * (q * q) - (1 - T) * (1 - T) * (r * r) - ((1 + T) * (1 - T)) * ((1 + T)
            * (1 - T)),
        D * (r * r * (q * q)),
        (1 + T) * (1 + T) * (ny * ny) - (1 - T) * (1 - T) * (nx * nx) - ((1 + T) * (1 - T)) * ((1
            + T) * (1 - T)),
        D * (nx * nx * (ny * ny)),
    );
    assert(cong(fr, fnn));

    // fnn = h, the left side of the certificate.
    lemma_id_add_cleared(T, nx * nx, ny * ny);
    lemma_id_add_num_diff(X1, Y1, X2, Y2);
    lemma_mul_eq(1 + T * T, 1 + T * T, ny * ny - nx * nx, u * v);
    lemma_add_d_num_square(X1, Y1, X2, Y2, D);
    let h = (1 + T * T) * (u * v) - a * (v * v) - b * (u * u) - (1 - T * T) * (1 - T * T);
    assert(fnn == h);

    // h = q1·c1 + q2·c2 + (T² − A·B)·K, and T² = A·B.
    lemma_id_add_certificate(u, v, a, b, T);
    lemma_add_t_square(X1, Y1, X2, Y2, D);
    let kk = u * v + 2 - T * T - a * b;
    lemma_mul_zero_factor(T * T - a * b, kk);
    let q1 = (1 + a * b) * v - b * (u + 1 + a);
    let q2 = 1 - a * v + a * a * b;
    lemma_curve_cong(x1, y1);
    lemma_curve_cong(x2, y2);
    lemma_cong_eq_zero(u - 1 - a, curve_poly(X1, Y1));
    lemma_cong_eq_zero(v - 1 - b, curve_poly(X2, Y2));
    lemma_cong_combo2(q1, u - 1 - a, q2, v - 1 - b);
    lemma_cong_eq_zero(h, q1 * (u - 1 - a) + q2 * (v - 1 - b));
    lemma_cong_eq_zero(fnn, h);
    assert(cong(fr, 0));
    lemma_cong_eq_zero(n * cp3, fr);

    // N ≢ 0, so curve_poly(x3, y3) ≡ 0.
    lemma_cong_mul_nonzero(1 + T, 1 - T);
    lemma_cong_mul_nonzero((1 + T) * (1 - T), (1 + T) * (1 - T));
    lemma_cong_mul_zero(n, cp3);
    lemma_curve_cong(x3, y3);
}

// =============================================================================
// Completeness: nonzero denominators
// =============================================================================
/// With i² ≡ −1 and u = i·x: u² ≡ −x², and the rotated curve polynomial
/// u² + y² − 1 − d'·u²·y², with d' = −d, is ≡ curve_poly(x, y).
proof fn lemma_rot_curve_cong(i: int, x: int, y: int, d: int)
    requires
        cong(i * i, -1),
    ensures
        cong((i * x) * (i * x), -(x * x)),
        cong(
            (i * x) * (i * x) + y * y - 1 - (-d) * ((i * x) * (i * x) * (y * y)),
            y * y - x * x - 1 - d * (x * x * (y * y)),
        ),
{
    let u = i * x;
    lemma_sq_mul(i, x);
    lemma_cong_refl(x * x);
    lemma_cong_mul(i * i, x * x, -1, x * x);
    lemma_neg_one_mul(x * x);
    assert(cong(u * u, -(x * x)));
    lemma_cong_refl(y * y);
    lemma_cong_mul(u * u, y * y, -(x * x), y * y);
    lemma_cong_refl(-d);
    lemma_cong_mul(-d, u * u * (y * y), -d, (-(x * x)) * (y * y));
    lemma_id_neg_neg(d, x * x, y * y);
    lemma_cong_add(u * u, y * y, -(x * x), y * y);
    lemma_cong_refl(1);
    lemma_cong_sub(u * u + y * y, 1, -(x * x) + y * y, 1);
    lemma_cong_sub(
        u * u + y * y - 1,
        (-d) * (u * u * (y * y)),
        -(x * x) + y * y - 1,
        (-d) * ((-(x * x)) * (y * y)),
    );
}

/// With i² ≡ −1, u_j = i·x_j and d' = −d: d'·(u1·y1)·(u2·y2) ≡ d·(x1x2)·(y1y2).
proof fn lemma_rot_t_cong(i: int, x1: int, y1: int, x2: int, y2: int, d: int)
    requires
        cong(i * i, -1),
    ensures
        cong((-d) * (((i * x1) * y1) * ((i * x2) * y2)), d * ((x1 * x2) * (y1 * y2))),
{
    lemma_id_swap4(i * x1, y1, i * x2, y2);
    lemma_id_swap4(i, x1, i, x2);
    lemma_mul_eq((i * x1) * (i * x2), (i * i) * (x1 * x2), y1 * y2, y1 * y2);
    lemma_cong_refl(x1 * x2);
    lemma_cong_refl(y1 * y2);
    lemma_cong_refl(-d);
    lemma_cong_mul(i * i, x1 * x2, -1, x1 * x2);
    lemma_neg_one_mul(x1 * x2);
    lemma_cong_mul((i * i) * (x1 * x2), y1 * y2, -(x1 * x2), y1 * y2);
    lemma_cong_mul(-d, ((i * i) * (x1 * x2)) * (y1 * y2), -d, (-(x1 * x2)) * (y1 * y2));
    lemma_id_neg_neg(d, x1 * x2, y1 * y2);
}

/// cong(0, e) is false for e = ±1.
proof fn lemma_cong_zero_pm_one(e: int)
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

/// If d'·B² ≡ N² with B ≢ 0 and d' ≡ −d, then d is a square. This contradicts
/// `lemma_edwards_d_not_square`.
proof fn lemma_neg_d_square_absurd(bb: int, nn: int)
    requires
        !cong(bb, 0),
        cong((-d_int()) * (bb * bb), nn * nn),
    ensures
        false,
{
    lemma_cong_p_facts();
    lemma_sqrt_m1_cong();
    let D = d_int();
    let pp = p() as int;
    let i = sqrt_m1();
    let I = i as int;
    // Residues of B and N.
    lemma_mod_bound(bb, pp);
    lemma_mod_twice(bb, pp);
    lemma_mod_bound(nn, pp);
    lemma_mod_twice(nn, pp);
    let b = (bb % pp) as nat;
    let a = (nn % pp) as nat;
    assert(cong(b as int, bb));
    assert(cong(a as int, nn));
    assert(!cong(b as int, 0));
    lemma_cong_inv(b);
    let bi = field_inv(b);
    let BI = bi as int;
    // B·BI ≡ 1.
    lemma_cong_refl(BI);
    assert((bi * b) as int == BI * (b as int));
    assert(cong(BI * (b as int), 1));
    lemma_cong_mul(BI, b as int, BI, bb);
    assert(cong(BI * bb, 1));
    assert(cong(bb * BI, 1));
    // w = N·BI, w² ≡ d'·(B·BI)² ≡ d'.
    let w = field_mul(a, bi);
    lemma_cong_fmul(a, bi, nn, BI);
    let W = w as int;
    lemma_cong_mul(W, W, nn * BI, nn * BI);
    lemma_sq_mul(nn, BI);
    lemma_cong_refl(BI * BI);
    lemma_cong_mul(nn * nn, BI * BI, (-D) * (bb * bb), BI * BI);
    lemma_mul_assoc4(-D, bb * bb, BI * BI);
    lemma_sq_mul(bb, BI);
    lemma_mul_eq(-D, -D, (bb * bb) * (BI * BI), (bb * BI) * (bb * BI));
    lemma_cong_mul(bb * BI, bb * BI, 1, 1);
    lemma_cong_refl(-D);
    lemma_cong_mul(-D, (bb * BI) * (bb * BI), -D, 1);
    assert(cong(W * W, -D));
    // v = i·w, v² ≡ i²·w² ≡ (−1)·(−d) = d.
    let v = field_mul(i, w);
    lemma_cong_refl(I);
    lemma_cong_refl(W);
    lemma_cong_fmul(i, w, I, W);
    let V = v as int;
    lemma_cong_mul(V, V, I * W, I * W);
    lemma_sq_mul(I, W);
    lemma_cong_mul(I * I, W * W, -1, -D);
    lemma_neg_one_mul(D);
    assert(cong(V * V, D));
    lemma_cong_fmul(v, v, V, V);
    // field_mul(v, v) = d, so d is a square.
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    lemma_mod_bound((v * v) as int, pp);
    lemma_mod_bound(u64_5_as_nat(EDWARDS_D.limbs) as int, pp);
    lemma_cong_canonical_eq(field_mul(v, v), d);
    lemma_small_mod(d, p());
    assert(field_mul(v, v) == field_canonical(d));
    lemma_edwards_d_not_square();
    assert(false);
}

/// Denominator case s = 1, ε = 1: d'·(u1y1)²·(u2 + y2)² ≡ (u1 + y1)².
proof fn lemma_denom_case_pp(u1: int, y1: int, u2: int, y2: int, dp: int)
    requires
        cong(u1 * u1 + y1 * y1 - 1 - dp * ((u1 * y1) * (u1 * y1)), 0),
        cong(u2 * u2 + y2 * y2 - 1 - dp * ((u2 * y2) * (u2 * y2)), 0),
        cong(dp * ((u1 * y1) * (u2 * y2)) - 1, 0),
    ensures
        cong(dp * ((u1 * y1) * (u1 * y1)) * ((u2 + y2) * (u2 + y2)) - (u1 + y1) * (u1 + y1), 0),
{
    let pp = u1 * y1;
    let qq = u2 * y2;
    let c1 = u1 * u1 + y1 * y1 - 1 - dp * (pp * pp);
    let c2 = u2 * u2 + y2 * y2 - 1 - dp * (qq * qq);
    let h3 = dp * (pp * qq) - 1;
    let q3 = dp * (pp * qq) + 1 + 2 * pp;
    lemma_id_sq_plus(u2, y2);
    lemma_id_sq_plus(u1, y1);
    lemma_id_denom_cert_pp(u1, y1, u2, y2, dp, pp, qq);
    lemma_mul_eq(dp * (pp * pp), dp * (pp * pp), (u2 + y2) * (u2 + y2), u2 * u2 + 2 * qq + y2 * y2);
    lemma_cong_combo3(dp * (pp * pp), c2, -1, c1, q3, h3);
    lemma_neg_one_mul(c1);
    lemma_cong_eq_zero(
        dp * (pp * pp) * ((u2 + y2) * (u2 + y2)) - (u1 + y1) * (u1 + y1),
        dp * (pp * pp) * c2 + (-1) * c1 + q3 * h3,
    );
}

/// Denominator case s = 1, ε = -1: d'·(u1y1)²·(u2 + y2)² ≡ (u1 − y1)².
proof fn lemma_denom_case_pm(u1: int, y1: int, u2: int, y2: int, dp: int)
    requires
        cong(u1 * u1 + y1 * y1 - 1 - dp * ((u1 * y1) * (u1 * y1)), 0),
        cong(u2 * u2 + y2 * y2 - 1 - dp * ((u2 * y2) * (u2 * y2)), 0),
        cong(dp * ((u1 * y1) * (u2 * y2)) + 1, 0),
    ensures
        cong(dp * ((u1 * y1) * (u1 * y1)) * ((u2 + y2) * (u2 + y2)) - (u1 - y1) * (u1 - y1), 0),
{
    let pp = u1 * y1;
    let qq = u2 * y2;
    let c1 = u1 * u1 + y1 * y1 - 1 - dp * (pp * pp);
    let c2 = u2 * u2 + y2 * y2 - 1 - dp * (qq * qq);
    let h3 = dp * (pp * qq) + 1;
    let q3 = dp * (pp * qq) - 1 + 2 * pp;
    lemma_id_sq_plus(u2, y2);
    lemma_id_sq_minus(u1, y1);
    lemma_id_denom_cert_pm(u1, y1, u2, y2, dp, pp, qq);
    lemma_mul_eq(dp * (pp * pp), dp * (pp * pp), (u2 + y2) * (u2 + y2), u2 * u2 + 2 * qq + y2 * y2);
    lemma_cong_combo3(dp * (pp * pp), c2, -1, c1, q3, h3);
    lemma_neg_one_mul(c1);
    lemma_cong_eq_zero(
        dp * (pp * pp) * ((u2 + y2) * (u2 + y2)) - (u1 - y1) * (u1 - y1),
        dp * (pp * pp) * c2 + (-1) * c1 + q3 * h3,
    );
}

/// Denominator case s = -1, ε = 1: d'·(u1y1)²·(u2 − y2)² ≡ (u1 − y1)².
proof fn lemma_denom_case_mp(u1: int, y1: int, u2: int, y2: int, dp: int)
    requires
        cong(u1 * u1 + y1 * y1 - 1 - dp * ((u1 * y1) * (u1 * y1)), 0),
        cong(u2 * u2 + y2 * y2 - 1 - dp * ((u2 * y2) * (u2 * y2)), 0),
        cong(dp * ((u1 * y1) * (u2 * y2)) - 1, 0),
    ensures
        cong(dp * ((u1 * y1) * (u1 * y1)) * ((u2 - y2) * (u2 - y2)) - (u1 - y1) * (u1 - y1), 0),
{
    let pp = u1 * y1;
    let qq = u2 * y2;
    let c1 = u1 * u1 + y1 * y1 - 1 - dp * (pp * pp);
    let c2 = u2 * u2 + y2 * y2 - 1 - dp * (qq * qq);
    let h3 = dp * (pp * qq) - 1;
    let q3 = dp * (pp * qq) + 1 - 2 * pp;
    lemma_id_sq_minus(u2, y2);
    lemma_id_sq_minus(u1, y1);
    lemma_id_denom_cert_mp(u1, y1, u2, y2, dp, pp, qq);
    lemma_mul_eq(dp * (pp * pp), dp * (pp * pp), (u2 - y2) * (u2 - y2), u2 * u2 - 2 * qq + y2 * y2);
    lemma_cong_combo3(dp * (pp * pp), c2, -1, c1, q3, h3);
    lemma_neg_one_mul(c1);
    lemma_cong_eq_zero(
        dp * (pp * pp) * ((u2 - y2) * (u2 - y2)) - (u1 - y1) * (u1 - y1),
        dp * (pp * pp) * c2 + (-1) * c1 + q3 * h3,
    );
}

/// Denominator case s = -1, ε = -1: d'·(u1y1)²·(u2 − y2)² ≡ (u1 + y1)².
proof fn lemma_denom_case_mm(u1: int, y1: int, u2: int, y2: int, dp: int)
    requires
        cong(u1 * u1 + y1 * y1 - 1 - dp * ((u1 * y1) * (u1 * y1)), 0),
        cong(u2 * u2 + y2 * y2 - 1 - dp * ((u2 * y2) * (u2 * y2)), 0),
        cong(dp * ((u1 * y1) * (u2 * y2)) + 1, 0),
    ensures
        cong(dp * ((u1 * y1) * (u1 * y1)) * ((u2 - y2) * (u2 - y2)) - (u1 + y1) * (u1 + y1), 0),
{
    let pp = u1 * y1;
    let qq = u2 * y2;
    let c1 = u1 * u1 + y1 * y1 - 1 - dp * (pp * pp);
    let c2 = u2 * u2 + y2 * y2 - 1 - dp * (qq * qq);
    let h3 = dp * (pp * qq) + 1;
    let q3 = dp * (pp * qq) - 1 - 2 * pp;
    lemma_id_sq_minus(u2, y2);
    lemma_id_sq_plus(u1, y1);
    lemma_id_denom_cert_mm(u1, y1, u2, y2, dp, pp, qq);
    lemma_mul_eq(dp * (pp * pp), dp * (pp * pp), (u2 - y2) * (u2 - y2), u2 * u2 - 2 * qq + y2 * y2);
    lemma_cong_combo3(dp * (pp * pp), c2, -1, c1, q3, h3);
    lemma_neg_one_mul(c1);
    lemma_cong_eq_zero(
        dp * (pp * pp) * ((u2 - y2) * (u2 - y2)) - (u1 + y1) * (u1 + y1),
        dp * (pp * pp) * c2 + (-1) * c1 + q3 * h3,
    );
}

/// For points on the curve, d·(x1x2)·(y1y2) is not ≡ e, for e = ±1.
proof fn lemma_add_t_not_pm_one(x1: nat, y1: nat, x2: nat, y2: nat, e: int)
    requires
        is_on_edwards_curve(x1, y1),
        is_on_edwards_curve(x2, y2),
        e == 1 || e == -1,
    ensures
        !cong(d_int() * (((x1 as int) * (x2 as int)) * ((y1 as int) * (y2 as int))), e),
{
    let (X1, Y1, X2, Y2) = (x1 as int, y1 as int, x2 as int, y2 as int);
    let D = d_int();
    let T = D * ((X1 * X2) * (Y1 * Y2));
    if cong(T, e) {
        lemma_cong_p_facts();
        lemma_sqrt_m1_cong();
        let I = sqrt_m1() as int;
        let dp = -D;
        let u1 = I * X1;
        let u2 = I * X2;
        let pp = u1 * Y1;
        let qq = u2 * Y2;
        let k = dp * (pp * qq);
        // k ≡ T ≡ e.
        lemma_rot_t_cong(I, X1, Y1, X2, Y2, D);
        assert(cong(k, e));
        lemma_cong_diff_zero(k, e);
        // The rotated curve polynomials are ≡ 0.
        lemma_curve_cong(x1, y1);
        lemma_curve_cong(x2, y2);
        lemma_rot_curve_cong(I, X1, Y1, D);
        lemma_rot_curve_cong(I, X2, Y2, D);
        lemma_sq_mul(u1, Y1);
        lemma_sq_mul(u2, Y2);
        lemma_mul_eq(dp, dp, pp * pp, u1 * u1 * (Y1 * Y1));
        lemma_mul_eq(dp, dp, qq * qq, u2 * u2 * (Y2 * Y2));
        let c1 = u1 * u1 + Y1 * Y1 - 1 - dp * (pp * pp);
        let c2 = u2 * u2 + Y2 * Y2 - 1 - dp * (qq * qq);
        assert(cong(c1, 0));
        assert(cong(c2, 0));
        // u1, y1 ≢ 0, else k ≡ 0.
        lemma_cong_zero_pm_one(e);
        assert(!cong(pp, 0)) by {
            if cong(pp, 0) {
                lemma_cong_refl(qq);
                lemma_cong_mul(pp, qq, 0, qq);
                lemma_mul_zero_factor(0, qq);
                lemma_cong_refl(dp);
                lemma_cong_mul(dp, pp * qq, dp, 0);
                lemma_mul_zero_factor(0, dp);
            }
        }
        // u2 + y2 and u2 − y2 are not both ≡ 0.
        assert(!cong(u2 + Y2, 0) || !cong(u2 - Y2, 0)) by {
            if cong(u2 + Y2, 0) && cong(u2 - Y2, 0) {
                lemma_cong_add(u2 + Y2, u2 - Y2, 0, 0);
                lemma_cong_sub(u2 + Y2, u2 - Y2, 0, 0);
                assert(u2 + Y2 + (u2 - Y2) == 2 * u2);
                lemma_cong_mul_zero(2, u2);
                lemma_cong_refl(Y2);
                lemma_cong_mul(u2, Y2, 0, Y2);
                lemma_mul_zero_factor(0, Y2);
                lemma_cong_refl(pp);
                lemma_cong_mul(pp, qq, pp, 0);
                lemma_mul_zero_factor(0, pp);
                lemma_cong_refl(dp);
                lemma_cong_mul(dp, pp * qq, dp, 0);
                lemma_mul_zero_factor(0, dp);
            }
        }
        // Pick the sign s with W = u2 + s·y2 ≢ 0. Then d'·(P·W)² ≡ (u1 + s·e·y1)².
        let (ww, nn) = if !cong(u2 + Y2, 0) {
            (
                u2 + Y2,
                if e == 1 {
                    u1 + Y1
                } else {
                    u1 - Y1
                },
            )
        } else {
            (
                u2 - Y2,
                if e == 1 {
                    u1 - Y1
                } else {
                    u1 + Y1
                },
            )
        };
        let s_pos = !cong(u2 + Y2, 0);
        if e == 1 {
            lemma_cong_eq_zero(k - 1, k - e);
        } else {
            lemma_cong_eq_zero(k + 1, k - e);
        }
        if s_pos {
            if e == 1 {
                lemma_denom_case_pp(u1, Y1, u2, Y2, dp);
            } else {
                lemma_denom_case_pm(u1, Y1, u2, Y2, dp);
            }
        } else {
            if e == 1 {
                lemma_denom_case_mp(u1, Y1, u2, Y2, dp);
            } else {
                lemma_denom_case_mm(u1, Y1, u2, Y2, dp);
            }
        }
        assert(cong(dp * (pp * pp) * (ww * ww) - nn * nn, 0));
        lemma_cong_diff_zero(dp * (pp * pp) * (ww * ww), nn * nn);
        // d'·(P·W)² = d'·P²·W².
        lemma_mul_assoc4(dp, pp * pp, ww * ww);
        lemma_sq_mul(pp, ww);
        lemma_mul_eq(dp, dp, (pp * pp) * (ww * ww), (pp * ww) * (pp * ww));
        lemma_cong_mul_nonzero(pp, ww);
        lemma_neg_d_square_absurd(pp * ww, nn);
    }
}

/// Completeness: for two points on the curve, 1 + t ≢ 0 and 1 − t ≢ 0.
pub proof fn lemma_edwards_add_denominators_cong(x1: nat, y1: nat, x2: nat, y2: nat)
    requires
        is_on_edwards_curve(x1, y1),
        is_on_edwards_curve(x2, y2),
    ensures
        !cong(1 + d_int() * (((x1 as int) * (x2 as int)) * ((y1 as int) * (y2 as int))), 0),
        !cong(1 - d_int() * (((x1 as int) * (x2 as int)) * ((y1 as int) * (y2 as int))), 0),
{
    let T = d_int() * (((x1 as int) * (x2 as int)) * ((y1 as int) * (y2 as int)));
    lemma_add_t_not_pm_one(x1, y1, x2, y2, 1);
    lemma_add_t_not_pm_one(x1, y1, x2, y2, -1);
    lemma_cong_refl(1);
    if cong(1 + T, 0) {
        lemma_cong_sub(1 + T, 1, 0, 1);
        assert(1 + T - 1 == T);
    }
    if cong(1 - T, 0) {
        lemma_cong_sub(1, 1 - T, 1, 0);
        assert(1 - (1 - T) == T);
    }
}

// =============================================================================
// Main result
// =============================================================================
/// Completeness and closure of Edwards addition, in the form of
/// `lemma_edwards_add_complete` in `curve_equation_lemmas`.
pub proof fn lemma_edwards_add_complete_cong(x1: nat, y1: nat, x2: nat, y2: nat)
    requires
        is_on_edwards_curve(x1, y1),
        is_on_edwards_curve(x2, y2),
    ensures
        ({
            let d = fe51_as_canonical_nat(&EDWARDS_D);
            let t = field_mul(d, field_mul(field_mul(x1, x2), field_mul(y1, y2)));
            field_add(1, t) != 0 && field_sub(1, t) != 0
        }),
        is_on_edwards_curve(edwards_add(x1, y1, x2, y2).0, edwards_add(x1, y1, x2, y2).1),
{
    lemma_cong_p_facts();
    let (X1, Y1, X2, Y2) = (x1 as int, y1 as int, x2 as int, y2 as int);
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let T = d_int() * ((X1 * X2) * (Y1 * Y2));
    lemma_edwards_add_denominators_cong(x1, y1, x2, y2);
    lemma_edwards_add_closure_cong(x1, y1, x2, y2);
    // Lift t = field_mul(d, (x1·x2)·(y1·y2)) to T.
    lemma_cong_refl(X1);
    lemma_cong_refl(Y1);
    lemma_cong_refl(X2);
    lemma_cong_refl(Y2);
    lemma_cong_refl(d as int);
    lemma_cong_refl(1);
    let x1x2 = field_mul(x1, x2);
    let y1y2 = field_mul(y1, y2);
    lemma_cong_fmul(x1, x2, X1, X2);
    lemma_cong_fmul(y1, y2, Y1, Y2);
    let m = field_mul(x1x2, y1y2);
    lemma_cong_fmul(x1x2, y1y2, X1 * X2, Y1 * Y2);
    let t = field_mul(d, m);
    lemma_cong_fmul(d, m, d as int, (X1 * X2) * (Y1 * Y2));
    lemma_cong_fadd(1, t, 1, T);
    lemma_cong_fsub(1, t, 1, T);
    lemma_mod_bound((1 + t) as int, p() as int);
    lemma_mod_bound((1 + p() - t) as int, p() as int);
    lemma_cong_canonical_zero(field_add(1, t));
    lemma_cong_canonical_zero(field_sub(1, t));
}

} // verus!
