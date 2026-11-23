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
use crate::lemmas::common_lemmas::mul_lemmas::*;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::field_lemmas::field_cong_lemmas::*;
use crate::lemmas::field_lemmas::sqrt_m1_lemmas::*;
use crate::specs::edwards_specs::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// Curve equation and addition in congruence form
// =============================================================================
/// The Edwards constant d as an integer.
pub open spec fn d_int() -> int {
    fe51_as_canonical_nat(&EDWARDS_D) as int
}

/// The curve equation as a polynomial: y² − x² − 1 − d·x²·y².
pub open spec fn curve_poly(x: int, y: int) -> int {
    y * y - x * x - 1 - d_int() * (x * x * (y * y))
}

/// is_on_edwards_curve(x, y) iff curve_poly(x, y) ≡ 0.
pub proof fn lemma_curve_cong(x: nat, y: nat)
    ensures
        is_on_edwards_curve(x, y) <==> cong(curve_poly(x as int, y as int), 0),
{
    lemma_cong_p_facts();
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let X = x as int;
    let Y = y as int;
    let x2 = field_square(x);
    let y2 = field_square(y);
    let x2y2 = field_mul(x2, y2);
    let dx2y2 = field_mul(d, x2y2);
    let lhs = field_sub(y2, x2);
    let rhs = field_add(1, dx2y2);
    lemma_cong_fsquare(x, X);
    lemma_cong_fsquare(y, Y);
    lemma_cong_fmul(x2, y2, X * X, Y * Y);
    lemma_cong_fmul(d, x2y2, d_int(), X * X * (Y * Y));
    lemma_cong_fsub(y2, x2, Y * Y, X * X);
    lemma_cong_fadd(1, dx2y2, 1, d_int() * (X * X * (Y * Y)));
    lemma_mod_bound((y2 + p() - x2) as int, p() as int);
    lemma_mod_bound((1 + dx2y2) as int, p() as int);
    let L = Y * Y - X * X;
    let R = 1 + d_int() * (X * X * (Y * Y));
    assert(curve_poly(X, Y) == L - R);
    if lhs == rhs {
        lemma_cong_sub(lhs as int, rhs as int, L, R);
    } else {
        if cong(L - R, 0) {
            lemma_cong_add(L - R, R, 0, R);
            assert(L - R + R == L);
            lemma_cong_canonical_eq(lhs, rhs);
        }
    }
}

/// edwards_add in congruence form: with t = d·x1x2·y1y2, if 1 + t ≢ 0 then
/// x3·(1 + t) ≡ x1y2 + y1x2, and if the numerator is ≡ 0 then x3 = 0.
/// The same holds for y3 with 1 − t and y1y2 + x1x2.
pub proof fn lemma_edwards_add_cong(x1: nat, y1: nat, x2: nat, y2: nat)
    ensures
        ({
            let (X1, Y1, X2, Y2) = (x1 as int, y1 as int, x2 as int, y2 as int);
            let t = d_int() * ((X1 * X2) * (Y1 * Y2));
            let (x3, y3) = edwards_add(x1, y1, x2, y2);
            &&& x3 < p()
            &&& y3 < p()
            &&& !cong(1 + t, 0) ==> cong((x3 as int) * (1 + t), X1 * Y2 + Y1 * X2)
            &&& cong(X1 * Y2 + Y1 * X2, 0) ==> x3 == 0
            &&& !cong(1 - t, 0) ==> cong((y3 as int) * (1 - t), Y1 * Y2 + X1 * X2)
            &&& cong(Y1 * Y2 + X1 * X2, 0) ==> y3 == 0
        }),
{
    lemma_cong_p_facts();
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let (X1, Y1, X2, Y2) = (x1 as int, y1 as int, x2 as int, y2 as int);
    let x1x2 = field_mul(x1, x2);
    let y1y2 = field_mul(y1, y2);
    let x1y2 = field_mul(x1, y2);
    let y1x2 = field_mul(y1, x2);
    lemma_cong_fmul(x1, x2, X1, X2);
    lemma_cong_fmul(y1, y2, Y1, Y2);
    lemma_cong_fmul(x1, y2, X1, Y2);
    lemma_cong_fmul(y1, x2, Y1, X2);
    let m = field_mul(x1x2, y1y2);
    lemma_cong_fmul(x1x2, y1y2, X1 * X2, Y1 * Y2);
    let tt = field_mul(d, m);
    let T = d_int() * ((X1 * X2) * (Y1 * Y2));
    lemma_cong_fmul(d, m, d_int(), (X1 * X2) * (Y1 * Y2));
    let dx = field_add(1, tt);
    let dy = field_sub(1, tt);
    lemma_cong_fadd(1, tt, 1, T);
    lemma_cong_fsub(1, tt, 1, T);
    let nx = field_add(x1y2, y1x2);
    let ny = field_add(y1y2, x1x2);
    lemma_cong_fadd(x1y2, y1x2, X1 * Y2, Y1 * X2);
    lemma_cong_fadd(y1y2, x1x2, Y1 * Y2, X1 * X2);
    let (x3, y3) = edwards_add(x1, y1, x2, y2);
    lemma_mod_bound((nx * field_inv(dx)) as int, p() as int);
    lemma_mod_bound((ny * field_inv(dy)) as int, p() as int);
    lemma_mod_bound((1 + tt) as int, p() as int);
    lemma_mod_bound((x1y2 + y1x2) as int, p() as int);
    lemma_mod_bound((y1y2 + x1x2) as int, p() as int);
    lemma_mod_bound((field_canonical(1) + p() - field_canonical(tt)) as int, p() as int);
    let NX = X1 * Y2 + Y1 * X2;
    let NY = Y1 * Y2 + X1 * X2;
    if !cong(1 + T, 0) {
        lemma_cong_inv(dx);
        let ii = field_inv(dx) as int;
        lemma_cong_fmul(nx, field_inv(dx), NX, ii);
        assert(cong(x3 as int, NX * ii));
        lemma_cong_mul(x3 as int, 1 + T, NX * ii, 1 + T);
        assert(NX * ii * (1 + T) == NX * (ii * (1 + T))) by (nonlinear_arith);
        lemma_cong_mul(ii, dx as int, ii, 1 + T);
        assert(cong(ii * (1 + T), 1));
        lemma_cong_mul(NX, ii * (1 + T), NX, 1);
        assert(NX * 1 == NX);
        assert(cong((x3 as int) * (1 + T), NX));
    }
    if cong(X1 * Y2 + Y1 * X2, 0) {
        lemma_cong_canonical_eq(nx, 0);
        lemma_small_mod(0, p());
        assert(0 * field_inv(dx) == 0);
    }
    if !cong(1 - T, 0) {
        lemma_cong_inv(dy);
        let ii = field_inv(dy) as int;
        lemma_cong_fmul(ny, field_inv(dy), NY, ii);
        assert(cong(y3 as int, NY * ii));
        lemma_cong_mul(y3 as int, 1 - T, NY * ii, 1 - T);
        assert(NY * ii * (1 - T) == NY * (ii * (1 - T))) by (nonlinear_arith);
        lemma_cong_mul(ii, dy as int, ii, 1 - T);
        assert(cong(ii * (1 - T), 1));
        lemma_cong_mul(NY, ii * (1 - T), NY, 1);
        assert(NY * 1 == NY);
        assert(cong((y3 as int) * (1 - T), NY));
    }
    if cong(Y1 * Y2 + X1 * X2, 0) {
        lemma_cong_canonical_eq(ny, 0);
        lemma_small_mod(0, p());
        assert(0 * field_inv(dy) == 0);
    }
}

/// d is not a square in GF(p) (Euler's criterion, by computation).
pub proof fn lemma_edwards_d_not_square()
    ensures
        !is_square(fe51_as_canonical_nat(&EDWARDS_D)),
{
    use vstd::arithmetic::power::*;
    reveal(pow);
    assert(fe51_as_canonical_nat(&EDWARDS_D) % p() != 0) by (compute_only);
    assert(pow_mod(fe51_as_canonical_nat(&EDWARDS_D), ((p() - 1) / 2) as nat, p()) != 1)
        by (compute_only);
    lemma_not_square_by_euler(fe51_as_canonical_nat(&EDWARDS_D));
}

// =============================================================================
// Ring identities
// =============================================================================
// The proofs below are mechanical. Each product of sums is expanded by one
// `lemma_dist_K_L` call and small monomial steps, because Z3's nonlinear
// mode does not expand products of sums reliably.
/// Ny² − Nx² = U·V, with Nx = x1·y2 + y1·x2, Ny = y1·y2 + x1·x2, U = y1² − x1² and
/// V = y2² − x2².
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

/// Nx² + Ny² = s1·s2 + 4·(x1·x2)·(y1·y2), with Nx = x1·y2 + y1·x2, Ny = y1·y2 + x1·x2,
/// s1 = x1² + y1² and s2 = x2² + y2².
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
}

/// Nx·Ny = p1·s2 + p2·s1, with Nx = x1·y2 + y1·x2, Ny = y1·y2 + x1·x2, p1 = x1·y1,
/// p2 = x2·y2, s1 = x1² + y1² and s2 = x2² + y2².
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

/// d·(p1·s2 + p2·s1)² = A·v² + B·u² + 2·T·(s1·s2 + 4·p1·p2) + A·(s2² − v² − 4·p2²)
/// + B·(s1² − u² − 4·p1²), with A = d·p1², B = d·p2² and T = d·p1·p2.
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
    assert(((d)) * ((p1 * p1)) == (d * p1 * p1)) by (nonlinear_arith);
    assert(((d * p1 * p1)) * ((v * v)) == (d * p1 * p1 * v * v)) by (nonlinear_arith);
    assert(((d)) * ((p2 * p2)) == (d * p2 * p2)) by (nonlinear_arith);
    assert(((d * p2 * p2)) * ((u * u)) == (d * p2 * p2 * u * u)) by (nonlinear_arith);
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

/// (x² + y²)² − (y² − x²)² = 4·(x·y)².
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
    assert(((x * y)) * ((x * y)) == (x * x * y * y)) by (nonlinear_arith);
}

/// (1 + t)²·yy − (1 − t)²·xx − ((1 + t)·(1 − t))² = (1 + t²)·(yy − xx) + 2·t·(xx + yy) − (1 − t²)².
/// For t = d·(x1x2)·(y1y2), xx = Nx² and yy = Ny², with Nx = x1·y2 + y1·x2, Ny = y1·y2 + x1·x2
/// the numerators of edwards_add(x1, y1, x2, y2), the left side is the cleared curve polynomial
/// of the sum without its −d·Nx²·Ny² term.
proof fn lemma_id_add_cleared(t: int, xx: int, yy: int)
    ensures
        (1 + t) * (1 + t) * yy - (1 - t) * (1 - t) * xx - ((1 + t) * (1 - t)) * ((1 + t) * (1 - t))
            == (1 + t * t) * (yy - xx) + 2 * t * (xx + yy) - (1 - t * t) * (1 - t * t),
{
    lemma_dist_2_2(1, (t), 1, (t), (1 + t), (1 + t));
    assert((1) * (1) == 1);
    assert((1) * ((t)) == (t));
    assert(((t)) * (1) == (t));
    lemma_dist_3_1(1, (2 * (t)), (t * t), (yy), ((1 + t) * (1 + t)), (yy));
    assert((1) * ((yy)) == (yy));
    assert(((2 * (t))) * ((yy)) == (2 * (t * yy))) by (nonlinear_arith);
    lemma_dist_2_2(1, (-(t)), 1, (-(t)), (1 - t), (1 - t));
    assert((1) * ((-(t))) == (-(t)));
    assert(((-(t))) * (1) == (-(t)));
    assert(((-(t))) * ((-(t))) == (t * t)) by (nonlinear_arith);
    lemma_dist_3_1(1, (-(2 * (t))), (t * t), (xx), ((1 - t) * (1 - t)), (xx));
    assert((1) * ((xx)) == (xx));
    assert(((-(2 * (t)))) * ((xx)) == (-(2 * (t * xx)))) by (nonlinear_arith);
    lemma_dist_2_2(1, (t), 1, (-(t)), (1 + t), (1 - t));
    assert(((t)) * ((-(t))) == (-(t * t))) by (nonlinear_arith);
    lemma_dist_2_2(1, (-(t * t)), 1, (-(t * t)), ((1 + t) * (1 - t)), ((1 + t) * (1 - t)));
    assert((1) * ((-(t * t))) == (-(t * t)));
    assert(((-(t * t))) * (1) == (-(t * t)));
    assert(((-(t * t))) * ((-(t * t))) == (t * t * t * t)) by (nonlinear_arith);
    lemma_dist_2_2(1, (t * t), (-(xx)), (yy), (1 + t * t), (yy - xx));
    assert((1) * ((-(xx))) == (-(xx)));
    assert(((t * t)) * ((-(xx))) == (-(t * t * xx))) by (nonlinear_arith);
    lemma_dist_1_2((2 * (t)), (xx), (yy), (2 * t), (xx + yy));
    assert(((2 * (t))) * ((xx)) == (2 * (t * xx))) by (nonlinear_arith);
    lemma_dist_2_2(1, (-(t * t)), 1, (-(t * t)), (1 - t * t), (1 - t * t));
}

/// The closure certificate: F = q1·(u − 1 − a) + q2·(v − 1 − b) + (t² − a·b)·(u·v + 2 − t² − a·b),
/// with F = (1 + t²)·u·v − a·v² − b·u² − (1 − t²)², q1 = (1 + a·b)·v − b·(u + 1 + a) and
/// q2 = 1 − a·v + a²·b.
proof fn lemma_id_add_certificate(u: int, v: int, a: int, b: int, t: int)
    ensures
        (1 + t * t) * (u * v) - a * (v * v) - b * (u * u) - (1 - t * t) * (1 - t * t) == ((1 + a
            * b) * v - b * (u + 1 + a)) * (u - 1 - a) + (1 - a * v + a * a * b) * (v - 1 - b) + (t
            * t - a * b) * (u * v + 2 - t * t - a * b),
{
    lemma_dist_2_1(1, (t * t), (u * v), (1 + t * t), (u * v));
    assert((1) * ((u * v)) == (u * v));
    assert(((t * t)) * ((u * v)) == (t * t * u * v)) by (nonlinear_arith);
    assert(((a)) * ((v * v)) == (a * v * v)) by (nonlinear_arith);
    assert(((b)) * ((u * u)) == (b * u * u)) by (nonlinear_arith);
    lemma_dist_2_2(1, (-(t * t)), 1, (-(t * t)), (1 - t * t), (1 - t * t));
    assert((1) * (1) == 1);
    assert((1) * ((-(t * t))) == (-(t * t)));
    assert(((-(t * t))) * (1) == (-(t * t)));
    assert(((-(t * t))) * ((-(t * t))) == (t * t * t * t)) by (nonlinear_arith);
    lemma_dist_2_1(1, (a * b), (v), (1 + a * b), (v));
    assert((1) * ((v)) == (v));
    lemma_dist_1_3((b), 1, (a), (u), (b), (u + 1 + a));
    assert(((b)) * (1) == (b));
    assert(((b)) * ((a)) == (a * b)) by (nonlinear_arith);
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
    assert(((-(a * b))) * ((-1)) == (a * b));
    assert(((-(a * b))) * ((-(a))) == (a * a * b)) by (nonlinear_arith);
    assert(((-(a * b))) * ((u)) == (-(a * b * u))) by (nonlinear_arith);
    assert(((a * b * v)) * ((-1)) == (-(a * b * v)));
    assert(((a * b * v)) * ((-(a))) == (-(a * a * b * v))) by (nonlinear_arith);
    assert(((a * b * v)) * ((u)) == (a * b * u * v)) by (nonlinear_arith);
    assert(((-(b))) * ((-1)) == (b));
    assert(((-(b))) * ((-(a))) == (a * b)) by (nonlinear_arith);
    assert(((-(b))) * ((u)) == (-(b * u))) by (nonlinear_arith);
    assert(((-(b * u))) * ((-1)) == (b * u));
    assert(((-(b * u))) * ((-(a))) == (a * b * u)) by (nonlinear_arith);
    assert(((-(b * u))) * ((u)) == (-(b * u * u))) by (nonlinear_arith);
    assert(((v)) * ((-1)) == (-(v)));
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
    assert((1) * ((-1)) == (-1));
    assert((1) * ((-(b))) == (-(b)));
    assert(((a * a * b)) * ((-1)) == (-(a * a * b)));
    assert(((a * a * b)) * ((-(b))) == (-(a * a * b * b))) by (nonlinear_arith);
    assert(((-(a * v))) * ((-1)) == (a * v));
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
}

// Denominator certificates. For s, ε ∈ {1, −1}, with k = dp·pp·qq,
// c1 = u1² + y1² − 1 − dp·pp² and c2 = u2² + y2² − 1 − dp·qq²:
// dp·pp²·(u2² + 2·s·qq + y2²) − (u1² + 2·s·ε·pp + y1²) = dp·pp²·c2 − c1 + (k − ε)·(k + ε + 2·s·pp).
/// The denominator certificate for s = 1, ε = 1.
proof fn lemma_id_denom_cert_pp(u1: int, y1: int, u2: int, y2: int, dp: int, pp: int, qq: int)
    ensures
        dp * (pp * pp) * (u2 * u2 + 2 * qq + y2 * y2) - (u1 * u1 + 2 * pp + y1 * y1) == dp * (pp
            * pp) * (u2 * u2 + y2 * y2 - 1 - dp * (qq * qq)) - (u1 * u1 + y1 * y1 - 1 - dp * (pp
            * pp)) + (dp * (pp * qq) - 1) * (dp * (pp * qq) + 1 + 2 * pp),
{
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
    assert(((dp * pp * pp)) * ((-1)) == (-(dp * pp * pp)));
    assert(((dp * pp * pp)) * ((-(dp * qq * qq))) == (-(dp * dp * pp * pp * qq * qq)))
        by (nonlinear_arith);
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
    assert(((-1)) * (1) == (-1));
    assert(((-1)) * ((dp * pp * qq)) == (-(dp * pp * qq)));
    assert(((-1)) * ((2 * (pp))) == (-(2 * (pp))));
    assert(((dp * pp * qq)) * (1) == (dp * pp * qq));
    assert(((dp * pp * qq)) * ((dp * pp * qq)) == (dp * dp * pp * pp * qq * qq))
        by (nonlinear_arith);
    assert(((dp * pp * qq)) * ((2 * (pp))) == (2 * (dp * pp * pp * qq))) by (nonlinear_arith);
}

/// The denominator certificate for s = 1, ε = −1.
proof fn lemma_id_denom_cert_pm(u1: int, y1: int, u2: int, y2: int, dp: int, pp: int, qq: int)
    ensures
        dp * (pp * pp) * (u2 * u2 + 2 * qq + y2 * y2) - (u1 * u1 - 2 * pp + y1 * y1) == dp * (pp
            * pp) * (u2 * u2 + y2 * y2 - 1 - dp * (qq * qq)) - (u1 * u1 + y1 * y1 - 1 - dp * (pp
            * pp)) + (dp * (pp * qq) + 1) * (dp * (pp * qq) - 1 + 2 * pp),
{
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
    assert(((dp * pp * pp)) * ((-1)) == (-(dp * pp * pp)));
    assert(((dp * pp * pp)) * ((-(dp * qq * qq))) == (-(dp * dp * pp * pp * qq * qq)))
        by (nonlinear_arith);
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
    assert((1) * ((-1)) == (-1));
    assert((1) * ((dp * pp * qq)) == (dp * pp * qq));
    assert((1) * ((2 * (pp))) == (2 * (pp)));
    assert(((dp * pp * qq)) * ((-1)) == (-(dp * pp * qq)));
    assert(((dp * pp * qq)) * ((dp * pp * qq)) == (dp * dp * pp * pp * qq * qq))
        by (nonlinear_arith);
    assert(((dp * pp * qq)) * ((2 * (pp))) == (2 * (dp * pp * pp * qq))) by (nonlinear_arith);
}

/// The denominator certificate for s = −1, ε = 1.
proof fn lemma_id_denom_cert_mp(u1: int, y1: int, u2: int, y2: int, dp: int, pp: int, qq: int)
    ensures
        dp * (pp * pp) * (u2 * u2 - 2 * qq + y2 * y2) - (u1 * u1 - 2 * pp + y1 * y1) == dp * (pp
            * pp) * (u2 * u2 + y2 * y2 - 1 - dp * (qq * qq)) - (u1 * u1 + y1 * y1 - 1 - dp * (pp
            * pp)) + (dp * (pp * qq) - 1) * (dp * (pp * qq) + 1 - 2 * pp),
{
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
    assert(((dp * pp * pp)) * ((-1)) == (-(dp * pp * pp)));
    assert(((dp * pp * pp)) * ((-(dp * qq * qq))) == (-(dp * dp * pp * pp * qq * qq)))
        by (nonlinear_arith);
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
    assert(((-1)) * (1) == (-1));
    assert(((-1)) * ((dp * pp * qq)) == (-(dp * pp * qq)));
    assert(((-1)) * ((-(2 * (pp)))) == (2 * (pp)));
    assert(((dp * pp * qq)) * (1) == (dp * pp * qq));
    assert(((dp * pp * qq)) * ((dp * pp * qq)) == (dp * dp * pp * pp * qq * qq))
        by (nonlinear_arith);
    assert(((dp * pp * qq)) * ((-(2 * (pp)))) == (-(2 * (dp * pp * pp * qq)))) by (nonlinear_arith);
}

/// The denominator certificate for s = −1, ε = −1.
proof fn lemma_id_denom_cert_mm(u1: int, y1: int, u2: int, y2: int, dp: int, pp: int, qq: int)
    ensures
        dp * (pp * pp) * (u2 * u2 - 2 * qq + y2 * y2) - (u1 * u1 + 2 * pp + y1 * y1) == dp * (pp
            * pp) * (u2 * u2 + y2 * y2 - 1 - dp * (qq * qq)) - (u1 * u1 + y1 * y1 - 1 - dp * (pp
            * pp)) + (dp * (pp * qq) + 1) * (dp * (pp * qq) - 1 - 2 * pp),
{
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
    assert(((dp * pp * pp)) * ((-1)) == (-(dp * pp * pp)));
    assert(((dp * pp * pp)) * ((-(dp * qq * qq))) == (-(dp * dp * pp * pp * qq * qq)))
        by (nonlinear_arith);
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
    assert((1) * ((-1)) == (-1));
    assert((1) * ((dp * pp * qq)) == (dp * pp * qq));
    assert((1) * ((-(2 * (pp)))) == (-(2 * (pp))));
    assert(((dp * pp * qq)) * ((-1)) == (-(dp * pp * qq)));
    assert(((dp * pp * qq)) * ((dp * pp * qq)) == (dp * dp * pp * pp * qq * qq))
        by (nonlinear_arith);
    assert(((dp * pp * qq)) * ((-(2 * (pp)))) == (-(2 * (dp * pp * pp * qq)))) by (nonlinear_arith);
}

/// Clearing denominators: with r = x3·a and q = y3·b,
/// (a·b)²·(y3² − x3² − 1 − d·x3²·y3²) = a²·q² − b²·r² − (a·b)² − d·r²·q².
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
    lemma_product_square_factorize(d, q);
    lemma_product_square_factorize(x1 * x2, y1 * y2);
    lemma_product_square_factorize(x1, x2);
    lemma_product_square_factorize(y1, y2);
    lemma_mul_quad_prod(x1 * x1, x2 * x2, y1 * y1, y2 * y2);
    lemma_mul_quad_prod(d, r1, d, r2);
}

/// d·Nx²·Ny² = A·V² + B·U² + 2·T·(Nx² + Ny²), with Nx = x1·y2 + y1·x2, Ny = y1·y2 + x1·x2,
/// U = y1² − x1², V = y2² − x2², A = d·x1²y1², B = d·x2²y2² and T = d·(x1x2)·(y1y2).
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
    lemma_product_square_factorize(nx, ny);
    lemma_id_add_num_prod(x1, y1, x2, y2);
    lemma_id_add_d_prod(d, p1, p2, s1, s2, u, v);
    // The two terms that vanish.
    lemma_id_sum_sq_rel(x1, y1);
    lemma_id_sum_sq_rel(x2, y2);
    lemma_mul_by_zero_is_zero(d * (p1 * p1));
    lemma_mul_by_zero_is_zero(d * (p2 * p2));
    // d·p1² = A and d·p2² = B.
    lemma_product_square_factorize(x1, y1);
    lemma_product_square_factorize(x2, y2);
    // d·p1·p2 = T and s1·s2 + 4·p1·p2 = Nx² + Ny².
    lemma_mul_quad_prod(x1, y1, x2, y2);
    lemma_id_add_num_sum(x1, y1, x2, y2);
}

/// Closure: if both points are on the curve and 1 ± t ≢ 0, with t = d·x1x2·y1y2, the sum is on
/// the curve.
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
    lemma_add_d_num_square(X1, Y1, X2, Y2, D);
    let h = (1 + T * T) * (u * v) - a * (v * v) - b * (u * u) - (1 - T * T) * (1 - T * T);
    assert(fnn == h);

    // h = q1·c1 + q2·c2 + (T² − A·B)·K, and T² = A·B.
    lemma_id_add_certificate(u, v, a, b, T);
    lemma_add_t_square(X1, Y1, X2, Y2, D);
    let kk = u * v + 2 - T * T - a * b;
    lemma_mul_by_zero_is_zero(kk);
    let q1 = (1 + a * b) * v - b * (u + 1 + a);
    let q2 = 1 - a * v + a * a * b;
    lemma_curve_cong(x1, y1);
    lemma_curve_cong(x2, y2);
    lemma_cong_combo2(q1, u - 1 - a, q2, v - 1 - b);
    assert(cong(fr, 0));

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
    lemma_product_square_factorize(i, x);
    lemma_cong_mul(i * i, x * x, -1, x * x);
    assert(cong(u * u, -(x * x)));
    lemma_cong_mul(u * u, y * y, -(x * x), y * y);
    lemma_cong_mul(-d, u * u * (y * y), -d, (-(x * x)) * (y * y));
    lemma_mul_unary_negation(x * x, y * y);
    lemma_mul_cancels_negatives(d, (x * x) * (y * y));
    lemma_cong_add(u * u, y * y, -(x * x), y * y);
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
    lemma_mul_quad_prod(i * x1, y1, i * x2, y2);
    lemma_mul_quad_prod(i, x1, i, x2);
    lemma_cong_mul(i * i, x1 * x2, -1, x1 * x2);
    lemma_cong_mul((i * i) * (x1 * x2), y1 * y2, -(x1 * x2), y1 * y2);
    lemma_cong_mul(-d, ((i * i) * (x1 * x2)) * (y1 * y2), -d, (-(x1 * x2)) * (y1 * y2));
    lemma_mul_unary_negation(x1 * x2, y1 * y2);
    lemma_mul_cancels_negatives(d, (x1 * x2) * (y1 * y2));
}

/// −d·bb² ≡ nn² with bb ≢ 0 is impossible: d would be a square, contradicting
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
    lemma_product_square_factorize(nn, BI);
    lemma_cong_mul(nn * nn, BI * BI, (-D) * (bb * bb), BI * BI);
    lemma_mul_is_associative(-D, bb * bb, BI * BI);
    lemma_product_square_factorize(bb, BI);
    lemma_cong_mul(bb * BI, bb * BI, 1, 1);
    lemma_cong_mul(-D, (bb * BI) * (bb * BI), -D, 1);
    assert(cong(W * W, -D));
    // v = i·w, v² ≡ i²·w² ≡ (−1)·(−d) = d.
    let v = field_mul(i, w);
    lemma_cong_fmul(i, w, I, W);
    let V = v as int;
    lemma_cong_mul(V, V, I * W, I * W);
    lemma_product_square_factorize(I, W);
    lemma_cong_mul(I * I, W * W, -1, -D);
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

// Denominator cases. For s, ε ∈ {1, −1}: if (u1, y1) and (u2, y2) satisfy
// u² + y² ≡ 1 + dp·u²·y², and dp·(u1·y1)·(u2·y2) ≡ ε, then
// dp·(u1·y1)²·(u2 + s·y2)² ≡ (u1 + s·ε·y1)².
/// The denominator case s = 1, ε = 1.
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
    lemma_square_of_sum(u2, y2);
    lemma_square_of_sum(u1, y1);
    lemma_id_denom_cert_pp(u1, y1, u2, y2, dp, pp, qq);
    lemma_cong_combo3(dp * (pp * pp), c2, -1, c1, q3, h3);
}

/// The denominator case s = 1, ε = −1.
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
    lemma_square_of_sum(u2, y2);
    lemma_square_of_difference(u1, y1);
    lemma_id_denom_cert_pm(u1, y1, u2, y2, dp, pp, qq);
    lemma_cong_combo3(dp * (pp * pp), c2, -1, c1, q3, h3);
}

/// The denominator case s = −1, ε = 1.
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
    lemma_square_of_difference(u2, y2);
    lemma_square_of_difference(u1, y1);
    lemma_id_denom_cert_mp(u1, y1, u2, y2, dp, pp, qq);
    lemma_cong_combo3(dp * (pp * pp), c2, -1, c1, q3, h3);
}

/// The denominator case s = −1, ε = −1.
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
    lemma_square_of_difference(u2, y2);
    lemma_square_of_sum(u1, y1);
    lemma_id_denom_cert_mm(u1, y1, u2, y2, dp, pp, qq);
    lemma_cong_combo3(dp * (pp * pp), c2, -1, c1, q3, h3);
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
        lemma_product_square_factorize(u1, Y1);
        lemma_product_square_factorize(u2, Y2);
        let c1 = u1 * u1 + Y1 * Y1 - 1 - dp * (pp * pp);
        let c2 = u2 * u2 + Y2 * Y2 - 1 - dp * (qq * qq);
        assert(cong(c1, 0));
        assert(cong(c2, 0));
        // u1, y1 ≢ 0, else k ≡ 0.
        lemma_cong_zero_pm_one(e);
        assert(!cong(pp, 0)) by {
            if cong(pp, 0) {
                lemma_cong_mul(pp, qq, 0, qq);
                lemma_mul_by_zero_is_zero(qq);
                lemma_cong_mul(dp, pp * qq, dp, 0);
                lemma_mul_by_zero_is_zero(dp);
            }
        }
        // u2 + y2 and u2 − y2 are not both ≡ 0.
        assert(!cong(u2 + Y2, 0) || !cong(u2 - Y2, 0)) by {
            if cong(u2 + Y2, 0) && cong(u2 - Y2, 0) {
                lemma_cong_add(u2 + Y2, u2 - Y2, 0, 0);
                lemma_cong_sub(u2 + Y2, u2 - Y2, 0, 0);
                assert(u2 + Y2 + (u2 - Y2) == 2 * u2);
                lemma_cong_mul_zero(2, u2);
                lemma_cong_mul(u2, Y2, 0, Y2);
                lemma_mul_by_zero_is_zero(Y2);
                lemma_cong_mul(pp, qq, pp, 0);
                lemma_mul_by_zero_is_zero(pp);
                lemma_cong_mul(dp, pp * qq, dp, 0);
                lemma_mul_by_zero_is_zero(dp);
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
        } else {
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
        lemma_mul_is_associative(dp, pp * pp, ww * ww);
        lemma_product_square_factorize(pp, ww);
        lemma_cong_mul_nonzero(pp, ww);
        lemma_neg_d_square_absurd(pp * ww, nn);
    }
}

/// Completeness: for two points on the curve, 1 + t ≢ 0 and 1 − t ≢ 0, with t = d·x1x2·y1y2.
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
