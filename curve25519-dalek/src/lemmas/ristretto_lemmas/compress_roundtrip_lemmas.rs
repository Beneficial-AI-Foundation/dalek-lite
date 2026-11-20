//! Ristretto compress/decompress round trip and injectivity on classes.
//!
//! Main results:
//! - `lemma_ristretto_compress_roundtrip`: for (x, y) on the curve and in 2E,
//!   decompress(compress(x, y)) succeeds and the decoded point is in the
//!   coset (x, y) + E[4].
//! - `lemma_ristretto_compress_injective`: two such points with the same
//!   encoding are in the same coset.
//!
//! Proof outline (RFC 9496 §4.3.1, §4.3.2; Hamburg, "Decaf" §4):
//! 0. If x·y = 0, the point is in E[4]. The encoder outputs s = 0, and the
//!    decoder returns (0, 1), which is in the coset.
//! 1. If x·y ≠ 0, with Z = 1 and T = x·y, the encoder computes z_inv = 1.
//!    It selects a representative (X, Y) of the coset: X ≥ 0 and X·Y ≥ 0.
//!    Its output s satisfies s²·(1 + Y) = 1 − Y.
//! 2. The decoder, given s with s²·(1 + Y) = 1 − Y, returns (X, Y).
//! 3. Step 1 needs (1 − y²)·(x·y)² to be a nonzero square. This holds for
//!    points in 2E with x·y ≠ 0.
//!
//! The algebra uses `field_cong_lemmas`: each field expression is lifted to an
//! integer polynomial congruent to it mod p.
#![allow(unused_imports)]
use crate::backend::serial::u64::constants as u64_constants;
use crate::backend::serial::u64::constants::EDWARDS_D;
use crate::edwards::EdwardsPoint;
use crate::lemmas::common_lemmas::mul_lemmas::*;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::common_lemmas::to_nat_lemmas::*;
use crate::lemmas::edwards_lemmas::add_complete_lemmas::*;
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::lemmas::field_lemmas::field_cong_lemmas::*;
use crate::lemmas::field_lemmas::from_bytes_lemmas::*;
use crate::lemmas::field_lemmas::sqrt_m1_lemmas::*;
use crate::lemmas::field_lemmas::sqrt_ratio_lemmas::*;
use crate::ristretto::RistrettoPoint;
use crate::specs::core_specs::*;
use crate::specs::edwards_specs::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use crate::specs::ristretto_specs::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

proof fn lemma_id_decode_kkv(K: int, T: int, D: int)
    ensures
        K * K * ((-D) * ((1 - T) * (1 - T)) - (1 + T) * (1 + T)) == -D * ((K * (1 - T)) * (K * (1
            - T))) - (K * (1 + T)) * (K * (1 + T)),
{
    assert(K * K * ((-D) * ((1 - T) * (1 - T)) - (1 + T) * (1 + T)) == -D * ((K * (1 - T)) * (K * (1
        - T))) - (K * (1 + T)) * (K * (1 + T))) by (nonlinear_arith);
}

proof fn lemma_id_decode_w(D: int, Y: int, h: int)
    ensures
        -D * ((2 * Y - h) * (2 * Y - h)) - (2 + h) * (2 + h) == -4 * D * Y * Y - 4 + h * (4 * D * Y
            - D * h - 4 - h),
{
    assert((2 * Y - h) * (2 * Y - h) == 4 * (Y * Y) - 4 * (Y * h) + h * h) by (nonlinear_arith);
    assert((2 + h) * (2 + h) == 4 + 4 * h + h * h) by (nonlinear_arith);
    assert(-D * (4 * (Y * Y) - 4 * (Y * h) + h * h) == -4 * (D * (Y * Y)) + 4 * (D * (Y * h)) - D
        * (h * h)) by (nonlinear_arith);
    assert(h * (4 * D * Y - D * h - 4 - h) == 4 * (D * (Y * h)) - D * (h * h) - 4 * h - h * h)
        by (nonlinear_arith);
    assert(-4 * D * Y * Y == -4 * (D * (Y * Y))) by (nonlinear_arith);
}

proof fn lemma_id_decode_split(K: int, X: int, V: int, T: int)
    ensures
        K * K * (X * X * V - 4 * T) == X * X * (K * K * V) - 4 * K * (T * K),
{
    assert(K * K * (X * X * V - 4 * T) == X * X * (K * K * V) - 4 * K * (T * K))
        by (nonlinear_arith);
}

proof fn lemma_id_decode_final(m: int, Y: int, D: int, h: int, Q1: int)
    ensures
        m * (-4 * D * Y * Y - 4 + h * Q1) - 4 * (1 + Y) * (h + (1 - Y)) == 4 * (Y * Y - m - 1 - D
            * (m * (Y * Y))) + (m * Q1 - 4 * (1 + Y)) * h,
{
    let u = -4 * D * Y * Y;
    let v = h * Q1;
    assert(m * (u - 4 + v) == m * u - 4 * m + m * v) by (nonlinear_arith);
    assert(m * u == -4 * (D * (m * (Y * Y)))) by (nonlinear_arith)
        requires
            u == -4 * D * Y * Y,
    ;
    assert(m * v == (m * Q1) * h) by (nonlinear_arith)
        requires
            v == h * Q1,
    ;
    assert(m * (-4 * D * Y * Y - 4 + h * Q1) == -4 * (D * (m * (Y * Y))) - 4 * m + (m * Q1) * h);
    assert(4 * (1 + Y) * (h + (1 - Y)) == 4 * (1 + Y) * h + 4 - 4 * (Y * Y)) by (nonlinear_arith);
    assert((m * Q1 - 4 * (1 + Y)) * h == (m * Q1) * h - 4 * (1 + Y) * h) by (nonlinear_arith);
}

proof fn lemma_id_decode_yd(Y: int, T: int, J: int, hs: int)
    requires
        hs == Y * (1 + T) - (1 - T),
    ensures
        2 * ((1 - T) * (1 + T) * J) - 2 * Y == (2 * Y - hs) * (J * ((1 + T) * (1 + T)) - 1) + (-1
            - (1 - T) * (1 + T) * J) * hs,
{
    let P = 1 + T;
    let Mn = 1 - T;
    assert((2 * Y - hs) * (J * (P * P) - 1) == 2 * Y * (J * (P * P)) - 2 * Y - hs * (J * (P * P))
        + hs) by (nonlinear_arith);
    assert((-1 - Mn * P * J) * hs == -hs - hs * (Mn * P * J)) by (nonlinear_arith);
    assert(hs * (J * (P * P)) + hs * (Mn * P * J) == hs * J * P * (P + Mn)) by (nonlinear_arith);
    assert(P + Mn == 2);
    assert(hs * J * P * 2 == 2 * (hs * J * P)) by (nonlinear_arith);
    assert(2 * Y * (J * (P * P)) - 2 * (hs * J * P) == 2 * J * P * (Y * P - hs))
        by (nonlinear_arith);
    assert(Y * P - hs == Mn);
    assert(2 * J * P * Mn == 2 * (Mn * P * J)) by (nonlinear_arith);
}

/// The decoder inverts the encoder on a representative.
///
/// If (x, y) is on the curve, x is non-negative and nonzero, 1 ± y ≢ 0, and
/// s²·(1 + y) ≡ 1 − y, then decoding s succeeds and returns (x, y).
///
/// Proof, with u1, u2, v, x_tmp and I = invsqrt as in `ristretto_decode_inner`: let
/// K = 1 + y and T = s². Then K·(1 + T) ≡ 2 and K·(1 − T) ≡ 2y, so K²·v ≡ −4·(1 + d·y²)
/// and, with the curve equation, x²·v ≡ 4·T. So v·u2² is a nonzero square, I²·v·u2² ≡ 1,
/// the decoded y satisfies y_dec·u2 ≡ u1, so y_dec ≡ y, and x_tmp² ≡ x² gives |x_tmp| = x.
pub proof fn lemma_decode_of_representative(s: nat, x: nat, y: nat)
    requires
        s < p(),
        x < p(),
        y < p(),
        x % 2 == 0,
        x != 0,
        is_on_edwards_curve(x, y),
        cong((s as int) * (s as int) * (1 + (y as int)), 1 - (y as int)),
        !cong(1 + (y as int), 0),
        !cong(1 - (y as int), 0),
    ensures
        ristretto_decode_inner(s) == (x, y, true),
{
    lemma_cong_p_facts();
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let D = d_int();
    let S = s as int;
    let X = x as int;
    let Y = y as int;
    let T = S * S;
    let K = 1 + Y;
    // Lift the decode intermediates.
    let ss = field_square(s);
    lemma_cong_fsquare(s, S);
    let u1 = field_sub(1, ss);
    lemma_cong_fsub(1, ss, 1, T);
    let u2 = field_add(1, ss);
    lemma_cong_fadd(1, ss, 1, T);
    let u2_sqr = field_square(u2);
    lemma_cong_fsquare(u2, 1 + T);
    let neg_d = field_neg(d);
    lemma_cong_fneg(d, D);
    let u1_sqr = field_square(u1);
    lemma_cong_fsquare(u1, 1 - T);
    let ndu = field_mul(neg_d, u1_sqr);
    lemma_cong_fmul(neg_d, u1_sqr, -D, (1 - T) * (1 - T));
    let v = field_sub(ndu, u2_sqr);
    let V = (-D) * ((1 - T) * (1 - T)) - (1 + T) * (1 + T);
    lemma_cong_fsub(ndu, u2_sqr, (-D) * ((1 - T) * (1 - T)), (1 + T) * (1 + T));
    let vu = field_mul(v, u2_sqr);
    let VU = V * ((1 + T) * (1 + T));
    lemma_cong_fmul(v, u2_sqr, V, (1 + T) * (1 + T));

    // Hypotheses as polynomials congruent to 0.
    let hs = T * K - (1 - Y);
    lemma_cong_diff_zero(T * K, 1 - Y);
    let hc = curve_poly(X, Y);
    lemma_curve_cong(x, y);
    assert(hc == Y * Y - X * X - 1 - D * (X * X * (Y * Y)));

    // x²·v ≡ 4·T.
    let hv = X * X * V - 4 * T;
    let qs = X * X * (4 * D * Y - D * hs - 4 - hs) - 4 * K;
    let A = K * (1 + T);
    let B = K * (1 - T);
    let W = K * K * V;
    lemma_id_decode_kkv(K, T, D);
    assert(A == 2 + hs && B == 2 * Y - hs) by (nonlinear_arith)
        requires
            A == K * (1 + T),
            B == K * (1 - T),
            hs == T * K - (1 - Y),
            K == 1 + Y,
    ;
    assert(W == -D * (B * B) - A * A);
    lemma_id_decode_w(D, Y, hs);
    let Q1 = 4 * D * Y - D * hs - 4 - hs;
    assert(W == -4 * D * Y * Y - 4 + hs * Q1);
    lemma_id_decode_split(K, X, V, T);
    assert(T * K == hs + (1 - Y));
    lemma_id_decode_final(X * X, Y, D, hs, Q1);
    assert(qs == X * X * Q1 - 4 * (1 + Y));
    assert(K * K * hv == 4 * hc + qs * hs);
    lemma_cong_combo2(4, hc, qs, hs);
    lemma_cong_mul_nonzero(K, K);
    lemma_cong_mul_zero(K * K, hv);
    assert(cong(hv, 0));

    // Nonzero facts.
    assert(!cong(T, 0)) by {
        if cong(T, 0) {
            lemma_cong_mul(T, K, 0, K);
            assert(0 * K == 0);
        }
    }
    assert(!cong(V, 0)) by {
        if cong(V, 0) {
            lemma_cong_mul(X * X, V, X * X, 0);
            assert(X * X * 0 == 0);
            lemma_cong_diff_zero(X * X * V, 4 * T);
            lemma_cong_mul_nonzero(4, T);
        }
    }
    assert(!cong(1 + T, 0)) by {
        assert(K * (1 + T) == 2 + 1 * hs);
        lemma_cong_add_multiple(2, 1, hs);
        if cong(1 + T, 0) {
            lemma_cong_mul(K, 1 + T, K, 0);
            assert(K * 0 == 0);
        }
    }
    lemma_cong_mul_nonzero(1 + T, 1 + T);
    lemma_cong_mul_nonzero(V, (1 + T) * (1 + T));
    assert(!cong(vu as int, 0));
    lemma_mod_bound((v * u2_sqr) as int, p() as int);

    // v·u2²·x² ≡ (2·s·(1 + T))².
    let num = 2 * S * (1 + T);
    assert(VU * (X * X) == (1 + T) * (1 + T) * hv + num * num) by (nonlinear_arith)
        requires
            VU == V * ((1 + T) * (1 + T)),
            hv == X * X * V - 4 * T,
            num == 2 * S * (1 + T),
            T == S * S,
    ;
    lemma_cong_add_multiple(num * num, (1 + T) * (1 + T), hv);
    lemma_cong_mul(vu as int, X * X, VU, X * X);
    lemma_cong_canonical_zero(x);
    lemma_invsqrt_of_square(vu, num, X);
    let big_i = nat_invsqrt(vu);
    let I = big_i as int;
    lemma_cong_mul(I * I, vu as int, I * I, VU);
    let hi = I * I * VU - 1;
    lemma_cong_diff_zero(I * I * VU, 1);

    // y_dec ≡ y.
    let dx = field_mul(big_i, u2);
    lemma_cong_fmul(big_i, u2, I, 1 + T);
    let dxv = field_mul(dx, v);
    lemma_cong_fmul(dx, v, I * (1 + T), V);
    let dy = field_mul(big_i, dxv);
    lemma_cong_fmul(big_i, dxv, I, I * (1 + T) * V);
    let y_dec = field_mul(u1, dy);
    let Yd = (1 - T) * (I * (I * (1 + T) * V));
    lemma_cong_fmul(u1, dy, 1 - T, I * (I * (1 + T) * V));
    let J = I * I * V;
    let P = 1 + T;
    assert(Yd == (1 - T) * P * J) by (nonlinear_arith)
        requires
            Yd == (1 - T) * (I * (I * (1 + T) * V)),
            J == I * I * V,
            P == 1 + T,
    ;
    assert(hi == J * (P * P) - 1) by (nonlinear_arith)
        requires
            hi == I * I * VU - 1,
            VU == V * ((1 + T) * (1 + T)),
            J == I * I * V,
            P == 1 + T,
    ;
    assert(hs == Y * P - (1 - T)) by (nonlinear_arith)
        requires
            hs == T * K - (1 - Y),
            K == 1 + Y,
            P == 1 + T,
    ;
    lemma_id_decode_yd(Y, T, J, hs);
    lemma_cong_combo2(2 * Y - hs, hi, -1 - Yd, hs);
    lemma_cong_diff_zero(2 * Yd, 2 * Y);
    lemma_cong_cancel(2, Yd, Y);
    lemma_mod_bound((u1 * dy) as int, p() as int);
    lemma_cong_canonical_eq(y_dec, y);

    // x_tmp² ≡ x², so |x_tmp| = x.
    let s2 = field_add(s, s);
    lemma_cong_fadd(s, s, S, S);
    let x_tmp = field_mul(s2, dx);
    let Xt = (S + S) * (I * (1 + T));
    lemma_cong_fmul(s2, dx, S + S, I * (1 + T));
    assert(V * (Xt * Xt) == 4 * T * (J * (P * P))) by (nonlinear_arith)
        requires
            Xt == (S + S) * (I * (1 + T)),
            J == I * I * V,
            P == 1 + T,
            T == S * S,
    ;
    assert(V * (Xt * Xt - X * X) == V * (Xt * Xt) - X * X * V) by (nonlinear_arith);
    assert((4 * T) * hi == 4 * T * (J * (P * P)) - 4 * T) by (nonlinear_arith)
        requires
            hi == J * (P * P) - 1,
    ;
    assert(V * (Xt * Xt - X * X) == (4 * T) * hi - hv);
    lemma_cong_combo2(4 * T, hi, -1, hv);
    assert((4 * T) * hi + (-1) * hv == (4 * T) * hi - hv);
    lemma_cong_mul_zero(V, Xt * Xt - X * X);
    lemma_cong_diff_zero(Xt * Xt, X * X);
    lemma_cong_mul(x_tmp as int, x_tmp as int, Xt, Xt);
    // x_tmp² ≡ x², and |x_tmp| and x are even square roots of x², so |x_tmp| = x.
    lemma_mod_bound((s2 * dx) as int, p() as int);
    lemma_small_mod(x_tmp, p());
    assert(field_square(x_tmp) == field_square(x));
    if is_negative(x_tmp) {
        lemma_neg_square_eq(x_tmp);
        lemma_conditional_negate_makes_even(x_tmp, true);
        lemma_mod_bound((p() - x_tmp) as int, p() as int);
        lemma_nonneg_square_root_unique(field_neg(x_tmp), x);
    } else {
        lemma_nonneg_square_root_unique(x_tmp, x);
    }
}

// =============================================================================
// Constants and coset helpers
// =============================================================================
/// c = INVSQRT_A_MINUS_D: c²·(−1 − d) ≡ 1, so −1 − d ≢ 0 and 1 + d ≢ 0.
pub proof fn lemma_invsqrt_a_minus_d_cong()
    ensures
        fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D) < p(),
        cong(
            (fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D) as int) * (
            fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D) as int) * (-1 - d_int()),
            1,
        ),
        !cong(-1 - d_int(), 0),
        !cong(1 + d_int(), 0),
{
    lemma_cong_p_facts();
    crate::lemmas::ristretto_lemmas::axioms::lemma_invsqrt_a_minus_d();
    let c = fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D);
    let C = c as int;
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let D = d_int();
    lemma_mod_bound(u64_5_as_nat(u64_constants::INVSQRT_A_MINUS_D.limbs) as int, p() as int);
    let n1 = field_neg(1nat);
    lemma_cong_fneg(1, 1);
    let m = field_sub(n1, d);
    lemma_cong_fsub(n1, d, -1, D);
    let c2 = field_square(c);
    lemma_cong_fsquare(c, C);
    lemma_cong_fmul(c2, m, C * C, -1 - D);
    lemma_small_mod(1, p());
    assert(cong(C * C * (-1 - D), 1));
    if cong(-1 - D, 0) {
        lemma_cong_mul(C * C, -1 - D, C * C, 0);
        assert(C * C * 0 == 0);
        lemma_small_mod(0, p());
    }
    if cong(1 + D, 0) {
        lemma_cong_neg(1 + D, 0);
        assert(-(1 + D) == -1 - D);
    }
}

/// On the curve with x ≢ 0: 1 + y ≢ 0 and 1 − y ≢ 0.
///
/// If y² ≡ 1, the curve equation gives x²·(1 + d) ≡ 0.
pub proof fn lemma_on_curve_y_not_pm1(x: nat, y: nat)
    requires
        is_on_edwards_curve(x, y),
        !cong(x as int, 0),
    ensures
        !cong(1 + (y as int), 0),
        !cong(1 - (y as int), 0),
        !cong((1 + (y as int)) * (1 - (y as int)), 0),
{
    lemma_cong_p_facts();
    lemma_curve_cong(x, y);
    lemma_invsqrt_a_minus_d_cong();
    let X = x as int;
    let Y = y as int;
    let D = d_int();
    let h = (1 + Y) * (1 - Y);
    let hc = curve_poly(X, Y);
    assert(X * X * (1 + D) == (-1) * hc + (D * (X * X) - 1) * h) by (nonlinear_arith)
        requires
            hc == Y * Y - X * X - 1 - D * (X * X * (Y * Y)),
            h == (1 + Y) * (1 - Y),
    ;
    if cong(h, 0) {
        lemma_cong_combo2(-1, hc, D * (X * X) - 1, h);
        lemma_cong_mul_nonzero(X, X);
        lemma_cong_mul_nonzero(X * X, 1 + D);
    }
    if cong(1 + Y, 0) {
        lemma_cong_mul(1 + Y, 1 - Y, 0, 1 - Y);
        assert(0 * (1 - Y) == 0);
    }
    if cong(1 - Y, 0) {
        lemma_cong_mul(1 + Y, 1 - Y, 1 + Y, 0);
        assert((1 + Y) * 0 == 0);
    }
}

/// The rotation (x, y) ↦ (i·y, i·x), the map P ↦ P + T₆ with T₆ = spec_eight_torsion()[6].
pub open spec fn ristretto_rot(x: nat, y: nat) -> (nat, nat) {
    (field_mul(y, sqrt_m1()), field_mul(x, sqrt_m1()))
}

/// pt is one of the four points of the coset (x, y) + E[4], in explicit form:
/// (x, y), (−x, −y), (i·y, i·x), (−i·y, −i·x).
pub open spec fn is_in_explicit_coset(pt: (nat, nat), x: nat, y: nat) -> bool {
    let r = ristretto_rot(x, y);
    pt == (x, y) || pt == (field_neg(x), field_neg(y)) || pt == r || pt == (
        field_neg(r.0),
        field_neg(r.1),
    )
}

/// From A·(1 − Y)·(1 + Y) ≡ 1 and sp² ≡ A·(1 − Y)², derive sp²·(1 + Y) ≡ 1 − Y.
proof fn lemma_s_relation_core(sp: int, Y: int, A: int)
    requires
        cong(sp * sp, A * ((1 - Y) * (1 - Y))),
        cong(A * ((1 - Y) * (1 + Y)), 1),
    ensures
        cong(sp * sp * (1 + Y), 1 - Y),
{
    // s²·(1 + Y) ≡ A·L²·(1 + Y) = L·(A·L·(1 + Y)) ≡ L, with L = 1 − Y.
    let L = 1 - Y;
    lemma_cong_mul(sp * sp, 1 + Y, A * (L * L), 1 + Y);
    assert(A * (L * L) * (1 + Y) == L * (A * (L * (1 + Y)))) by (nonlinear_arith);
    lemma_cong_mul(L, A * (L * (1 + Y)), L, 1);
}

/// curve_poly depends only on the squares of its arguments.
pub proof fn lemma_curve_poly_cong(a: int, b: int, a2: int, b2: int)
    requires
        cong(a * a, a2),
        cong(b * b, b2),
    ensures
        cong(curve_poly(a, b), b2 - a2 - 1 - d_int() * (a2 * b2)),
{
    let D = d_int();
    lemma_cong_sub(b * b, a * a, b2, a2);
    lemma_cong_sub(b * b - a * a, 1, b2 - a2, 1);
    lemma_cong_mul(a * a, b * b, a2, b2);
    lemma_cong_mul(D, a * a * (b * b), D, a2 * b2);
    lemma_cong_sub(b * b - a * a - 1, D * (a * a * (b * b)), b2 - a2 - 1, D * (a2 * b2));
}

/// Negation (x, y) ↦ (−x, −y) keeps a point on the curve.
pub proof fn lemma_neg_both_on_curve(x: nat, y: nat)
    requires
        is_on_edwards_curve(x, y),
    ensures
        is_on_edwards_curve(field_neg(x), field_neg(y)),
{
    let X = x as int;
    let Y = y as int;
    lemma_cong_fneg(x, X);
    lemma_cong_fneg(y, Y);
    lemma_cong_mul(field_neg(x) as int, field_neg(x) as int, -X, -X);
    lemma_cong_mul(field_neg(y) as int, field_neg(y) as int, -Y, -Y);
    assert((-X) * (-X) == X * X) by (nonlinear_arith);
    assert((-Y) * (-Y) == Y * Y) by (nonlinear_arith);
    lemma_curve_poly_cong(field_neg(x) as int, field_neg(y) as int, X * X, Y * Y);
    lemma_curve_cong(x, y);
    lemma_curve_cong(field_neg(x), field_neg(y));
}

/// Rotation (x, y) ↦ (i·y, i·x) keeps a point on the curve.
pub proof fn lemma_rot_on_curve(x: nat, y: nat)
    requires
        is_on_edwards_curve(x, y),
    ensures
        is_on_edwards_curve(ristretto_rot(x, y).0, ristretto_rot(x, y).1),
{
    lemma_sqrt_m1_cong();
    let i = sqrt_m1();
    let Ii = i as int;
    let X = x as int;
    let Y = y as int;
    let a = field_mul(y, i);
    let b = field_mul(x, i);
    lemma_cong_fmul(y, i, Y, Ii);
    lemma_cong_fmul(x, i, X, Ii);
    lemma_cong_mul(a as int, a as int, Y * Ii, Y * Ii);
    lemma_cong_mul(b as int, b as int, X * Ii, X * Ii);
    assert(Y * Ii * (Y * Ii) == (Ii * Ii) * (Y * Y)) by (nonlinear_arith);
    assert(X * Ii * (X * Ii) == (Ii * Ii) * (X * X)) by (nonlinear_arith);
    lemma_cong_mul(Ii * Ii, Y * Y, -1, Y * Y);
    lemma_cong_mul(Ii * Ii, X * X, -1, X * X);
    lemma_curve_poly_cong(a as int, b as int, (-1) * (Y * Y), (-1) * (X * X));
    let D = d_int();
    assert((-1) * (X * X) - (-1) * (Y * Y) - 1 - D * (((-1) * (Y * Y)) * ((-1) * (X * X)))
        == curve_poly(X, Y)) by (nonlinear_arith)
        requires
            D == d_int(),
    ;
    lemma_curve_cong(x, y);
    lemma_curve_cong(a, b);
}

/// The last part of the encoder, shared by the two rotation cases.
///
/// Inputs: the (possibly rotated) point (xr, yr) and the denominator dn, with
/// dn²·(1 − yr²) ≡ 1. Let (X, Y) = (−xr, −yr) if xr is negative, else (xr, yr). The
/// encoder outputs s = |dn·(1 − Y)|. Returns (s, X, Y), with s²·(1 + Y) ≡ 1 − Y.
proof fn lemma_encode_tail(xr: nat, yr: nat, dn: nat) -> (r: (nat, nat, nat))
    requires
        xr < p(),
        yr < p(),
        dn < p(),
        xr != 0,
        yr != 0,
        is_on_edwards_curve(xr, yr),
        cong((dn as int) * (dn as int) * (1 - (yr as int) * (yr as int)), 1),
    ensures
        ({
            let neg2 = is_negative(xr);
            let yf = if neg2 {
                field_neg(yr)
            } else {
                yr
            };
            let s = field_mul(dn, field_sub(1, yf));
            let sf = if is_negative(s) {
                field_neg(s)
            } else {
                s
            };
            r == (
                sf,
                if neg2 {
                    field_neg(xr)
                } else {
                    xr
                },
                yf,
            )
        }),
        r.0 < p(),
        r.0 % 2 == 0,
        r.1 < p(),
        r.2 < p(),
        r.1 % 2 == 0,
        r.1 != 0,
        r.2 != 0,
        field_mul(r.1, r.2) == field_mul(xr, yr),
        is_on_edwards_curve(r.1, r.2),
        cong((r.0 as int) * (r.0 as int) * (1 + (r.2 as int)), 1 - (r.2 as int)),
        !cong(1 + (r.2 as int), 0),
        !cong(1 - (r.2 as int), 0),
{
    lemma_cong_p_facts();
    let Xr = xr as int;
    let Yr = yr as int;
    let Dn = dn as int;
    lemma_small_mod(xr, p());
    lemma_small_mod(yr, p());
    let neg2 = is_negative(xr);
    let yf = if neg2 {
        field_neg(yr)
    } else {
        yr
    };
    let xf = if neg2 {
        field_neg(xr)
    } else {
        xr
    };
    let Y = yf as int;
    let X = xf as int;
    lemma_cong_fneg(xr, Xr);
    lemma_cong_fneg(yr, Yr);
    lemma_neg_parity(xr);
    lemma_neg_parity(yr);
    // X, Y facts.
    if neg2 {
        lemma_neg_both_on_curve(xr, yr);
        lemma_cong_fmul(xf, yf, -Xr, -Yr);
        lemma_cong_fmul(xr, yr, Xr, Yr);
        assert((-Xr) * (-Yr) == Xr * Yr) by (nonlinear_arith);
        lemma_mod_bound((xf * yf) as int, p() as int);
        lemma_mod_bound((xr * yr) as int, p() as int);
        lemma_cong_canonical_eq(field_mul(xf, yf), field_mul(xr, yr));
        lemma_cong_mul(Y, Y, -Yr, -Yr);
        assert((-Yr) * (-Yr) == Yr * Yr) by (nonlinear_arith);
    }
    assert(cong(Y * Y, Yr * Yr));
    lemma_small_mod(xf, p());
    assert(X % 2 == 0);
    lemma_cong_canonical_zero(xf);
    lemma_on_curve_y_not_pm1(xf, yf);
    // s ≡ dn·(1 − Y), and |s|² ≡ s².
    let om = field_sub(1, yf);
    lemma_cong_fsub(1, yf, 1, Y);
    let s = field_mul(dn, om);
    lemma_cong_fmul(dn, om, Dn, 1 - Y);
    lemma_mod_bound((dn * om) as int, p() as int);
    let sf = if is_negative(s) {
        field_neg(s)
    } else {
        s
    };
    let SF = sf as int;
    let S = s as int;
    lemma_small_mod(s, p());
    if is_negative(s) {
        lemma_neg_parity(s);
        lemma_cong_fneg(s, S);
        lemma_cong_mul(SF, SF, -S, -S);
        assert((-S) * (-S) == S * S) by (nonlinear_arith);
    }
    lemma_small_mod(sf, p());
    lemma_cong_mul(S, S, Dn * (1 - Y), Dn * (1 - Y));
    assert(Dn * (1 - Y) * (Dn * (1 - Y)) == (Dn * Dn) * ((1 - Y) * (1 - Y))) by (nonlinear_arith);
    // A·(1 − Y)(1 + Y) ≡ 1 with A = dn².
    assert((1 - Y) * (1 + Y) == 1 - Y * Y) by (nonlinear_arith);
    lemma_cong_sub(1, Y * Y, 1, Yr * Yr);
    lemma_cong_mul(Dn * Dn, (1 - Y) * (1 + Y), Dn * Dn, 1 - Yr * Yr);
    lemma_s_relation_core(SF, Y, Dn * Dn);
    lemma_mod_bound((p() - yr) as int, p() as int);
    lemma_mod_bound((p() - xr) as int, p() as int);
    (sf, xf, yf)
}

/// The encoder on an affine point with x·y ≠ 0 whose u1 = 1 − y² is a square.
///
/// The square is given by a witness: u1·den² ≡ num² with den ≢ 0.
/// Returns (s, X, Y): the encoding is the bytes of s, and (X, Y) is the
/// representative of the coset that the encoder selects.
pub proof fn lemma_compress_representative(x: nat, y: nat, num: int, den: int) -> (r: (
    nat,
    nat,
    nat,
))
    requires
        x < p(),
        y < p(),
        x != 0,
        y != 0,
        is_on_edwards_curve(x, y),
        !cong(den, 0),
        cong((1 + (y as int)) * (1 - (y as int)) * (den * den), num * num),
    ensures
        ristretto_compress_affine(x, y) == u8_32_from_nat(r.0),
        r.0 < p(),
        r.0 % 2 == 0,
        r.1 < p(),
        r.2 < p(),
        r.1 % 2 == 0,
        r.1 != 0,
        r.2 != 0,
        !is_negative(field_mul(r.1, r.2)),
        is_on_edwards_curve(r.1, r.2),
        is_in_explicit_coset((r.1, r.2), x, y),
        cong((r.0 as int) * (r.0 as int) * (1 + (r.2 as int)), 1 - (r.2 as int)),
        !cong(1 + (r.2 as int), 0),
        !cong(1 - (r.2 as int), 0),
{
    lemma_cong_p_facts();
    lemma_sqrt_m1_cong();
    lemma_invsqrt_a_minus_d_cong();
    let X0 = x as int;
    let Y0 = y as int;
    let D = d_int();
    let i = sqrt_m1();
    let Ii = i as int;
    let c = fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D);
    let C = c as int;
    lemma_cong_canonical_zero(x);
    lemma_cong_canonical_zero(y);
    lemma_on_curve_y_not_pm1(x, y);
    let u1p = (1 + Y0) * (1 - Y0);
    let xy = X0 * Y0;
    // Encoder intermediates (Z = 1, T = x·y).
    let opy = field_add(1, y);
    lemma_cong_fadd(1, y, 1, Y0);
    let omy = field_sub(1, y);
    lemma_cong_fsub(1, y, 1, Y0);
    let u1 = field_mul(opy, omy);
    lemma_cong_fmul(opy, omy, 1 + Y0, 1 - Y0);
    let u2 = field_mul(x, y);
    lemma_cong_fmul(x, y, X0, Y0);
    lemma_mod_bound((x * y) as int, p() as int);
    let t = u2;
    let u2sq = field_square(u2);
    lemma_cong_fsquare(u2, xy);
    let vu = field_mul(u1, u2sq);
    let VU = u1p * (xy * xy);
    lemma_cong_fmul(u1, u2sq, u1p, xy * xy);
    lemma_mod_bound((u1 * u2sq) as int, p() as int);
    lemma_cong_mul_nonzero(X0, Y0);
    lemma_cong_mul_nonzero(xy, xy);
    lemma_cong_mul_nonzero(u1p, xy * xy);
    // vu·den² ≡ (num·x·y)².
    assert(VU * (den * den) == (u1p * (den * den)) * (xy * xy)) by (nonlinear_arith)
        requires
            VU == u1p * (xy * xy),
    ;
    lemma_cong_mul(u1p * (den * den), xy * xy, num * num, xy * xy);
    assert((num * num) * (xy * xy) == (num * xy) * (num * xy)) by (nonlinear_arith);
    lemma_cong_mul(vu as int, den * den, VU, den * den);
    lemma_invsqrt_of_square(vu, num * xy, den);
    let big_i = nat_invsqrt(vu);
    let I = big_i as int;
    lemma_cong_mul(I * I, vu as int, I * I, VU);
    assert(cong(I * I * VU, 1));
    // z_inv = 1.
    let i1 = field_mul(big_i, u1);
    lemma_cong_fmul(big_i, u1, I, u1p);
    let i2 = field_mul(big_i, u2);
    lemma_cong_fmul(big_i, u2, I, xy);
    let i2t = field_mul(i2, t);
    lemma_cong_fmul(i2, t, I * xy, xy);
    let z_inv = field_mul(i1, i2t);
    lemma_cong_fmul(i1, i2t, I * u1p, I * xy * xy);
    assert(I * u1p * (I * xy * xy) == I * I * VU) by (nonlinear_arith)
        requires
            VU == u1p * (xy * xy),
    ;
    lemma_mod_bound((i1 * i2t) as int, p() as int);
    lemma_small_mod(1, p());
    lemma_cong_canonical_eq(z_inv, 1);
    // field_mul(a, 1) == a for reduced a.
    assert(forall|a: nat| a < p() ==> #[trigger] field_mul(a, 1) == a) by {
        assert forall|a: nat| a < p() implies #[trigger] field_mul(a, 1) == a by {
            lemma_small_mod(a, p());
        }
    }
    let rotate = is_negative(field_mul(t, z_inv));
    assert(rotate == is_negative(t));
    let iX = field_mul(x, i);
    let iY = field_mul(y, i);
    lemma_cong_fmul(x, i, X0, Ii);
    lemma_cong_fmul(y, i, Y0, Ii);
    lemma_mod_bound((x * i) as int, p() as int);
    lemma_mod_bound((y * i) as int, p() as int);
    let ench = field_mul(i1, c);
    lemma_cong_fmul(i1, c, I * u1p, C);
    lemma_mod_bound((i1 * c) as int, p() as int);
    lemma_mod_bound((big_i * u2) as int, p() as int);
    let r = if !rotate {
        lemma_den_cond_nonrot(i2, I, x, y);
        lemma_encode_tail(x, y, i2)
    } else {
        lemma_rot_on_curve(x, y);
        lemma_cong_mul_nonzero(Y0, Ii);
        lemma_cong_mul_nonzero(X0, Ii);
        lemma_cong_canonical_zero(iX);
        lemma_cong_canonical_zero(iY);
        lemma_den_cond_rot(ench, I, x, y);
        lemma_encode_tail(iY, iX, ench)
    };
    // XY ≥ 0.
    lemma_cong_canonical_zero(t);
    if rotate {
        // XY ≡ (i·y)(i·x) ≡ −x·y, and x·y is odd, so −x·y is even.
        lemma_cong_fmul(iY, iX, Y0 * Ii, X0 * Ii);
        assert(Y0 * Ii * (X0 * Ii) == (Ii * Ii) * xy) by (nonlinear_arith)
            requires
                xy == X0 * Y0,
        ;
        lemma_cong_mul(Ii * Ii, xy, -1, xy);
        lemma_cong_fneg(t, xy);
        lemma_mod_bound((iY * iX) as int, p() as int);
        lemma_mod_bound((p() - t) as int, p() as int);
        lemma_cong_canonical_eq(field_mul(iY, iX), field_neg(t));
        lemma_neg_parity(t);
    }
    // Coset membership.

    lemma_neg_parity(x);
    lemma_neg_parity(y);
    r
}

proof fn lemma_id_double_g(A2: int, B2: int, D: int)
    ensures
        ({
            let m = A2 * B2;
            let dxp = 1 + D * m;
            let hq = B2 - A2 - 1 - D * m;
            (1 - D * m) * (1 - D * m) - (B2 + A2) * (B2 + A2) == (-1 - D) * (4 * m) + (-hq) * (dxp
                + (B2 - A2))
        }),
{
    let m = A2 * B2;
    let dxp = 1 + D * m;
    let hq = B2 - A2 - 1 - D * m;
    let dm = D * m;
    assert((1 - dm) * (1 - dm) == 1 - 2 * dm + dm * dm) by (nonlinear_arith);
    assert((B2 + A2) * (B2 + A2) == B2 * B2 + 2 * m + A2 * A2) by (nonlinear_arith)
        requires
            m == A2 * B2,
    ;
    assert((-hq) * (dxp + (B2 - A2)) == (1 + dm - (B2 - A2)) * (1 + dm + (B2 - A2)));
    assert((1 + dm - (B2 - A2)) * (1 + dm + (B2 - A2)) == (1 + dm) * (1 + dm) - (B2 - A2) * (B2
        - A2)) by (nonlinear_arith);
    assert((1 + dm) * (1 + dm) == 1 + 2 * dm + dm * dm) by (nonlinear_arith);
    assert((B2 - A2) * (B2 - A2) == B2 * B2 - 2 * m + A2 * A2) by (nonlinear_arith)
        requires
            m == A2 * B2,
    ;
    assert((-1 - D) * (4 * m) == -4 * dm - 4 * m) by (nonlinear_arith)
        requires
            dm == D * m,
    ;
}

/// For (x, y) = 2·q, the encoder value u1 = 1 − y² is a square.
///
/// With q = (a, b), Dx = 1 + d·a²b² and Dy = 1 − d·a²b²: x·Dx ≡ 2ab and
/// y·Dy ≡ a² + b². The curve equation for q gives
/// (1 − y²)·Dy² ≡ (−1 − d)·(x·Dx)², and (−1 − d) = 1/c² with c = INVSQRT_A_MINUS_D.
/// Returns w = (x·Dx, c·Dy), with w.1 ≢ 0 and (1 − y²)·w.1² ≡ w.0².
pub proof fn lemma_double_u1_square(x: nat, y: nat, q: (nat, nat)) -> (w: (int, int))
    requires
        is_on_edwards_curve(q.0, q.1),
        (x, y) == edwards_scalar_mul(q, 2),
    ensures
        !cong(w.1, 0),
        cong((1 + (y as int)) * (1 - (y as int)) * (w.1 * w.1), w.0 * w.0),
{
    lemma_cong_p_facts();
    lemma_invsqrt_a_minus_d_cong();
    crate::lemmas::edwards_lemmas::curve_equation_lemmas::lemma_double_is_scalar_mul_2(q);
    let D = d_int();
    let C = fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D) as int;
    let (a, b) = q;
    let (A, B) = (a as int, b as int);
    let (xv, yv) = (x as int, y as int);
    let M = A * A * (B * B);
    // x·Dx ≡ 2ab and y·Dy ≡ a² + b², with Dx = 1 + d·M ≢ 0 and Dy = 1 − d·M ≢ 0.
    lemma_edwards_add_cong(a, b, a, b);
    lemma_edwards_add_denominators_cong(a, b, a, b);
    let DX = 1 + D * M;
    let DY = 1 - D * M;
    // (1 − y²)·Dy² ≡ Dy² − (y·Dy)² ≡ (1 − d·M)² − (a² + b²)².
    assert((1 + yv) * (1 - yv) * (DY * DY) == DY * DY - (yv * DY) * (yv * DY)) by (nonlinear_arith);
    lemma_cong_mul(yv * DY, yv * DY, B * B + A * A, B * B + A * A);
    lemma_cong_sub(
        DY * DY,
        (yv * DY) * (yv * DY),
        (1 - D * M) * (1 - D * M),
        (B * B + A * A) * (B * B + A * A),
    );
    lemma_id_double_g(A * A, B * B, D);
    let hq = curve_poly(A, B);
    lemma_curve_cong(a, b);
    assert(hq == B * B - A * A - 1 - D * M);
    lemma_cong_add_multiple((-1 - D) * (4 * M), -(1 + D * M + (B * B - A * A)), hq);
    assert((-hq) * (1 + D * M + (B * B - A * A)) == -(1 + D * M + (B * B - A * A)) * hq)
        by (nonlinear_arith);
    // (x·Dx)² ≡ (2ab)² = 4·M.
    lemma_cong_mul(xv * DX, xv * DX, A * B + B * A, A * B + B * A);
    assert((A * B + B * A) * (A * B + B * A) == 4 * M) by (nonlinear_arith)
        requires
            M == A * A * (B * B),
    ;
    // Multiply by c²: (1 − y²)·(c·Dy)² ≡ c²·(−1 − d)·(x·Dx)² ≡ (x·Dx)².
    let u1p = (1 + yv) * (1 - yv);
    lemma_cong_mul(C * C, u1p * (DY * DY), C * C, (-1 - D) * (4 * M));
    assert(C * C * ((-1 - D) * (4 * M)) == (C * C * (-1 - D)) * (4 * M)) by (nonlinear_arith);
    lemma_cong_mul(C * C * (-1 - D), 4 * M, 1, (xv * DX) * (xv * DX));
    assert(u1p * ((C * DY) * (C * DY)) == C * C * (u1p * (DY * DY))) by (nonlinear_arith);
    // den = c·Dy ≢ 0.
    assert(!cong(C, 0)) by {
        if cong(C, 0) {
            lemma_small_mod(1, p());
            lemma_small_mod(0, p());
            assert(0int * 0int == 0);
            assert(0 * (-1 - D) == 0);
            lemma_cong_mul(C, C, 0, 0);
            lemma_cong_mul(C * C, -1 - D, 0, -1 - D);
        }
    }
    lemma_cong_mul_nonzero(C, DY);
    (xv * DX, C * DY)
}

// =============================================================================
// Decompress of an encoding
// =============================================================================
/// Decoding s = 0 gives the identity (0, 1).
pub proof fn lemma_decode_zero()
    ensures
        ristretto_decode_inner(0) == (0nat, 1nat, true),
{
    lemma_cong_p_facts();
    lemma_invsqrt_a_minus_d_cong();
    crate::lemmas::ristretto_lemmas::axioms::lemma_invsqrt_a_minus_d();
    lemma_small_mod(0, p());
    lemma_small_mod(1, p());
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let D = d_int();
    let c = fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D);
    let C = c as int;
    let ss = field_square(0);
    assert(ss == 0);
    let u1 = field_sub(1, ss);
    lemma_cong_fsub(1, ss, 1, 0);
    lemma_mod_bound((1 + p()) as int, p() as int);
    lemma_cong_canonical_eq(u1, 1);
    let u2 = field_add(1, ss);
    assert(u2 == 1);
    let u2_sqr = field_square(u2);
    assert(u2_sqr == 1);
    let neg_d = field_neg(d);
    let u1_sqr = field_square(u1);
    assert(u1_sqr == 1);
    let v = field_sub(field_mul(neg_d, u1_sqr), u2_sqr);
    lemma_cong_fneg(d, D);
    lemma_cong_fmul(neg_d, u1_sqr, -D, 1);
    lemma_cong_fsub(field_mul(neg_d, u1_sqr), u2_sqr, -D * 1, 1);
    let vu = field_mul(v, u2_sqr);
    lemma_cong_fmul(v, u2_sqr, -D * 1 - 1, 1);
    // vu == field_sub(field_neg(1), d)
    let target = field_sub(field_neg(1nat), d);
    lemma_cong_fneg(1, 1);
    lemma_cong_fsub(field_neg(1nat), d, -1, D);
    lemma_mod_bound((v * u2_sqr) as int, p() as int);
    lemma_mod_bound(
        (field_canonical(field_neg(1nat)) + p() - field_canonical(d)) as int,
        p() as int,
    );
    assert((-D * 1 - 1) * 1 == -1 - D);
    lemma_cong_canonical_eq(vu, target);
    assert(nat_invsqrt(vu) == c);
    // ok: c²·vu ≡ 1.
    lemma_cong_mul(C * C, vu as int, C * C, -1 - D);
    lemma_mod_bound((c * c * vu) as int, p() as int);
    assert(is_sqrt_ratio(1, vu, c));
    // Dx = c, Dy = c·(c·v) ≡ 1.
    let dx = field_mul(c, u2);
    lemma_cong_fmul(c, u2, C, 1);
    lemma_mod_bound((c * u2) as int, p() as int);
    lemma_cong_canonical_eq(dx, c);
    let dxv = field_mul(dx, v);
    lemma_cong_fmul(dx, v, C, -1 - D);
    let dy = field_mul(c, dxv);
    lemma_cong_fmul(c, dxv, C, C * (-1 - D));
    assert(C * (C * (-1 - D)) == C * C * (-1 - D)) by (nonlinear_arith);
    lemma_mod_bound((c * dxv) as int, p() as int);
    lemma_cong_canonical_eq(dy, 1);
    let x_tmp = field_mul(field_add(0, 0), dx);
    assert(field_add(0, 0) == 0);
    assert(0 * dx == 0);
    assert(x_tmp == 0);
    let y = field_mul(u1, dy);
    assert(y == 1);
}

/// The decompress result for the bytes of s, when s is a valid encoding of a
/// representative (x, y) with x·y ≥ 0 and y ≠ 0.
pub proof fn lemma_decompress_of_representative(s: nat, x: nat, y: nat)
    requires
        s < p(),
        s % 2 == 0,
        ristretto_decode_inner(s) == (x, y, true),
        !is_negative(field_mul(x, y)),
        y != 0,
    ensures
        spec_ristretto_decompress(u8_32_from_nat(s)) == Some((x, y, 1nat, field_mul(x, y))),
{
    lemma_bytes_of_canonical(s);
    lemma_small_mod(s, p());
}

// =============================================================================
// Main theorem: round trip
// =============================================================================
/// On the curve with x·y = 0, the point is in E[4], and its coset contains (0, 1).
pub proof fn lemma_zero_xy_coset_contains_identity(x: nat, y: nat)
    requires
        x < p(),
        y < p(),
        is_on_edwards_curve(x, y),
        x == 0 || y == 0,
    ensures
        is_in_explicit_coset((0nat, 1nat), x, y),
{
    use crate::lemmas::edwards_lemmas::torsion_lemmas::*;
    if x == 0 {
        lemma_on_curve_x_zero_implies_y_pm_one(x, y);
    }
    if y == 0 {
        lemma_on_curve_y_zero_implies_x_sq_neg_one(x, y);
    }
    crate::lemmas::ristretto_lemmas::coset_lemmas::lemma_edge_coset_contains_e4(x, y);
    lemma_explicit_coset_iff_coset_affine((0nat, 1nat), x, y);
}

/// Round trip: for (x, y) on the curve with (x, y) = 2·q, decompressing
/// the encoding of (x, y) succeeds, and the decoded point (X, Y, 1, X·Y) has
/// (X, Y) in the coset (x, y) + E[4].
///
/// Reference: RFC 9496 §4.3.1, §4.3.2; Hamburg, "Decaf" §4.
pub proof fn lemma_ristretto_compress_roundtrip(x: nat, y: nat, q: (nat, nat))
    requires
        x < p(),
        y < p(),
        is_on_edwards_curve(x, y),
        is_on_edwards_curve(q.0, q.1),
        (x, y) == edwards_scalar_mul(q, 2),
    ensures
        spec_ristretto_decompress(ristretto_compress_affine(x, y)) is Some,
        ({
            let (dx, dy, dz, dt) = spec_ristretto_decompress(
                ristretto_compress_affine(x, y),
            ).unwrap();
            &&& dz == 1
            &&& dt == field_mul(dx, dy)
            &&& is_in_explicit_coset((dx, dy), x, y)
            &&& is_on_edwards_curve(dx, dy)
        }),
{
    lemma_cong_p_facts();
    if x == 0 || y == 0 {
        assert(field_mul(x, y) % p() == 0) by {
            assert(x * y == 0);
            lemma_small_mod(0, p());
        }
        crate::lemmas::ristretto_lemmas::batch_compress_lemmas::lemma_ristretto_compress_affine_zero_xy(
        x, y);
        lemma_decode_zero();
        lemma_small_mod(0, p());
        assert(field_mul(0, 1) == 0);
        lemma_decompress_of_representative(0, 0, 1);
        lemma_zero_xy_coset_contains_identity(x, y);
        crate::lemmas::edwards_lemmas::curve_equation_lemmas::lemma_identity_on_curve();
    } else {
        let w = lemma_double_u1_square(x, y, q);
        let r = lemma_compress_representative(x, y, w.0, w.1);
        lemma_decode_of_representative(r.0, r.1, r.2);
        lemma_decompress_of_representative(r.0, r.1, r.2);
    }
}

// =============================================================================
// The coset maps form the cyclic group generated by the rotation
// =============================================================================
/// The four maps P ↦ P + T for T in E[4], as ristretto_rot^k: k = 0 identity,
/// 1 rotation (+T₆), 2 negation (+T₄), 3 negated rotation (+T₂), with
/// T_j = spec_eight_torsion()[j].
pub open spec fn coset_map(k: nat, pt: (nat, nat)) -> (nat, nat) {
    let r = ristretto_rot(pt.0, pt.1);
    if k == 0 {
        pt
    } else if k == 1 {
        r
    } else if k == 2 {
        (field_neg(pt.0), field_neg(pt.1))
    } else {
        (field_neg(r.0), field_neg(r.1))
    }
}

/// Coordinate rules: −(−a) = a, (−a)·i = −(a·i), (a·i)·i = −a.
proof fn lemma_coset_rules(a: nat)
    requires
        a < p(),
    ensures
        field_neg(field_neg(a)) == a,
        field_mul(field_neg(a), sqrt_m1()) == field_neg(field_mul(a, sqrt_m1())),
        field_mul(field_mul(a, sqrt_m1()), sqrt_m1()) == field_neg(a),
        field_neg(a) < p(),
        field_mul(a, sqrt_m1()) < p(),
{
    p_gt_2();
    lemma_small_mod(a, p());
    lemma_field_neg_neg(a);
    lemma_field_neg_mul_left(a, sqrt_m1());
    lemma_mul_i_squared_is_neg(a);
    lemma_mod_bound((p() - field_canonical(a)) as int, p() as int);
    lemma_mod_bound((a * sqrt_m1()) as int, p() as int);
}

/// coset_map(g, coset_map(h, pt)) = coset_map((g + h) mod 4, pt).
pub proof fn lemma_coset_map_compose(g: nat, h: nat, pt: (nat, nat))
    requires
        g < 4,
        h < 4,
        pt.0 < p(),
        pt.1 < p(),
    ensures
        coset_map(g, coset_map(h, pt)) == coset_map((g + h) % 4, pt),
        coset_map(h, pt).0 < p(),
        coset_map(h, pt).1 < p(),
{
    let i = sqrt_m1();
    let (x, y) = pt;
    lemma_coset_rules(x);
    lemma_coset_rules(y);
    lemma_coset_rules(field_neg(x));
    lemma_coset_rules(field_neg(y));
    lemma_coset_rules(field_mul(x, i));
    lemma_coset_rules(field_mul(y, i));
    lemma_coset_rules(field_neg(field_mul(x, i)));
    lemma_coset_rules(field_neg(field_mul(y, i)));
}

/// Membership in the explicit coset, as an index k < 4.
pub proof fn lemma_explicit_coset_index(a: (nat, nat), x: nat, y: nat) -> (k: nat)
    requires
        is_in_explicit_coset(a, x, y),
    ensures
        k < 4,
        a == coset_map(k, (x, y)),
{
    if a == (x, y) {
        0
    } else if a == ristretto_rot(x, y) {
        1
    } else if a == (field_neg(x), field_neg(y)) {
        2
    } else {
        3
    }
}

/// Symmetry: a in coset(e) implies e in coset(a).
pub proof fn lemma_explicit_coset_symmetric(a: (nat, nat), e: (nat, nat))
    requires
        e.0 < p(),
        e.1 < p(),
        is_in_explicit_coset(a, e.0, e.1),
    ensures
        is_in_explicit_coset(e, a.0, a.1),
        a.0 < p(),
        a.1 < p(),
{
    let k = lemma_explicit_coset_index(a, e.0, e.1);
    let kinv = ((4 - k) % 4) as nat;
    lemma_coset_map_compose(kinv, k, e);
    assert((kinv + k) % 4 == 0);
}

/// Transitivity: a in coset(b) and b in coset(e) imply a in coset(e).
pub proof fn lemma_explicit_coset_transitive(a: (nat, nat), b: (nat, nat), e: (nat, nat))
    requires
        e.0 < p(),
        e.1 < p(),
        is_in_explicit_coset(a, b.0, b.1),
        is_in_explicit_coset(b, e.0, e.1),
    ensures
        is_in_explicit_coset(a, e.0, e.1),
{
    let kb = lemma_explicit_coset_index(b, e.0, e.1);
    let ka = lemma_explicit_coset_index(a, b.0, b.1);
    lemma_coset_map_compose(ka, kb, e);
}

// =============================================================================
// Link to ristretto_coset_affine
// =============================================================================
/// Adding a point (a, b) with a·b = 0: the denominators are 1, so
/// (x, y) + (a, b) = (x·b + y·a, y·b + x·a).
proof fn lemma_edwards_add_e4(x: nat, y: nat, a: nat, b: nat)
    requires
        cong((a as int) * (b as int), 0),
    ensures
        cong(edwards_add(x, y, a, b).0 as int, (x as int) * (b as int) + (y as int) * (a as int)),
        cong(edwards_add(x, y, a, b).1 as int, (y as int) * (b as int) + (x as int) * (a as int)),
        edwards_add(x, y, a, b).0 < p(),
        edwards_add(x, y, a, b).1 < p(),
{
    lemma_cong_p_facts();
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let (X, Y, A, B) = (x as int, y as int, a as int, b as int);
    let x1x2 = field_mul(x, a);
    let y1y2 = field_mul(y, b);
    let x1y2 = field_mul(x, b);
    let y1x2 = field_mul(y, a);
    lemma_cong_fmul(x, a, X, A);
    lemma_cong_fmul(y, b, Y, B);
    lemma_cong_fmul(x, b, X, B);
    lemma_cong_fmul(y, a, Y, A);
    let m = field_mul(x1x2, y1y2);
    lemma_cong_fmul(x1x2, y1y2, X * A, Y * B);
    let t = field_mul(d, m);
    lemma_cong_fmul(d, m, d_int(), X * A * (Y * B));
    assert(d_int() * (X * A * (Y * B)) == (d_int() * X * Y) * (A * B)) by (nonlinear_arith);
    lemma_cong_mul(d_int() * X * Y, A * B, d_int() * X * Y, 0);
    assert(d_int() * X * Y * 0 == 0);
    lemma_mod_bound((d * m) as int, p() as int);
    lemma_small_mod(0, p());
    lemma_cong_canonical_eq(t, 0);
    lemma_small_mod(1, p());
    let dx = field_add(1, t);
    let dy = field_sub(1, t);
    assert(dx == 1);
    lemma_cong_fsub(1, t, 1, 0);
    lemma_mod_bound((1 + p()) as int, p() as int);
    lemma_cong_canonical_eq(dy, 1);
    lemma_field_inv_one();
    let nx = field_add(x1y2, y1x2);
    lemma_cong_fadd(x1y2, y1x2, X * B, Y * A);
    let ny = field_add(y1y2, x1x2);
    lemma_cong_fadd(y1y2, x1x2, Y * B, X * A);
    lemma_cong_fmul(nx, 1, X * B + Y * A, 1);
    lemma_cong_fmul(ny, 1, Y * B + X * A, 1);
    lemma_mod_bound((nx * 1) as int, p() as int);
    lemma_mod_bound((ny * 1) as int, p() as int);
}

/// With P = (x, y), ristretto_coset_affine(x, y) = [P, P + T₂, P + T₄, P + T₆] is
/// [P, coset_map(3, P), coset_map(2, P), coset_map(1, P)].
pub proof fn lemma_coset_affine_explicit(x: nat, y: nat)
    requires
        x < p(),
        y < p(),
    ensures
        ristretto_coset_affine(x, y) == [
            (x, y),
            coset_map(3, (x, y)),
            coset_map(2, (x, y)),
            coset_map(1, (x, y)),
        ],
{
    use crate::lemmas::edwards_lemmas::torsion_lemmas::lemma_four_torsion_affine;
    lemma_cong_p_facts();
    lemma_sqrt_m1_cong();
    lemma_four_torsion_affine();
    let i = sqrt_m1();
    let Ii = i as int;
    let (X, Y) = (x as int, y as int);
    let ni = field_neg(i);
    let n1 = field_neg(1nat);
    lemma_cong_fneg(i, Ii);
    lemma_cong_fneg(1, 1);
    lemma_small_mod(0, p());
    assert(-Ii * 0 == 0);
    assert(0 * -1 == 0);
    assert(Ii * 0 == 0);
    lemma_cong_mul(ni as int, 0, -Ii, 0);
    lemma_cong_mul(0, n1 as int, 0, -1);
    lemma_edwards_add_e4(x, y, ni, 0);
    lemma_edwards_add_e4(x, y, 0, n1);
    lemma_edwards_add_e4(x, y, i, 0);
    let c = ristretto_coset_affine(x, y);
    let r = ristretto_rot(x, y);
    lemma_coset_rules(x);
    lemma_coset_rules(y);
    // P + T₂ = (−y·i, −x·i).
    lemma_cong_fmul(y, i, Y, Ii);
    lemma_cong_fmul(x, i, X, Ii);
    lemma_cong_fneg(r.0, Y * Ii);
    lemma_cong_fneg(r.1, X * Ii);
    assert(X * 0 + Y * (-Ii) == -(Y * Ii)) by (nonlinear_arith);
    assert(Y * 0 + X * (-Ii) == -(X * Ii)) by (nonlinear_arith);
    lemma_cong_mul(Y, ni as int, Y, -Ii);
    lemma_cong_mul(X, ni as int, X, -Ii);
    lemma_cong_add(X * 0, Y * (ni as int), X * 0, Y * (-Ii));
    lemma_cong_add(Y * 0, X * (ni as int), Y * 0, X * (-Ii));
    lemma_mod_bound((p() - field_canonical(r.0)) as int, p() as int);
    lemma_mod_bound((p() - field_canonical(r.1)) as int, p() as int);
    lemma_cong_canonical_eq(c[1].0, field_neg(r.0));
    lemma_cong_canonical_eq(c[1].1, field_neg(r.1));
    // P + T₄ = (−x, −y).
    lemma_cong_fneg(x, X);
    lemma_cong_fneg(y, Y);
    lemma_cong_mul(X, n1 as int, X, -1);
    lemma_cong_mul(Y, n1 as int, Y, -1);
    lemma_cong_add(X * (n1 as int), Y * 0, X * -1, Y * 0);
    lemma_cong_add(Y * (n1 as int), X * 0, Y * -1, X * 0);
    assert(X * -1 + Y * 0 == -X);
    assert(Y * -1 + X * 0 == -Y);
    lemma_mod_bound((p() - field_canonical(x)) as int, p() as int);
    lemma_mod_bound((p() - field_canonical(y)) as int, p() as int);
    lemma_cong_canonical_eq(c[2].0, field_neg(x));
    lemma_cong_canonical_eq(c[2].1, field_neg(y));
    // P + T₆ = (y·i, x·i).
    assert(X * 0 + Y * Ii == Y * Ii);
    assert(Y * 0 + X * Ii == X * Ii);
    lemma_mod_bound((y * i) as int, p() as int);
    lemma_mod_bound((x * i) as int, p() as int);
    lemma_cong_canonical_eq(c[3].0, r.0);
    lemma_cong_canonical_eq(c[3].1, r.1);
}

/// is_in_explicit_coset is membership in ristretto_coset_affine.
pub proof fn lemma_explicit_coset_iff_coset_affine(a: (nat, nat), x: nat, y: nat)
    requires
        x < p(),
        y < p(),
    ensures
        is_in_explicit_coset(a, x, y) <==> (a == ristretto_coset_affine(x, y)[0] || a
            == ristretto_coset_affine(x, y)[1] || a == ristretto_coset_affine(x, y)[2] || a
            == ristretto_coset_affine(x, y)[3]),
{
    lemma_coset_affine_explicit(x, y);
}

// =============================================================================
// Injectivity on classes
// =============================================================================
/// Corollary: two points of 2E with the same encoding are in the same coset.
///
/// Both decode to the same point D. D is in the coset of each, so
/// (x1, y1) is in the coset of (x2, y2).
pub proof fn lemma_ristretto_compress_injective(
    x1: nat,
    y1: nat,
    q1: (nat, nat),
    x2: nat,
    y2: nat,
    q2: (nat, nat),
)
    requires
        x1 < p(),
        y1 < p(),
        is_on_edwards_curve(x1, y1),
        is_on_edwards_curve(q1.0, q1.1),
        (x1, y1) == edwards_scalar_mul(q1, 2),
        x2 < p(),
        y2 < p(),
        is_on_edwards_curve(x2, y2),
        is_on_edwards_curve(q2.0, q2.1),
        (x2, y2) == edwards_scalar_mul(q2, 2),
        ristretto_compress_affine(x1, y1) == ristretto_compress_affine(x2, y2),
    ensures
        is_in_explicit_coset((x1, y1), x2, y2),
        (x1, y1) == ristretto_coset_affine(x2, y2)[0] || (x1, y1) == ristretto_coset_affine(
            x2,
            y2,
        )[1] || (x1, y1) == ristretto_coset_affine(x2, y2)[2] || (x1, y1) == ristretto_coset_affine(
            x2,
            y2,
        )[3],
{
    lemma_ristretto_compress_roundtrip(x1, y1, q1);
    lemma_ristretto_compress_roundtrip(x2, y2, q2);
    let dec = spec_ristretto_decompress(ristretto_compress_affine(x1, y1)).unwrap();
    let d = (dec.0, dec.1);
    lemma_explicit_coset_symmetric(d, (x1, y1));
    lemma_explicit_coset_transitive((x1, y1), d, (x2, y2));
    lemma_explicit_coset_iff_coset_affine((x1, y1), x2, y2);
}

// =============================================================================
// The four points of a coset have the same encoding
// =============================================================================
/// Uniqueness of the representative: if a and b are in the coset of e, both have X ≥ 0 and
/// X·Y ≥ 0, and a.0 ≠ 0 and a.1 ≠ 0, then a = b. (The coset of the identity has no such a.)
///
/// Within a coset, negation flips the sign of X, and rotation maps X·Y to
/// −X·Y. A nonzero value and its negation have different signs.
pub proof fn lemma_representative_unique(a: (nat, nat), b: (nat, nat), e: (nat, nat))
    requires
        e.0 < p(),
        e.1 < p(),
        is_in_explicit_coset(a, e.0, e.1),
        is_in_explicit_coset(b, e.0, e.1),
        a.0 % 2 == 0,
        b.0 % 2 == 0,
        a.0 != 0,
        a.1 != 0,
        !is_negative(field_mul(a.0, a.1)),
        !is_negative(field_mul(b.0, b.1)),
    ensures
        a == b,
{
    lemma_cong_p_facts();
    lemma_sqrt_m1_cong();
    lemma_explicit_coset_symmetric(a, e);
    lemma_explicit_coset_symmetric(b, e);
    lemma_explicit_coset_transitive(b, e, a);
    let k = lemma_explicit_coset_index(b, a.0, a.1);
    let i = sqrt_m1();
    let Ii = i as int;
    let (A0, A1) = (a.0 as int, a.1 as int);
    let pa = field_mul(a.0, a.1);
    lemma_cong_fmul(a.0, a.1, A0, A1);
    lemma_mod_bound((a.0 * a.1) as int, p() as int);
    lemma_cong_canonical_zero(a.0);
    lemma_cong_canonical_zero(a.1);
    lemma_cong_mul_nonzero(A0, A1);
    lemma_cong_canonical_zero(pa);
    lemma_small_mod(pa, p());
    if k == 2 {
        lemma_neg_parity(a.0);
        lemma_small_mod(a.0, p());
        lemma_small_mod(b.0, p());
    } else if k == 1 || k == 3 {
        // b.0·b.1 ≡ (±a.1·i)(±a.0·i) ≡ −a.0·a.1.
        let r = ristretto_rot(a.0, a.1);
        lemma_cong_fmul(a.1, i, A1, Ii);
        lemma_cong_fmul(a.0, i, A0, Ii);
        let (B0, B1) = (b.0 as int, b.1 as int);
        if k == 1 {
            lemma_cong_mul(B0, B1, A1 * Ii, A0 * Ii);
        } else {
            lemma_cong_fneg(r.0, A1 * Ii);
            lemma_cong_fneg(r.1, A0 * Ii);
            lemma_cong_mul(B0, B1, -(A1 * Ii), -(A0 * Ii));
            assert(-(A1 * Ii) * -(A0 * Ii) == A1 * Ii * (A0 * Ii)) by (nonlinear_arith);
        }
        assert(A1 * Ii * (A0 * Ii) == (Ii * Ii) * (A0 * A1)) by (nonlinear_arith);
        lemma_cong_mul(Ii * Ii, A0 * A1, -1, A0 * A1);
        lemma_cong_fmul(b.0, b.1, B0, B1);
        lemma_cong_fneg(pa, A0 * A1);
        lemma_mod_bound((b.0 * b.1) as int, p() as int);
        lemma_mod_bound((p() - field_canonical(pa)) as int, p() as int);
        assert(-1 * (A0 * A1) == -(A0 * A1));
        lemma_cong_canonical_eq(field_mul(b.0, b.1), field_neg(pa));
        lemma_neg_parity(pa);
        lemma_small_mod(field_neg(pa), p());
    }
}

/// For P = (x, y) with x·y ≠ 0 and (qx, qy) = coset_map(k, P): if (1 − y²)·den² ≡ num²
/// with den ≢ 0, then w satisfies (1 − qy²)·w.1² ≡ w.0² with w.1 ≢ 0.
proof fn lemma_coset_u1_square(x: nat, y: nat, num: int, den: int, k: nat) -> (w: (int, int))
    requires
        x < p(),
        y < p(),
        x != 0,
        y != 0,
        k < 4,
        is_on_edwards_curve(x, y),
        !cong(den, 0),
        cong((1 + (y as int)) * (1 - (y as int)) * (den * den), num * num),
    ensures
        !cong(w.1, 0),
        cong(
            (1 + (coset_map(k, (x, y)).1 as int)) * (1 - (coset_map(k, (x, y)).1 as int)) * (w.1
                * w.1),
            w.0 * w.0,
        ),
{
    lemma_cong_p_facts();
    lemma_sqrt_m1_cong();
    lemma_invsqrt_a_minus_d_cong();
    let i = sqrt_m1();
    let Ii = i as int;
    let (X, Y) = (x as int, y as int);
    let D = d_int();
    let c = fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D);
    let C = c as int;
    let qy = coset_map(k, (x, y)).1;
    let QY = qy as int;
    let u1p = (1 + Y) * (1 - Y);
    assert((1 + QY) * (1 - QY) == 1 - QY * QY) by (nonlinear_arith);
    assert(u1p == 1 - Y * Y) by (nonlinear_arith)
        requires
            u1p == (1 + Y) * (1 - Y),
    ;
    lemma_cong_fmul(x, i, X, Ii);
    lemma_cong_fneg(y, Y);
    lemma_cong_fneg(field_mul(x, i), X * Ii);
    if k == 0 || k == 2 {
        // qy = ±y, so 1 − qy² ≡ 1 − y².
        if k == 2 {
            lemma_cong_mul(QY, QY, -Y, -Y);
            assert((-Y) * (-Y) == Y * Y) by (nonlinear_arith);
        }
        assert(cong(QY * QY, Y * Y));
        lemma_cong_sub(1, QY * QY, 1, Y * Y);
        lemma_cong_mul(1 - QY * QY, den * den, u1p, den * den);
        (num, den)
    } else {
        // qy = ±x·i, so 1 − qy² ≡ 1 + x².
        if k == 3 {
            lemma_cong_mul(QY, QY, -(X * Ii), -(X * Ii));
            assert(-(X * Ii) * -(X * Ii) == X * Ii * (X * Ii)) by (nonlinear_arith);
        } else {
            lemma_cong_mul(QY, QY, X * Ii, X * Ii);
        }
        assert(X * Ii * (X * Ii) == (Ii * Ii) * (X * X)) by (nonlinear_arith);
        lemma_cong_mul(Ii * Ii, X * X, -1, X * X);
        lemma_cong_sub(1, QY * QY, 1, -1 * (X * X));
        assert(1 - -1 * (X * X) == 1 + X * X);
        lemma_u1_rot_cong(x, y);
        // (1 + x²)·(c·num)² ≡ (1 + x²)·c²·u1·den² ≡ c²(−1 − d)·(x·y·den)² ≡ (x·y·den)².
        let n2 = X * Y * den;
        let d2 = C * num;
        lemma_cong_mul(1 - QY * QY, d2 * d2, 1 + X * X, d2 * d2);
        assert((1 + X * X) * (d2 * d2) == (C * C) * ((1 + X * X) * (num * num)))
            by (nonlinear_arith)
            requires
                d2 == C * num,
        ;
        lemma_cong_mul(1 + X * X, num * num, 1 + X * X, u1p * (den * den));
        assert((1 + X * X) * (u1p * (den * den)) == (u1p * (1 + X * X)) * (den * den))
            by (nonlinear_arith);
        lemma_cong_mul(u1p * (1 + X * X), den * den, (X * X * (Y * Y)) * (-1 - D), den * den);
        lemma_cong_mul(
            C * C,
            (1 + X * X) * (num * num),
            C * C,
            (X * X * (Y * Y)) * (-1 - D) * (den * den),
        );
        assert((C * C) * ((X * X * (Y * Y)) * (-1 - D) * (den * den)) == (C * C * (-1 - D)) * (n2
            * n2)) by (nonlinear_arith)
            requires
                n2 == X * Y * den,
        ;
        lemma_cong_mul(C * C * (-1 - D), n2 * n2, 1, n2 * n2);
        // c·num ≢ 0: num² ≡ u1·den² ≢ 0 and c ≢ 0.
        lemma_cong_canonical_zero(x);
        lemma_on_curve_y_not_pm1(x, y);
        lemma_cong_mul_nonzero(den, den);
        lemma_cong_mul_nonzero(u1p, den * den);
        assert(!cong(num, 0)) by {
            if cong(num, 0) {
                lemma_cong_mul(num, num, 0, 0);
                assert(0int * 0int == 0);
            }
        }
        assert(!cong(C, 0)) by {
            if cong(C, 0) {
                lemma_small_mod(1, p());
                lemma_small_mod(0, p());
                assert(0int * 0int == 0);
                assert(0 * (-1 - D) == 0);
                lemma_cong_mul(C, C, 0, 0);
                lemma_cong_mul(C * C, -1 - D, 0, -1 - D);
            }
        }
        lemma_cong_mul_nonzero(C, num);
        (n2, d2)
    }
}

/// With P = (x, y), coset_map(m, P) = (u, v) is on the curve and reduced, and u·v ≡ ±x·y.
pub proof fn lemma_coset_map_props(m: nat, x: nat, y: nat)
    requires
        m < 4,
        x < p(),
        y < p(),
        is_on_edwards_curve(x, y),
    ensures
        coset_map(m, (x, y)).0 < p(),
        coset_map(m, (x, y)).1 < p(),
        is_on_edwards_curve(coset_map(m, (x, y)).0, coset_map(m, (x, y)).1),
        cong(
            (coset_map(m, (x, y)).0 as int) * (coset_map(m, (x, y)).1 as int),
            (x as int) * (y as int),
        ) || cong(
            (coset_map(m, (x, y)).0 as int) * (coset_map(m, (x, y)).1 as int),
            -((x as int) * (y as int)),
        ),
{
    lemma_cong_p_facts();
    lemma_sqrt_m1_cong();
    lemma_coset_map_compose(0, m, (x, y));
    let qq = coset_map(m, (x, y));
    let i = sqrt_m1();
    let Ii = i as int;
    let (X, Y) = (x as int, y as int);
    let (QX, QY) = (qq.0 as int, qq.1 as int);
    lemma_cong_fmul(x, i, X, Ii);
    lemma_cong_fmul(y, i, Y, Ii);
    lemma_cong_fneg(x, X);
    lemma_cong_fneg(y, Y);
    lemma_cong_fneg(field_mul(x, i), X * Ii);
    lemma_cong_fneg(field_mul(y, i), Y * Ii);
    if m == 2 {
        lemma_cong_mul(QX, QY, -X, -Y);
        assert((-X) * (-Y) == X * Y) by (nonlinear_arith);
        lemma_neg_both_on_curve(x, y);
    } else if m == 1 || m == 3 {
        lemma_rot_on_curve(x, y);
        if m == 1 {
            lemma_cong_mul(QX, QY, Y * Ii, X * Ii);
        } else {
            let r = ristretto_rot(x, y);
            lemma_neg_both_on_curve(r.0, r.1);
            lemma_cong_mul(QX, QY, -(Y * Ii), -(X * Ii));
            assert(-(Y * Ii) * -(X * Ii) == Y * Ii * (X * Ii)) by (nonlinear_arith);
        }
        assert(Y * Ii * (X * Ii) == (Ii * Ii) * (X * Y)) by (nonlinear_arith);
        lemma_cong_mul(Ii * Ii, X * Y, -1, X * Y);
        assert(-1 * (X * Y) == -(X * Y));
    }
}

/// For x·y ≠ 0: coset_map(m, (x, y)) and (x, y) have the same encoding.
proof fn lemma_coset_same_encoding_nonzero(x: nat, y: nat, q: (nat, nat), m: nat)
    requires
        x < p(),
        y < p(),
        x != 0,
        y != 0,
        m < 4,
        is_on_edwards_curve(x, y),
        is_on_edwards_curve(q.0, q.1),
        (x, y) == edwards_scalar_mul(q, 2),
    ensures
        ristretto_compress_affine(coset_map(m, (x, y)).0, coset_map(m, (x, y)).1)
            == ristretto_compress_affine(x, y),
{
    lemma_cong_p_facts();
    let qq = coset_map(m, (x, y));
    let (X, Y) = (x as int, y as int);
    let (QX, QY) = (qq.0 as int, qq.1 as int);
    lemma_coset_map_props(m, x, y);
    let w = lemma_double_u1_square(x, y, q);
    let wq = lemma_coset_u1_square(x, y, w.0, w.1, m);
    lemma_cong_canonical_zero(x);
    lemma_cong_canonical_zero(y);
    lemma_cong_mul_nonzero(X, Y);
    assert(!cong(QX * QY, 0)) by {
        if cong(QX * QY, 0) && cong(QX * QY, -(X * Y)) {
            assert(cong(-(X * Y), 0));
            lemma_cong_neg(-(X * Y), 0);
            assert(--(X * Y) == X * Y);
        }
    }
    assert(qq.0 != 0 && qq.1 != 0) by {
        lemma_small_mod(0, p());
        if qq.0 == 0 {
            lemma_mul_by_zero_is_zero(QY);
        }
        if qq.1 == 0 {
            lemma_mul_by_zero_is_zero(QX);
        }
    }
    let rp = lemma_compress_representative(x, y, w.0, w.1);
    let rq = lemma_compress_representative(qq.0, qq.1, wq.0, wq.1);
    // Both representatives are in the coset of P, so they are equal.
    lemma_explicit_coset_transitive((rq.1, rq.2), qq, (x, y));
    lemma_representative_unique((rp.1, rp.2), (rq.1, rq.2), (x, y));
    // s_P² ≡ s_Q², and both are even and reduced.
    let (sp, sq) = (rp.0 as int, rq.0 as int);
    let yy = rp.2 as int;
    lemma_cong_diff_zero(sp * sp * (1 + yy), sq * sq * (1 + yy));
    assert(sp * sp * (1 + yy) == (1 + yy) * (sp * sp)) by (nonlinear_arith);
    assert(sq * sq * (1 + yy) == (1 + yy) * (sq * sq)) by (nonlinear_arith);
    lemma_cong_cancel(1 + yy, sp * sp, sq * sq);
    lemma_cong_fsquare(rp.0, sp);
    lemma_cong_fsquare(rq.0, sq);
    lemma_mod_bound((rp.0 * rp.0) as int, p() as int);
    lemma_mod_bound((rq.0 * rq.0) as int, p() as int);
    lemma_cong_canonical_eq(field_square(rp.0), field_square(rq.0));
    lemma_nonneg_square_root_unique(rp.0, rq.0);
}

/// The four points of the coset (x, y) + E[4] of a point of 2E have the same encoding.
pub proof fn lemma_ristretto_coset_same_encoding(x: nat, y: nat, q: (nat, nat), k: int)
    requires
        x < p(),
        y < p(),
        is_on_edwards_curve(x, y),
        is_on_edwards_curve(q.0, q.1),
        (x, y) == edwards_scalar_mul(q, 2),
        0 <= k < 4,
    ensures
        ristretto_compress_affine(
            ristretto_coset_affine(x, y)[k].0,
            ristretto_coset_affine(x, y)[k].1,
        ) == ristretto_compress_affine(x, y),
{
    lemma_cong_p_facts();
    lemma_coset_affine_explicit(x, y);
    let m: nat = if k == 0 {
        0
    } else if k == 1 {
        3
    } else if k == 2 {
        2
    } else {
        1
    };
    let qq = coset_map(m, (x, y));
    assert(ristretto_coset_affine(x, y)[k] == qq);
    if x == 0 || y == 0 {
        // Both encodings are the zero encoding.
        lemma_coset_map_props(m, x, y);
        let (X, Y) = (x as int, y as int);
        let (QX, QY) = (qq.0 as int, qq.1 as int);
        assert(X * Y == 0) by {
            assert(x * y == 0);
        }
        assert(-(X * Y) == 0);
        lemma_cong_fmul(qq.0, qq.1, QX, QY);
        lemma_mod_bound((qq.0 * qq.1) as int, p() as int);
        lemma_small_mod(0, p());
        lemma_cong_canonical_eq(field_mul(qq.0, qq.1), 0);
        assert(field_mul(x, y) % p() == 0) by {
            assert(x * y == 0);
        }
        crate::lemmas::ristretto_lemmas::batch_compress_lemmas::lemma_ristretto_compress_affine_zero_xy(
        x, y);
        crate::lemmas::ristretto_lemmas::batch_compress_lemmas::lemma_ristretto_compress_affine_zero_xy(
        qq.0, qq.1);
    } else {
        lemma_coset_same_encoding_nonzero(x, y, q, m);
    }
}

/// On the curve, (1 + y)(1 − y)·(1 + x²) ≡ x²y²·(−1 − d).
proof fn lemma_u1_rot_cong(x: nat, y: nat)
    requires
        is_on_edwards_curve(x, y),
    ensures
        ({
            let (X, Y) = (x as int, y as int);
            cong((1 + Y) * (1 - Y) * (1 + X * X), (X * X * (Y * Y)) * (-1 - d_int()))
        }),
{
    let (X, Y) = (x as int, y as int);
    let D = d_int();
    let hc = curve_poly(X, Y);
    lemma_curve_cong(x, y);
    assert((1 + Y) * (1 - Y) * (1 + X * X) == (X * X * (Y * Y)) * (-1 - D) + (-1) * hc)
        by (nonlinear_arith)
        requires
            hc == Y * Y - X * X - 1 - D * (X * X * (Y * Y)),
    ;
    lemma_cong_add_multiple((X * X * (Y * Y)) * (-1 - D), -1, hc);
}

/// With u1 = (1 + y)(1 − y): dn ≡ J·x·y and J²·u1·(x·y)² ≡ 1 give dn²·(1 − y²) ≡ 1
/// (no rotation).
proof fn lemma_den_cond_nonrot(dn: nat, J: int, x: nat, y: nat)
    requires
        cong(dn as int, J * ((x as int) * (y as int))),
        cong(
            J * J * ((1 + (y as int)) * (1 - (y as int)) * (((x as int) * (y as int)) * ((x as int)
                * (y as int)))),
            1,
        ),
    ensures
        cong((dn as int) * (dn as int) * (1 - (y as int) * (y as int)), 1),
{
    let (X0, Y0) = (x as int, y as int);
    let xy = X0 * Y0;
    let u1p = (1 + Y0) * (1 - Y0);
    let VU = u1p * (xy * xy);
    lemma_cong_mul(dn as int, dn as int, J * xy, J * xy);
    assert(J * xy * (J * xy) * (1 - Y0 * Y0) == J * J * VU) by (nonlinear_arith)
        requires
            VU == u1p * (xy * xy),
            u1p == (1 + Y0) * (1 - Y0),
    ;
    lemma_cong_mul((dn as int) * (dn as int), 1 - Y0 * Y0, J * xy * (J * xy), 1 - Y0 * Y0);
}

/// With u1 = (1 + y)(1 − y) and c = INVSQRT_A_MINUS_D: dn ≡ J·u1·c and J²·u1·(x·y)² ≡ 1
/// give dn²·(1 − (x·i)²) ≡ 1 (rotation).
proof fn lemma_den_cond_rot(dn: nat, J: int, x: nat, y: nat)
    requires
        is_on_edwards_curve(x, y),
        cong(
            dn as int,
            J * ((1 + (y as int)) * (1 - (y as int))) * (fe51_as_canonical_nat(
                &u64_constants::INVSQRT_A_MINUS_D,
            ) as int),
        ),
        cong(
            J * J * ((1 + (y as int)) * (1 - (y as int)) * (((x as int) * (y as int)) * ((x as int)
                * (y as int)))),
            1,
        ),
    ensures
        cong(
            (dn as int) * (dn as int) * (1 - (field_mul(x, sqrt_m1()) as int) * (field_mul(
                x,
                sqrt_m1(),
            ) as int)),
            1,
        ),
{
    lemma_cong_p_facts();
    lemma_sqrt_m1_cong();
    lemma_invsqrt_a_minus_d_cong();
    let i = sqrt_m1();
    let Ii = i as int;
    let D = d_int();
    let C = fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D) as int;
    let (X0, Y0) = (x as int, y as int);
    let xy = X0 * Y0;
    let u1p = (1 + Y0) * (1 - Y0);
    let VU = u1p * (xy * xy);
    let iX = field_mul(x, i);
    lemma_cong_fmul(x, i, X0, Ii);
    let Yr = iX as int;
    lemma_cong_mul(Yr, Yr, X0 * Ii, X0 * Ii);
    assert(X0 * Ii * (X0 * Ii) == (Ii * Ii) * (X0 * X0)) by (nonlinear_arith);
    lemma_cong_mul(Ii * Ii, X0 * X0, -1, X0 * X0);
    lemma_cong_sub(1, Yr * Yr, 1, (-1) * (X0 * X0));
    let Dn = dn as int;
    let E = J * u1p * C;
    lemma_cong_mul(Dn, Dn, E, E);
    lemma_cong_mul(Dn * Dn, 1 - Yr * Yr, E * E, 1 - (-1) * (X0 * X0));
    let P1 = J * J;
    let P2 = C * C;
    assert(E * E * (1 - (-1) * (X0 * X0)) == (P1 * P2 * u1p) * (u1p * (1 + X0 * X0)))
        by (nonlinear_arith)
        requires
            E == J * u1p * C,
            P1 == J * J,
            P2 == C * C,
    ;
    lemma_u1_rot_cong(x, y);
    let Q = X0 * X0 * (Y0 * Y0);
    lemma_cong_mul(P1 * P2 * u1p, u1p * (1 + X0 * X0), P1 * P2 * u1p, Q * (-1 - D));
    assert(xy * xy == Q) by (nonlinear_arith)
        requires
            xy == X0 * Y0,
            Q == X0 * X0 * (Y0 * Y0),
    ;
    assert(P1 * P2 * u1p * (Q * (-1 - D)) == (P1 * (u1p * Q)) * (P2 * (-1 - D)))
        by (nonlinear_arith);
    assert(J * J * VU == P1 * (u1p * Q));
    lemma_cong_mul(P1 * (u1p * Q), P2 * (-1 - D), 1, 1);
}

} // verus!
