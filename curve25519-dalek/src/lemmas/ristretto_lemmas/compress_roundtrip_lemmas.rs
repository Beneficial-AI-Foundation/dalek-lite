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
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::common_lemmas::to_nat_lemmas::*;
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::lemmas::field_lemmas::field_cong_lemmas::*;
use crate::lemmas::field_lemmas::sqrt_m1_lemmas::*;
use crate::lemmas::field_lemmas::sqrt_ratio_lemmas::*;
use crate::ristretto::RistrettoPoint;
use crate::specs::core_specs::*;
use crate::specs::edwards_specs::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use crate::specs::ristretto_specs::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

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

/// If a·den² ≡ num², a ≢ 0 and den ≢ 0, then nat_invsqrt(a)²·a ≡ 1.
pub proof fn lemma_invsqrt_of_square(a: nat, num: int, den: int)
    requires
        a < p(),
        !cong(a as int, 0),
        !cong(den, 0),
        cong(a * (den * den), num * num),
    ensures
        nat_invsqrt(a) < p(),
        cong((nat_invsqrt(a) * nat_invsqrt(a) * a) as int, 1),
        is_sqrt_ratio(1, a, nat_invsqrt(a)),
{
    lemma_cong_p_facts();
    lemma_small_mod(0, p());
    lemma_small_mod(1, p());
    assert(a % p() != 0);
    lemma_nat_invsqrt_satisfies_relation(a);
    let r = nat_invsqrt(a);
    let R = r as int;
    let A = a as int;
    let i = sqrt_m1();
    if !is_sqrt_ratio(1, a, r) {
        // r²·a ≡ i, so (r·num/den)² ≡ i: i would be a square.
        assert(is_sqrt_ratio_times_i(1, a, r));
        lemma_cong_fmul(i, 1, i as int, 1);
        assert(cong(R * R * A, i as int));
        let dn = (den % (p() as int)) as nat;
        lemma_mod_bound(den, p() as int);
        lemma_mod_twice(den, p() as int);
        assert(!cong(dn as int, 0));
        lemma_cong_inv(dn);
        let di = field_inv(dn);
        let nn = (num % (p() as int)) as nat;
        lemma_mod_bound(num, p() as int);
        lemma_mod_twice(num, p() as int);
        let w = field_mul(field_mul(r, nn), di);
        lemma_cong_fmul(r, nn, R, num);
        lemma_cong_fmul(field_mul(r, nn), di, R * num, di as int);
        lemma_cong_fmul(w, w, R * num * di, R * num * di);
        // (R·num·di)² = (R²·num²)·di² ≡ R²·a·den²·di² = (R²·a)·(di·den)² ≡ i
        let DI = di as int;
        assert(R * num * DI * (R * num * DI) == (R * R) * (num * num) * (DI * DI))
            by (nonlinear_arith);
        lemma_cong_mul(R * R, num * num, R * R, A * (den * den));
        lemma_cong_mul((R * R) * (num * num), DI * DI, (R * R) * (A * (den * den)), DI * DI);
        assert((R * R) * (A * (den * den)) * (DI * DI) == (R * R * A) * ((DI * den) * (DI * den)))
            by (nonlinear_arith);
        lemma_cong_mul(DI, dn as int, DI, den);
        lemma_cong_mul(DI * dn, DI * dn, DI * den, DI * den);
        assert(cong(DI * dn, 1));
        lemma_cong_mul(DI * dn, DI * dn, 1, 1);
        lemma_cong_mul(R * R * A, (DI * den) * (DI * den), i as int, 1);
        assert(cong(field_mul(w, w) as int, i as int));
        lemma_mod_bound((w * w) as int, p() as int);
        lemma_sqrt_m1_limbs_bounded();
        assert(i < p()) by {
            lemma_mod_bound(fe51_as_nat(&crate::constants::SQRT_M1) as int, p() as int);
        }
        lemma_cong_canonical_eq(field_mul(w, w), i);
        lemma_small_mod(i, p());
        assert(field_mul(w, w) == field_canonical(i));
        lemma_sqrt_m1_not_square();
        assert(false);
    }
    assert(cong(R * R * A, 1));
}

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
/// Proof: let K = 1 + y and T = s². Then K·(1 + T) ≡ 2 and K·(1 − T) ≡ 2y,
/// so K²·v ≡ −4·(1 + d·y²) and, with the curve equation, x²·v ≡ 4·T.
/// So v·u2² is a nonzero square, the invsqrt I satisfies I²·v·u2² ≡ 1,
/// y_dec·u2 ≡ u1 gives y_dec ≡ y, and x_tmp² ≡ x² gives |x_tmp| = x.
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
        assert(K * (1 + T) == 2 + 1 * hs) by (nonlinear_arith)
            requires
                hs == T * K - (1 - Y),
                K == 1 + Y,
        ;
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
    lemma_cong_square_eq(x_tmp as int, X);
    lemma_mod_bound((s2 * dx) as int, p() as int);
    lemma_small_mod(x, p());
    lemma_small_mod(x_tmp, p());
    if cong(x_tmp as int, X) {
        lemma_cong_canonical_eq(x_tmp, x);
    } else {
        lemma_cong_fneg(x, X);
        lemma_mod_bound((p() - x) as int, p() as int);
        lemma_cong_canonical_eq(x_tmp, field_neg(x));
        lemma_neg_parity(x);
        lemma_cong_fneg(x_tmp, -X);
        lemma_mod_bound((p() - x_tmp) as int, p() as int);
        assert(--X == X);
        lemma_cong_canonical_eq(field_neg(x_tmp), x);
    }
}

// =============================================================================
// Constants and coset helpers
// =============================================================================
/// i = sqrt(−1): i² ≡ −1, i ≢ 0, i < p.
pub proof fn lemma_sqrt_m1_cong()
    ensures
        sqrt_m1() < p(),
        cong((sqrt_m1() as int) * (sqrt_m1() as int), -1),
        !cong(sqrt_m1() as int, 0),
{
    lemma_cong_p_facts();
    lemma_sqrt_m1_nonzero();
    lemma_sqrt_m1_squared();
    lemma_cong_fneg(1, 1);
    lemma_small_mod(1, p());
    lemma_small_mod((p() - 1) as nat, p());
    lemma_small_mod(0, p());
}

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

/// The rotation (x, y) ↦ (i·y, i·x), the map P ↦ P + T₆.
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

/// From A·(1 − Y)·(1 + Y) ≡ 1 and s² ≡ A·(1 − Y)², derive s²·(1 + Y) ≡ 1 − Y.
proof fn lemma_s_relation_core(sp: int, Y: int, A: int)
    requires
        cong(sp * sp, A * ((1 - Y) * (1 - Y))),
        cong(A * ((1 - Y) * (1 + Y)), 1),
        !cong(1 - Y, 0),
    ensures
        cong(sp * sp * (1 + Y), 1 - Y),
{
    let L = 1 - Y;
    lemma_cong_mul(sp * sp, L * (1 + Y), A * (L * L), L * (1 + Y));
    assert(A * (L * L) * (L * (1 + Y)) == (L * L) * (A * (L * (1 + Y)))) by (nonlinear_arith);
    lemma_cong_mul(L * L, A * (L * (1 + Y)), L * L, 1);
    assert(sp * sp * (L * (1 + Y)) == L * (sp * sp * (1 + Y))) by (nonlinear_arith);
    assert(L * L * 1 == L * L);
    lemma_cong_cancel(L, sp * sp * (1 + Y), L);
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
/// dn²·(1 − yr²) ≡ 1. The encoder negates (xr, yr) when xr < 0 and outputs
/// s = |dn·(1 − Y)|. The result (s, X, Y) satisfies s²·(1 + Y) ≡ 1 − Y.
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
    } else {
        lemma_cong_mul(SF, SF, S, S);
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
        // dn = i2 ≡ I·x·y, so dn²·(1 − y²) ≡ I²·u1·(x·y)² ≡ 1.
        lemma_cong_mul(i2 as int, i2 as int, I * xy, I * xy);
        assert(I * xy * (I * xy) * (1 - Y0 * Y0) == I * I * VU) by (nonlinear_arith)
            requires
                VU == u1p * (xy * xy),
                u1p == (1 + Y0) * (1 - Y0),
        ;
        lemma_cong_mul(i2 as int * i2 as int, 1 - Y0 * Y0, I * xy * (I * xy), 1 - Y0 * Y0);
        lemma_encode_tail(x, y, i2)
    } else {
        // dn = ench ≡ I·u1·c and yr = i·x, so 1 − yr² ≡ 1 + x² and
        // dn²·(1 + x²) ≡ I²·c²·u1·(x²y²·(−1 − d)) ≡ 1.
        lemma_rot_on_curve(x, y);
        lemma_cong_mul_nonzero(Y0, Ii);
        lemma_cong_mul_nonzero(X0, Ii);
        lemma_cong_canonical_zero(iX);
        lemma_cong_canonical_zero(iY);
        let Yr = iX as int;
        lemma_cong_mul(Yr, Yr, X0 * Ii, X0 * Ii);
        assert(X0 * Ii * (X0 * Ii) == (Ii * Ii) * (X0 * X0)) by (nonlinear_arith);
        lemma_cong_mul(Ii * Ii, X0 * X0, -1, X0 * X0);
        lemma_cong_sub(1, Yr * Yr, 1, (-1) * (X0 * X0));
        let Dn = ench as int;
        let E = I * u1p * C;
        lemma_cong_mul(Dn, Dn, E, E);
        lemma_cong_mul(Dn * Dn, 1 - Yr * Yr, E * E, 1 - (-1) * (X0 * X0));
        assert(E * E * (1 - (-1) * (X0 * X0)) == (I * I * C * C * u1p) * (u1p * (1 + X0 * X0)))
            by (nonlinear_arith)
            requires
                E == I * u1p * C,
        ;
        let hc = curve_poly(X0, Y0);
        lemma_curve_cong(x, y);
        assert(u1p * (1 + X0 * X0) == (X0 * X0 * (Y0 * Y0)) * (-1 - D) + (-1) * hc)
            by (nonlinear_arith)
            requires
                u1p == (1 + Y0) * (1 - Y0),
                hc == Y0 * Y0 - X0 * X0 - 1 - D * (X0 * X0 * (Y0 * Y0)),
        ;
        lemma_cong_add_multiple((X0 * X0 * (Y0 * Y0)) * (-1 - D), -1, hc);
        lemma_cong_mul(
            I * I * C * C * u1p,
            u1p * (1 + X0 * X0),
            I * I * C * C * u1p,
            (X0 * X0 * (Y0 * Y0)) * (-1 - D),
        );
        let P1 = I * I;
        let P2 = C * C;
        let Q = X0 * X0 * (Y0 * Y0);
        assert(xy * xy == Q) by (nonlinear_arith)
            requires
                xy == X0 * Y0,
                Q == X0 * X0 * (Y0 * Y0),
        ;
        assert(I * I * C * C * u1p == P1 * P2 * u1p) by (nonlinear_arith)
            requires
                P1 == I * I,
                P2 == C * C,
        ;
        assert(P1 * P2 * u1p * (Q * (-1 - D)) == (P1 * (u1p * Q)) * (P2 * (-1 - D)))
            by (nonlinear_arith);
        assert(I * I * VU == P1 * (u1p * Q));
        assert(C * C * (-1 - D) == P2 * (-1 - D));
        lemma_cong_mul(I * I * VU, C * C * (-1 - D), 1, 1);
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

/// For (x, y) = 2·Q with x·y ≠ 0, the encoder value u1 = 1 − y² is a square.
///
/// With Q = (a, b), Dx = 1 + d·a²b² and Dy = 1 − d·a²b²: x·Dx ≡ 2ab and
/// y·Dy ≡ a² + b². The curve equation for Q gives
/// (1 − y²)·Dy² ≡ (−1 − d)·(x·Dx)², and (−1 − d) = 1/c² with c = INVSQRT_A_MINUS_D.
/// Returns (num, den) = (x·Dx, c·Dy) with (1 − y²)·den² ≡ num².
pub proof fn lemma_double_u1_square(x: nat, y: nat, q: (nat, nat)) -> (w: (int, int))
    requires
        x < p(),
        y < p(),
        x != 0,
        y != 0,
        is_on_edwards_curve(q.0, q.1),
        (x, y) == edwards_scalar_mul(q, 2),
    ensures
        !cong(w.1, 0),
        cong((1 + (y as int)) * (1 - (y as int)) * (w.1 * w.1), w.0 * w.0),
{
    lemma_cong_p_facts();
    lemma_invsqrt_a_minus_d_cong();
    crate::lemmas::edwards_lemmas::curve_equation_lemmas::lemma_double_is_scalar_mul_2(q);
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let D = d_int();
    let c = fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D);
    let C = c as int;
    let a = q.0;
    let b = q.1;
    let A = a as int;
    let B = b as int;
    let xv = x as int;
    let yv = y as int;
    // Lift edwards_add(a, b, a, b).
    let x1x2 = field_mul(a, a);
    lemma_cong_fmul(a, a, A, A);
    let y1y2 = field_mul(b, b);
    lemma_cong_fmul(b, b, B, B);
    let x1y2 = field_mul(a, b);
    lemma_cong_fmul(a, b, A, B);
    let y1x2 = field_mul(b, a);
    lemma_cong_fmul(b, a, B, A);
    let m = field_mul(x1x2, y1y2);
    let M = A * A * (B * B);
    lemma_cong_fmul(x1x2, y1y2, A * A, B * B);
    let tt = field_mul(d, m);
    lemma_cong_fmul(d, m, D, M);
    let dx = field_add(1, tt);
    lemma_cong_fadd(1, tt, 1, D * M);
    let dy = field_sub(1, tt);
    lemma_cong_fsub(1, tt, 1, D * M);
    let nx = field_add(x1y2, y1x2);
    lemma_cong_fadd(x1y2, y1x2, A * B, B * A);
    let ny = field_add(y1y2, x1x2);
    lemma_cong_fadd(y1y2, x1x2, B * B, A * A);
    lemma_mod_bound((1 + tt) as int, p() as int);
    lemma_mod_bound((1 + p() - tt % p()) as int, p() as int);
    lemma_mod_bound(tt as int, p() as int);
    lemma_mod_bound((d * m) as int, p() as int);
    lemma_small_mod(0, p());
    // Dx ≢ 0 and Dy ≢ 0, since otherwise x = 0 or y = 0.
    assert(x == field_mul(nx, field_inv(dx)));
    assert(y == field_mul(ny, field_inv(dy)));
    if cong(dx as int, 0) {
        lemma_small_mod(dx, p());
        assert(dx % p() == 0);
        assert(field_inv(dx) == 0);
        lemma_small_mod(0, p());
        assert(nx * 0 == 0);
        assert(field_mul(nx, 0) == 0);
        assert(x == 0);
    }
    if cong(dy as int, 0) {
        lemma_mod_bound((field_canonical(1) + p() - field_canonical(tt)) as int, p() as int);
        lemma_small_mod(dy, p());
        assert(field_inv(dy) == 0);
        assert(ny * 0 == 0);
        assert(field_mul(ny, 0) == 0);
        assert(y == 0);
    }
    lemma_cong_inv(dx);
    lemma_cong_inv(dy);
    let ix = field_inv(dx) as int;
    let inv_dy = field_inv(dy) as int;
    let DX = dx as int;
    let DY = dy as int;
    // x·Dx ≡ N_x and y·Dy ≡ N_y.
    lemma_cong_fmul(nx, field_inv(dx), A * B + B * A, ix);
    lemma_cong_mul(xv, DX, (A * B + B * A) * ix, DX);
    assert((A * B + B * A) * ix * DX == (A * B + B * A) * (ix * DX)) by (nonlinear_arith);
    lemma_cong_mul(A * B + B * A, ix * DX, A * B + B * A, 1);
    lemma_cong_fmul(ny, field_inv(dy), B * B + A * A, inv_dy);
    lemma_cong_mul(yv, DY, (B * B + A * A) * inv_dy, DY);
    assert((B * B + A * A) * inv_dy * DY == (B * B + A * A) * (inv_dy * DY)) by (nonlinear_arith);
    lemma_cong_mul(B * B + A * A, inv_dy * DY, B * B + A * A, 1);
    // (1 − y²)·Dy² ≡ Dy² − (y·Dy)² ≡ (1 − d·M)² − (a² + b²)².
    assert((1 + yv) * (1 - yv) * (DY * DY) == DY * DY - (yv * DY) * (yv * DY)) by (nonlinear_arith);
    lemma_cong_mul(DY, DY, 1 - D * M, 1 - D * M);
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
    lemma_cong_canonical_zero(dy);
    lemma_cong_mul_nonzero(C, DY);
    (xv * DX, C * DY)
}

// =============================================================================
// Bytes of a nat
// =============================================================================
/// Byte k of n in little-endian order.
pub open spec fn nat_byte(n: nat, k: nat) -> u8 {
    ((n / pow2(k * 8)) % 256) as u8
}

/// The 32 little-endian bytes of n.
pub open spec fn nat_to_bytes32(n: nat) -> [u8; 32] {
    [
        nat_byte(n, 0),
        nat_byte(n, 1),
        nat_byte(n, 2),
        nat_byte(n, 3),
        nat_byte(n, 4),
        nat_byte(n, 5),
        nat_byte(n, 6),
        nat_byte(n, 7),
        nat_byte(n, 8),
        nat_byte(n, 9),
        nat_byte(n, 10),
        nat_byte(n, 11),
        nat_byte(n, 12),
        nat_byte(n, 13),
        nat_byte(n, 14),
        nat_byte(n, 15),
        nat_byte(n, 16),
        nat_byte(n, 17),
        nat_byte(n, 18),
        nat_byte(n, 19),
        nat_byte(n, 20),
        nat_byte(n, 21),
        nat_byte(n, 22),
        nat_byte(n, 23),
        nat_byte(n, 24),
        nat_byte(n, 25),
        nat_byte(n, 26),
        nat_byte(n, 27),
        nat_byte(n, 28),
        nat_byte(n, 29),
        nat_byte(n, 30),
        nat_byte(n, 31),
    ]
}

proof fn lemma_nat_to_bytes32_index(n: nat, k: int)
    requires
        0 <= k < 32,
    ensures
        nat_to_bytes32(n)[k] == nat_byte(n, k as nat),
{
    if k == 0 {
    } else if k == 1 {
    } else if k == 2 {
    } else if k == 3 {
    } else if k == 4 {
    } else if k == 5 {
    } else if k == 6 {
    } else if k == 7 {
    } else if k == 8 {
    } else if k == 9 {
    } else if k == 10 {
    } else if k == 11 {
    } else if k == 12 {
    } else if k == 13 {
    } else if k == 14 {
    } else if k == 15 {
    } else if k == 16 {
    } else if k == 17 {
    } else if k == 18 {
    } else if k == 19 {
    } else if k == 20 {
    } else if k == 21 {
    } else if k == 22 {
    } else if k == 23 {
    } else if k == 24 {
    } else if k == 25 {
    } else if k == 26 {
    } else if k == 27 {
    } else if k == 28 {
    } else if k == 29 {
    } else if k == 30 {
    } else {
        assert(k == 31);
    }
}

proof fn lemma_nat_to_bytes32_rec(n: nat, idx: nat)
    requires
        n < pow2(256),
        idx <= 32,
    ensures
        u8_32_as_nat_rec(&nat_to_bytes32(n), idx) == (n / pow2(idx * 8)) * pow2(idx * 8),
    decreases 32 - idx,
{
    use vstd::arithmetic::power2::*;
    use vstd::arithmetic::mul::*;
    let b = nat_to_bytes32(n);
    lemma_pow2_pos(idx * 8);
    if idx == 32 {
        lemma_small_mod(n, pow2(256));
        assert(idx * 8 == 256);
        lemma_div_basics(n as int);
        vstd::arithmetic::div_mod::lemma_basic_div(n as int, pow2(256) as int);
        assert(n / pow2(256) == 0);
        assert(u8_32_as_nat_rec(&b, idx) == 0);
    } else {
        lemma_nat_to_bytes32_rec(n, idx + 1);
        lemma_nat_to_bytes32_index(n, idx as int);
        let e = idx * 8;
        let w = pow2(e);
        let q = n / w;
        lemma_pow2_adds(e, 8);
        lemma2_to64();
        assert((idx + 1) * 8 == e + 8);
        assert(pow2((idx + 1) * 8) == w * 256);
        lemma_div_denominator(n as int, w as int, 256);
        assert(n / pow2((idx + 1) * 8) == q / 256);
        lemma_mod_bound(q as int, 256);
        assert(b[idx as int] as nat == q % 256);
        lemma_fundamental_div_mod(q as int, 256);
        let lo = q % 256;
        let hi = q / 256;
        assert(q == 256 * hi + lo);
        assert(u8_32_as_nat_rec(&b, idx) == (b[idx as int] as nat) * pow2(idx * 8)
            + u8_32_as_nat_rec(&b, idx + 1));
        assert(u8_32_as_nat_rec(&b, idx + 1) == hi * (w * 256));
        assert(u8_32_as_nat_rec(&b, idx) == lo * w + hi * (w * 256));
        assert(lo * w + hi * (w * 256) == (256 * hi + lo) * w) by (nonlinear_arith);
        assert(u8_32_as_nat_rec(&b, idx) == q * w);
    }
}

/// For n < 2^256, u8_32_from_nat(n) holds the value n.
pub proof fn lemma_u8_32_from_nat_value(n: nat)
    requires
        n < pow2(256),
    ensures
        u8_32_as_nat(&u8_32_from_nat(n)) == n,
{
    let b = nat_to_bytes32(n);
    lemma_nat_to_bytes32_rec(n, 0);
    lemma_u8_32_as_nat_equals_rec(&b);
    assert(pow2(0) == 1) by {
        vstd::arithmetic::power2::lemma2_to64();
    }
    assert(0nat * 8 == 0);
    assert((n / 1nat) * 1nat == n) by (nonlinear_arith);
    lemma_small_mod(n, pow2(256));
    assert(u8_32_as_nat(&b) == n % pow2(256));
}

// =============================================================================
// Decompress of an encoding
// =============================================================================
/// For s < p, the bytes of s decode to the field element s, canonically.
pub proof fn lemma_bytes_of_canonical(s: nat)
    requires
        s < p(),
    ensures
        u8_32_as_nat(&u8_32_from_nat(s)) == s,
        field_element_from_bytes(&u8_32_from_nat(s)) == s,
{
    pow255_gt_19();
    lemma_pow2_strictly_increases(255, 256);
    lemma_u8_32_from_nat_value(s);
    lemma_small_mod(s, pow2(255));
    lemma_small_mod(s, p());
}

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
    assert((-D * 1 - 1) * 1 == -1 - D) by (nonlinear_arith);
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
    lemma_cong_p_facts();
    lemma_sqrt_m1_cong();
    lemma_small_mod(0, p());
    lemma_small_mod(1, p());
    let i = sqrt_m1();
    let Ii = i as int;
    if x == 0 {
        lemma_on_curve_x_zero_implies_y_pm_one(x, y);
        if y != 1 {
            lemma_cong_fneg(0, 0);
            lemma_mod_bound(p() as int, p() as int);
            lemma_cong_canonical_eq(field_neg(0), 0);
            lemma_cong_fneg(1, 1);
            lemma_cong_fneg(field_neg(1), -1);
            lemma_mod_bound((p() - field_canonical(field_neg(1))) as int, p() as int);
            lemma_cong_canonical_eq(field_neg(field_neg(1)), 1);
        }
    } else {
        lemma_on_curve_y_zero_implies_x_sq_neg_one(x, y);
        lemma_sqrt_m1_nonzero();
        assert((x * x) % p() == (p() - 1) as nat) by {
            lemma_small_mod((p() - 1) as nat, p());
        }
        lemma_square_root_of_neg_one(x, i);
        lemma_small_mod(x, p());
        let r = ristretto_rot(x, y);
        assert(r.0 == 0) by {
            assert(y * i == 0);
        }
        lemma_cong_fmul(x, i, x as int, Ii);
        lemma_mod_bound((x * i) as int, p() as int);
        if x == i {
            // r.1 = i² = −1, so −r = (0, 1).
            lemma_cong_fneg(r.1, -1);
            lemma_mod_bound((p() - field_canonical(r.1)) as int, p() as int);
            lemma_cong_canonical_eq(field_neg(r.1), 1);
            lemma_cong_fneg(0, 0);
            lemma_mod_bound(p() as int, p() as int);
            lemma_cong_canonical_eq(field_neg(0), 0);
        } else {
            // x = −i, r.1 = −i² = 1.
            assert(x == (p() - i) as nat);
            lemma_cong_fneg(i, Ii);
            assert(field_neg(i) == x) by {
                lemma_small_mod(i, p());
                lemma_small_mod((p() - i) as nat, p());
            }
            lemma_cong_mul(x as int, Ii, -Ii, Ii);
            assert(-Ii * Ii == -(Ii * Ii)) by (nonlinear_arith);
            lemma_cong_neg(Ii * Ii, -1);
            lemma_cong_canonical_eq(r.1, 1);
        }
    }
}

/// Round trip: for (x, y) on the curve and in 2E (x, y) = 2·Q, decompressing
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

} // verus!
