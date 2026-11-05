//! Lemmas and axioms for Montgomery curve operations.
//!
//! Provides axioms and lemmas for verifying the Montgomery ladder.
//!
//! ## Reference
//!
//! The xDBL and xADD formulas are from:
//! > Craig Costello & Benjamin Smith (2017).
//! > *Montgomery curves and their arithmetic*.
//! > <https://eprint.iacr.org/2017/212.pdf>
//!
//! ## Contents
//!
//! - **Group Axioms**: associativity, identity, inverse for Montgomery curve addition
//! - **xDBL Axiom** (Equation 10): doubling `[2]P` in projective coordinates `(U:W)`
//! - **xADD Axiom** (Equation 9): differential addition `P + Q` given `P - Q`
//! - **Scalar Multiplication Lemmas**: distribution `[m+n]P = [m]P + [n]P`, doubling `[2n]P = [n]P + [n]P`
//! - **Projective Representation Lemmas**: connecting projective `(U:W)` to affine `u = U/W`
//! - **Curve Membership Lemmas**: `montgomery_add`, negation, scalar multiples and the canonical lift
//!   keep points on the curve with reduced coordinates (`is_canonical_montgomery_affine`)
#![allow(unused)]
use crate::constants::{APLUS2_OVER_FOUR, MONTGOMERY_A, MONTGOMERY_A_NEG};
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::specs::edwards_specs::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use crate::specs::montgomery_specs::*;
use crate::specs::primality_specs::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{
    lemma2_to64, lemma2_to64_rest, lemma_pow2_adds, lemma_pow2_strictly_increases, pow2,
};
use vstd::prelude::*;

verus! {

// =============================================================================
// GROUP AXIOMS: properties of the Montgomery curve group structure.
// =============================================================================
/// Axiom: Montgomery addition is associative
/// (P + Q) + R = P + (Q + R)
///
/// Holds only for points on the curve with reduced coordinates.
pub proof fn axiom_montgomery_add_associative(
    P: MontgomeryAffine,
    Q: MontgomeryAffine,
    R: MontgomeryAffine,
)
    requires
        is_canonical_montgomery_affine(P),
        is_canonical_montgomery_affine(Q),
        is_canonical_montgomery_affine(R),
    ensures
        montgomery_add(montgomery_add(P, Q), R) == montgomery_add(P, montgomery_add(Q, R)),
{
    admit();
}

/// Lemma: Left identity element
/// ∞ + P = P
pub proof fn lemma_montgomery_add_identity_left(P: MontgomeryAffine)
    ensures
        montgomery_add(MontgomeryAffine::Infinity, P) == P,
{
}

/// Lemma: Infinity is the identity element (right identity)
/// P + ∞ = P
pub proof fn lemma_montgomery_add_identity(P: MontgomeryAffine)
    ensures
        montgomery_add(P, MontgomeryAffine::Infinity) == P,
{
}

/// Lemma: every point has an inverse
/// P + (-P) = ∞
pub proof fn lemma_montgomery_add_inverse(P: MontgomeryAffine)
    ensures
        montgomery_add(P, montgomery_neg(P)) == MontgomeryAffine::Infinity,
{
    match P {
        MontgomeryAffine::Infinity => {},
        MontgomeryAffine::Finite { u, v } => {
            assert(field_add(v, field_neg(v)) == 0) by {
                lemma_field_sub_self(v);
                lemma_field_sub_eq_add_neg(v, v);
            }
        },
    }
}

// =============================================================================
// X-ONLY PROJECTIVE FORMULAS AND AXIOMS
// Costello–Smith 2017: https://eprint.iacr.org/2017/212.pdf (Equations 9–10)
// =============================================================================
//
// The Montgomery ladder operates on x-coordinates only, using projective (U:W)
// representation where the affine x-coordinate is u = U/W.
//
// Montgomery curve: By² = x(x² + Ax + 1)
// - Affine point: (u, v) where u is x-coord, v is y-coord; plus point at infinity ∞
// - Projective x-only: (U:W) represents affine u = U/W; infinity when W = 0
//
// Notation: uppercase U, W = projective coords; lowercase u = affine coord (u = U/W).
//
// Each formula is modeled as a `spec fn` (the algebraic computation) paired with
// an `axiom` (asserting the computation equals the mathematical operation).
//
// -----------------------------------------------------------------------------
// xDBL (Equation 10): Doubling P → [2]P
// -----------------------------------------------------------------------------
//
// Input:  (U : W) representing point P
// Output: (U' : W') representing [2]P
//
// Preconditions: P is on the curve with reduced coordinates, and (U:W) validly represents P
// (for ∞, requires W = 0 and U ≠ 0).
//
// Formulas:
//   U' = (U + W)² · (U - W)²
//   W' = ((U + W)² - (U - W)²) · ((U - W)² + ((A+2)/4) · ((U + W)² - (U - W)²))
//
pub(crate) open spec fn spec_xdbl_projective(U: nat, W: nat) -> (nat, nat) {
    let t0 = field_add(U, W);  // t0 = U + W
    let t1 = field_sub(U, W);  // t1 = U - W
    let t4 = field_square(t0);  // t4 = (U + W)²
    let t5 = field_square(t1);  // t5 = (U - W)²
    let t6 = field_sub(t4, t5);  // t6 = (U + W)² - (U - W)² = 4·U·W
    let a24 = fe51_as_canonical_nat(&APLUS2_OVER_FOUR);  // a24 = (A+2)/4
    let t13 = field_mul(a24, t6);  // t13 = ((A+2)/4) · 4·U·W
    let t15 = field_add(t13, t5);  // t15 = (U - W)² + ((A+2)/4) · 4·U·W
    let U2 = field_mul(t4, t5);  // U' = (U + W)² · (U - W)²
    let W2 = field_mul(t6, t15);  // W' = 4·U·W · ((U - W)² + ((A+2)/4) · 4·U·W)
    (U2, W2)
}

/// **xDBL Axiom**: `spec_xdbl_projective` correctly computes [2]P.
///
/// If `P` is on the curve with reduced coordinates and `(U:W)` represents `P`, then `xDBL(U,W)`
/// represents `[2]P`.
pub(crate) proof fn axiom_xdbl_projective_correct(P: MontgomeryAffine, U: nat, W: nat)
    requires
        is_canonical_montgomery_affine(P),
        // (U:W) represents P: for finite points u = U/W; for ∞ we have W = 0, U ≠ 0
        projective_represents_montgomery_or_infinity_nat(U, W, P),
    ensures
        ({
            let (U2, W2) = spec_xdbl_projective(U, W);
            projective_represents_montgomery_or_infinity_nat(U2, W2, montgomery_add(P, P))
        }),
{
    admit();
}

/// **Lemma**: xDBL gives W'=0 when U=0 or W=0.
///
/// When U=0 or W=0, we have (U+W)² = (U-W)², so t6 = 0 and W' = t6 * ... = 0.
pub(crate) proof fn lemma_xdbl_degenerate_gives_w_zero(U: nat, W: nat)
    requires
        U == 0 || W == 0,
    ensures
        ({
            let (_, W2) = spec_xdbl_projective(U, W);
            W2 == 0
        }),
{
    let t0 = field_add(U, W);
    let t1 = field_sub(U, W);
    let t4 = field_square(t0);
    let t5 = field_square(t1);
    let t6 = field_sub(t4, t5);

    p_gt_2();

    // Show t4 == t5
    if U == 0 {
        // t0 = (0 + W) % p = W % p
        assert(t0 == W % p());
        // t1 = field_sub(0, W) = (((0 % p) + p) - (W % p)) % p = (p - (W % p)) % p = field_neg(W)
        assert(t1 == field_neg(W)) by {
            lemma_small_mod(0, p());
            assert(0nat % p() == 0);
        }
        // (-W)² = (W % p)²
        assert(t5 == field_square(W % p())) by {
            lemma_neg_square_eq(W);
        }
        // t4 = (W % p)²
        assert(t4 == field_square(W % p())) by {
            lemma_square_mod_noop(W);
        }
        assert(t4 == t5);
    } else {
        // W == 0 case: t0 = U % p, t1 = U % p
        assert(W == 0);
        assert(t0 == U % p());
        // field_sub(U, 0) = (((U % p) + p) - 0) % p = ((U % p) + p) % p = U % p
        assert(t1 == U % p()) by {
            lemma_small_mod(0nat, p());
            // t1 = ((U % p) + p) % p
            // lemma_mod_add_multiples_vanish: (x + p) % p == x % p
            lemma_mod_add_multiples_vanish((U % p()) as int, p() as int);
            // (U % p) % p == U % p
            lemma_mod_twice(U as int, p() as int);
        }
        assert(t0 == t1);
        assert(t4 == t5);
    }

    assert(t6 == 0) by {
        lemma_field_sub_self(t4);
    }

    // W2 = t6 * t15 = 0 * anything = 0
    assert(spec_xdbl_projective(U, W).1 == 0) by {
        let t15 = field_add(field_mul(fe51_as_canonical_nat(&APLUS2_OVER_FOUR), t6), t5);
        lemma_field_mul_zero_left(0, t15);
    }
}

// -----------------------------------------------------------------------------
// xADD (Equation 9): Differential addition P + Q given P - Q
// -----------------------------------------------------------------------------
//
// Input:  (U_P : W_P) representing P
//         (U_Q : W_Q) representing Q
//         u(P-Q)      affine x-coordinate of P - Q
// Output: (U' : W') representing P + Q
//
// Preconditions: P and Q are on the curve with reduced coordinates, P ≠ Q and u(P-Q) ≠ 0.
//
// Formulas (with P - Q in affine form, i.e., W(P-Q) = 1):
//   U' = [(U_P + W_P)(U_Q - W_Q) + (U_P - W_P)(U_Q + W_Q)]²
//   W' = u(P-Q) · [(U_P + W_P)(U_Q - W_Q) - (U_P - W_P)(U_Q + W_Q)]²
//
pub(crate) open spec fn spec_xadd_projective(
    U_P: nat,
    W_P: nat,
    U_Q: nat,
    W_Q: nat,
    affine_PmQ: nat,  // u(P-Q) in affine coordinates
) -> (nat, nat) {
    let t0 = field_add(U_P, W_P);  // t0 = U_P + W_P
    let t1 = field_sub(U_P, W_P);  // t1 = U_P - W_P
    let t2 = field_add(U_Q, W_Q);  // t2 = U_Q + W_Q
    let t3 = field_sub(U_Q, W_Q);  // t3 = U_Q - W_Q
    let t7 = field_mul(t0, t3);  // t7 = (U_P + W_P)(U_Q - W_Q)
    let t8 = field_mul(t1, t2);  // t8 = (U_P - W_P)(U_Q + W_Q)
    let t9 = field_add(t7, t8);  // t7 + t8
    let t10 = field_sub(t7, t8);  // t7 - t8
    let U_PpQ = field_square(t9);  // U' = (t7 + t8)²
    let W_PpQ = field_mul(affine_PmQ, field_square(t10));  // W' = u(P-Q) · (t7 - t8)²
    (U_PpQ, W_PpQ)
}

/// **xADD Axiom**: `spec_xadd_projective` correctly computes P + Q.
///
/// Requires P and Q on the curve with reduced coordinates, P ≠ Q and u(P - Q) ≠ 0.
pub(crate) proof fn axiom_xadd_projective_correct(
    P: MontgomeryAffine,
    Q: MontgomeryAffine,
    U_P: nat,
    W_P: nat,
    U_Q: nat,
    W_Q: nat,
    affine_PmQ: nat,
)
    requires
        is_canonical_montgomery_affine(P),
        is_canonical_montgomery_affine(Q),
        // (U_P:W_P) represents P; (U_Q:W_Q) represents Q
        projective_represents_montgomery_or_infinity_nat(U_P, W_P, P),
        projective_represents_montgomery_or_infinity_nat(U_Q, W_Q, Q),
        P != Q,
        affine_PmQ != 0,
        // u-coordinate is symmetric: u(P-Q) = u(Q-P) since u is invariant under negation
        affine_PmQ == u_coordinate(montgomery_sub(P, Q)) || affine_PmQ == u_coordinate(
            montgomery_sub(Q, P),
        ),
    ensures
        ({
            let (U_PpQ, W_PpQ) = spec_xadd_projective(U_P, W_P, U_Q, W_Q, affine_PmQ);
            projective_represents_montgomery_or_infinity_nat(U_PpQ, W_PpQ, montgomery_add(P, Q))
        }),
{
    admit();
}

/// Combined xDBLADD step for the Montgomery ladder.
///
/// Returns `(U_dbl, W_dbl, U_add, W_add)` where:
/// - `(U_dbl:W_dbl)` is `xDBL(U_P, W_P)` — the doubled point `[2]P`
/// - `(U_add:W_add)` is `xADD(U_P, W_P, U_Q, W_Q, affine_PmQ)` — the sum `P + Q`
pub(crate) open spec fn spec_xdbladd_projective(
    U_P: nat,
    W_P: nat,
    U_Q: nat,
    W_Q: nat,
    affine_PmQ: nat,
) -> (nat, nat, nat, nat) {
    let (U2, W2) = spec_xdbl_projective(U_P, W_P);
    let (U3, W3) = spec_xadd_projective(U_P, W_P, U_Q, W_Q, affine_PmQ);
    (U2, W2, U3, W3)
}

// =============================================================================
// SCALAR MULTIPLICATION LEMMAS
// =============================================================================
/// Lemma: If an affine point has reduced u-coordinate (< p), then any projective representation
/// of its u-coordinate yields the same value via `projective_u_coordinate`.
pub proof fn lemma_projective_represents_implies_u_coordinate(
    P_proj: crate::montgomery::ProjectivePoint,
    P_aff: MontgomeryAffine,
)
    requires
        projective_represents_montgomery_or_infinity(P_proj, P_aff),
    ensures
        projective_u_coordinate(P_proj) == (u_coordinate(P_aff) % p()),
{
    match P_aff {
        MontgomeryAffine::Infinity => {
            // Representation gives W == 0, and both u-coordinate conventions map ∞ to 0.
            assert(fe51_as_canonical_nat(&P_proj.W) == 0);
            assert(projective_u_coordinate(P_proj) == 0);
            assert(u_coordinate(P_aff) == 0);
            assert(u_coordinate(P_aff) % p() == 0) by {
                p_gt_2();
                lemma_small_mod(0, p());
            }
        },
        MontgomeryAffine::Finite { u, v: _ } => {
            let U = fe51_as_canonical_nat(&P_proj.U);
            let W = fe51_as_canonical_nat(&P_proj.W);
            assert(W != 0);
            assert(U == field_mul(u, W));
            assert(W % p() != 0) by {
                let W_raw = fe51_as_nat(&P_proj.W);
                assert(W == W_raw % p());
                assert(W_raw % p() < p()) by {
                    p_gt_2();
                    lemma_mod_division_less_than_divisor(W_raw as int, p() as int);
                }
                assert(W % p() == W) by {
                    lemma_small_mod(W, p());
                }
            }

            // projective_u_coordinate = U / W = (u*W) / W = u
            assert(projective_u_coordinate(P_proj) == field_mul(U, field_inv(W)));
            assert(projective_u_coordinate(P_proj) == field_mul(field_mul(u, W), field_inv(W)));

            assert(projective_u_coordinate(P_proj) == field_mul(u, field_mul(W, field_inv(W)))) by {
                lemma_field_mul_assoc(u, W, field_inv(W));
            }

            assert(field_mul(W, field_inv(W)) == 1) by {
                lemma_inv_mul_cancel(W);
                lemma_field_mul_comm(field_inv(W), W);
            }

            assert(field_mul(u, 1) == u % p()) by {
                lemma_field_mul_one_right(u);
            }
            assert(projective_u_coordinate(P_proj) == u % p());
        },
    }
}

// -----------------------------------------------------------------------------
// Basic scalar multiplication lemmas
// -----------------------------------------------------------------------------
/// Lemma: scalar multiplication by 1 gives P
pub proof fn lemma_montgomery_scalar_mul_one(P: MontgomeryAffine)
    ensures
        montgomery_scalar_mul(P, 1) == P,
{
    // [1]P = P + [0]P = P + Infinity = P
    assert(montgomery_scalar_mul(P, 0) == MontgomeryAffine::Infinity);
    assert(montgomery_scalar_mul(P, 1) == montgomery_add(P, montgomery_scalar_mul(P, 0)));
    assert(montgomery_add(P, MontgomeryAffine::Infinity) == P);
}

/// Lemma: unfolding scalar multiplication by n+1
///
/// [n+1]P = P + [n]P (by definition)
///
/// Note: Kept as explicit lemma; inlining causes rlimit issues in the ladder loop.
pub proof fn lemma_montgomery_scalar_mul_succ(P: MontgomeryAffine, n: nat)
    ensures
        montgomery_scalar_mul(P, n + 1) == montgomery_add(P, montgomery_scalar_mul(P, n)),
{
    // Follows directly from the recursive definition
}

/// Lemma: scalar multiplication distributes over addition of scalars
/// [m + n]P = [m]P + [n]P
///
/// This is a fundamental property that follows from associativity and identity.
/// Proof by induction on m.
///
/// Used by: `differential_add_and_double` proof (to connect [k]P + [k+1]P = [2k+1]P)
pub proof fn lemma_montgomery_scalar_mul_add(P: MontgomeryAffine, m: nat, n: nat)
    requires
        is_canonical_montgomery_affine(P),
    ensures
        montgomery_scalar_mul(P, m + n) == montgomery_add(
            montgomery_scalar_mul(P, m),
            montgomery_scalar_mul(P, n),
        ),
    decreases m,
{
    if m == 0 {
        // Base case: [0 + n]P = [n]P = ∞ + [n]P = [0]P + [n]P
        assert(montgomery_scalar_mul(P, 0) == MontgomeryAffine::Infinity);
        lemma_montgomery_add_identity_left(montgomery_scalar_mul(P, n));
    } else {
        let m_minus_1 = (m - 1) as nat;

        lemma_montgomery_scalar_mul_add(P, m_minus_1, n);

        // [m+n]P = P + [m+n-1]P = P + [m-1+n]P
        assert(m + n >= 1);
        assert(m + n - 1 == m_minus_1 + n) by {
            assert(m >= 1);
            assert(m_minus_1 == m - 1);
        }
        assert(montgomery_scalar_mul(P, m + n) == montgomery_add(
            P,
            montgomery_scalar_mul(P, m_minus_1 + n),
        ));

        // Expand IH on [m-1+n]P.
        assert(montgomery_scalar_mul(P, m_minus_1 + n) == montgomery_add(
            montgomery_scalar_mul(P, m_minus_1),
            montgomery_scalar_mul(P, n),
        ));

        lemma_montgomery_scalar_mul_canonical(P, m_minus_1);
        lemma_montgomery_scalar_mul_canonical(P, n);
        axiom_montgomery_add_associative(
            P,
            montgomery_scalar_mul(P, m_minus_1),
            montgomery_scalar_mul(P, n),
        );
        assert(montgomery_add(
            P,
            montgomery_add(montgomery_scalar_mul(P, m_minus_1), montgomery_scalar_mul(P, n)),
        ) == montgomery_add(
            montgomery_add(P, montgomery_scalar_mul(P, m_minus_1)),
            montgomery_scalar_mul(P, n),
        ));

        // By definition: [m]P = P + [m-1]P.
        assert(montgomery_scalar_mul(P, m) == montgomery_add(
            P,
            montgomery_scalar_mul(P, m_minus_1),
        ));

        assert(montgomery_scalar_mul(P, m + n) == montgomery_add(
            montgomery_scalar_mul(P, m),
            montgomery_scalar_mul(P, n),
        ));
    }
}

/// Lemma: [2n]P = [n]P + [n]P (doubling a scalar multiple)
///
/// Used by: `differential_add_and_double` proof (to show xDBL output is [2k]B)
pub proof fn lemma_montgomery_scalar_mul_double(P: MontgomeryAffine, n: nat)
    requires
        is_canonical_montgomery_affine(P),
    ensures
        montgomery_scalar_mul(P, 2 * n) == montgomery_add(
            montgomery_scalar_mul(P, n),
            montgomery_scalar_mul(P, n),
        ),
{
    // [2n]P = [n + n]P = [n]P + [n]P (by lemma_montgomery_scalar_mul_add)
    lemma_montgomery_scalar_mul_add(P, n, n);
}

// =============================================================================
// CURVE MEMBERSHIP
// =============================================================================
//
// The group axioms above hold only for points on the curve with reduced
// coordinates (`is_canonical_montgomery_affine`). These lemmas show that the
// points used by the Montgomery ladder have this property.
/// Lemma: the canonical lift of a valid u-coordinate is a canonical curve point.
pub proof fn lemma_canonical_montgomery_lift_is_canonical(u0: nat)
    requires
        is_valid_u_coordinate(u0),
    ensures
        is_canonical_montgomery_affine(canonical_montgomery_lift(u0)),
{
    p_gt_2();
    let pp = p();
    let a = fe51_as_canonical_nat(&MONTGOMERY_A);
    let r = montgomery_rhs(u0);
    let u = u0 % pp;
    let v = canonical_sqrt(r);
    assert(canonical_montgomery_lift(u0) == MontgomeryAffine::Finite { u, v });

    // r is reduced, so field_canonical(r) == r.
    assert(r % pp == r) by {
        lemma_mod_twice(
            (field_add(field_mul(field_mul(u0, u0), u0), field_mul(a, field_mul(u0, u0)))
                + u0) as int,
            pp as int,
        );
    }

    // field_sqrt(r) is a reduced square root of r.
    let y = choose|y: nat| #[trigger] field_mul(y, y) == field_canonical(r);
    let y0 = y % pp;
    assert(y0 < pp && field_mul(y0, y0) == field_canonical(r)) by {
        lemma_mod_bound(y as int, pp as int);
        lemma_mul_mod_noop(y as int, y as int, pp as int);
    }
    let s1 = field_sqrt(r);
    assert(s1 < pp && field_mul(s1, s1) == r);

    // v is s1 or -s1; both are reduced and square to r.
    assert(v < pp && field_square(v) == r) by {
        if s1 % 2 != 0 {
            lemma_mod_bound((pp - field_canonical(s1)) as int, pp as int);
            lemma_neg_square_eq(s1);
            lemma_small_mod(s1, pp);
        }
    }

    // The curve right-hand side at u = u0 % p equals montgomery_rhs(u0).
    let sq = field_mul(u0, u0);
    assert(field_square(u) == sq) by {
        lemma_mul_mod_noop(u0 as int, u0 as int, pp as int);
    }
    assert(field_mul(u, sq) == field_mul(sq, u0)) by {
        lemma_mul_mod_noop_left(u0 as int, sq as int, pp as int);
        lemma_mul_is_commutative(u0 as int, sq as int);
    }
    let x = field_add(field_mul(sq, u0), field_mul(a, sq));
    assert(field_add(x, u) == field_add(x, u0)) by {
        lemma_add_mod_noop_right(x as int, u0 as int, pp as int);
    }
    assert(u < pp) by {
        lemma_mod_bound(u0 as int, pp as int);
    }
}

/// Lemma: negation keeps a point canonical.
pub proof fn lemma_montgomery_neg_canonical(P: MontgomeryAffine)
    requires
        is_canonical_montgomery_affine(P),
    ensures
        is_canonical_montgomery_affine(montgomery_neg(P)),
{
    if let MontgomeryAffine::Finite { u, v } = P {
        p_gt_2();
        lemma_mod_bound((p() - field_canonical(v)) as int, p() as int);
        lemma_neg_square_eq(v);
        lemma_small_mod(v, p());
    }
}

/// Lemma: scalar multiples of a canonical point are canonical.
pub proof fn lemma_montgomery_scalar_mul_canonical(P: MontgomeryAffine, n: nat)
    requires
        is_canonical_montgomery_affine(P),
    ensures
        is_canonical_montgomery_affine(montgomery_scalar_mul(P, n)),
    decreases n,
{
    if n > 0 {
        lemma_montgomery_scalar_mul_canonical(P, (n - 1) as nat);
        lemma_montgomery_add_canonical(P, montgomery_scalar_mul(P, (n - 1) as nat));
    }
}

/// Lemma: the points used in one Montgomery ladder step are canonical.
///
/// For `B = canonical_montgomery_lift(u0)`: `B`, `[k]B`, `[k+1]B` and the
/// negations of `[k]B` and `[k+1]B`.
pub proof fn lemma_montgomery_ladder_points_canonical(u0: nat, k: nat)
    requires
        is_valid_u_coordinate(u0),
    ensures
        ({
            let B = canonical_montgomery_lift(u0);
            &&& is_canonical_montgomery_affine(B)
            &&& is_canonical_montgomery_affine(montgomery_scalar_mul(B, k))
            &&& is_canonical_montgomery_affine(montgomery_scalar_mul(B, k + 1))
            &&& is_canonical_montgomery_affine(montgomery_neg(montgomery_scalar_mul(B, k)))
            &&& is_canonical_montgomery_affine(montgomery_neg(montgomery_scalar_mul(B, k + 1)))
        }),
{
    let B = canonical_montgomery_lift(u0);
    lemma_canonical_montgomery_lift_is_canonical(u0);
    lemma_montgomery_scalar_mul_canonical(B, k);
    lemma_montgomery_scalar_mul_canonical(B, k + 1);
    lemma_montgomery_neg_canonical(montgomery_scalar_mul(B, k));
    lemma_montgomery_neg_canonical(montgomery_scalar_mul(B, k + 1));
}

// -----------------------------------------------------------------------------
// Closure of montgomery_add
// -----------------------------------------------------------------------------
//
// Proof sketch. Let f(x) = x³ + A·x² + x and let L(x) = λ·(x - u1) + v1 be the
// chord (or tangent) line. Then f(x) - L(x)² equals (x - u1)(x - u2)(x - c) + α·x + β
// for c = λ² - A - u1 - u2 and some α, β. The line meets the curve at u1 and u2
// (or touches it at u1), so α ≡ β ≡ 0 (mod p). The third point u3 ≡ c then also
// satisfies f(u3) ≡ L(u3)² = v3².
//
// All steps below are integer congruences mod p (`field_congruent`).
/// Congruence mod p on integers.
spec fn field_congruent(a: int, b: int) -> bool {
    a % (p() as int) == b % (p() as int)
}

/// f(x) = x·x² + A·x² + x, the right-hand side of the curve equation, over the integers.
spec fn montgomery_rhs_int(a: int, x: int) -> int {
    x * (x * x) + a * (x * x) + x
}

/// f(x) - L(x)² where L(x) = l·(x - u1) + v1.
spec fn montgomery_line_gap(a: int, u1: int, v1: int, l: int, x: int) -> int {
    montgomery_rhs_int(a, x) - (l * (x - u1) + v1) * (l * (x - u1) + v1)
}

/// The x-coefficient of `montgomery_line_gap - (x - u1)(x - u2)(x - c)`.
spec fn montgomery_line_alpha(a: int, u1: int, u2: int, v1: int, l: int) -> int {
    1 + 2 * l * l * u1 - 2 * l * v1 - u1 * u2 - (l * l - a - u1 - u2) * (u1 + u2)
}

/// The constant term of `montgomery_line_gap - (x - u1)(x - u2)(x - c)`.
spec fn montgomery_line_beta(a: int, u1: int, u2: int, v1: int, l: int) -> int {
    -(l * l * u1 * u1) + 2 * l * v1 * u1 - v1 * v1 + u1 * u2 * (l * l - a - u1 - u2)
}

proof fn lemma_field_congruent_add(a: int, b: int, c: int, d: int)
    requires
        field_congruent(a, b),
        field_congruent(c, d),
    ensures
        field_congruent(a + c, b + d),
{
    p_gt_2();
    lemma_add_mod_noop(a, c, p() as int);
    lemma_add_mod_noop(b, d, p() as int);
}

proof fn lemma_field_congruent_sub(a: int, b: int, c: int, d: int)
    requires
        field_congruent(a, b),
        field_congruent(c, d),
    ensures
        field_congruent(a - c, b - d),
{
    p_gt_2();
    lemma_sub_mod_noop(a, c, p() as int);
    lemma_sub_mod_noop(b, d, p() as int);
}

proof fn lemma_field_congruent_mul(a: int, b: int, c: int, d: int)
    requires
        field_congruent(a, b),
        field_congruent(c, d),
    ensures
        field_congruent(a * c, b * d),
{
    p_gt_2();
    lemma_mul_mod_noop(a, c, p() as int);
    lemma_mul_mod_noop(b, d, p() as int);
}

proof fn lemma_field_congruent_mod(a: int)
    ensures
        field_congruent(a % (p() as int), a),
{
    p_gt_2();
    lemma_mod_twice(a, p() as int);
}

/// Two reduced values that are congruent are equal.
proof fn lemma_field_congruent_reduced_eq(x: nat, y: nat)
    requires
        x < p(),
        y < p(),
        field_congruent(x as int, y as int),
    ensures
        x == y,
{
    lemma_small_mod(x, p());
    lemma_small_mod(y, p());
}

/// Euclid's lemma for congruences: if p | a·b and p ∤ b, then p | a.
proof fn lemma_field_congruent_mul_zero(a: int, b: int)
    requires
        field_congruent(a * b, 0),
        !field_congruent(b, 0),
    ensures
        field_congruent(a, 0),
{
    let pp = p() as int;
    p_gt_2();
    lemma_mod_bound(a, pp);
    lemma_mod_bound(b, pp);
    let am = (a % pp) as nat;
    let bm = (b % pp) as nat;
    assert((am * bm) % p() == 0) by {
        lemma_mul_mod_noop(a, b, pp);
        lemma_small_mod(0, p());
    }
    axiom_p_is_prime();
    lemma_euclid_prime(am, bm, p());
    lemma_small_mod(0, p());
    lemma_small_mod(am, p());
    lemma_small_mod(bm, p());
}

proof fn lemma_field_congruent_field_add(a: nat, b: nat)
    ensures
        field_congruent(field_add(a, b) as int, a as int + b as int),
{
    lemma_field_congruent_mod(a as int + b as int);
}

proof fn lemma_field_congruent_field_mul(a: nat, b: nat)
    ensures
        field_congruent(field_mul(a, b) as int, (a as int) * (b as int)),
        field_congruent(field_square(a) as int, (a as int) * (a as int)),
{
    lemma_field_congruent_mod((a as int) * (b as int));
    lemma_field_congruent_mod((a as int) * (a as int));
}

proof fn lemma_field_congruent_field_sub(a: nat, b: nat)
    ensures
        field_congruent(field_sub(a, b) as int, a - b),
{
    let pp = p() as int;
    p_gt_2();
    lemma_mod_bound(b as int, pp);
    let x: int = (a % p()) as int + pp - (b % p()) as int;
    assert(field_sub(a, b) as int == x % pp);
    lemma_field_congruent_mod(x);
    lemma_field_congruent_mod(a as int);
    lemma_field_congruent_mod(b as int);
    assert(field_congruent(pp, 0)) by {
        lemma_mod_self_0(pp);
        lemma_small_mod(0, p());
    }
    lemma_field_congruent_add((a % p()) as int, a as int, pp, 0);
    lemma_field_congruent_sub((a % p()) as int + pp, a as int + 0, (b % p()) as int, b as int);
}

/// `on_montgomery_curve(u, v)` holds exactly when v² ≡ f(u) (mod p).
proof fn lemma_on_montgomery_curve_iff_fcong(u: nat, v: nat)
    ensures
        on_montgomery_curve(u, v) == field_congruent(
            (v as int) * (v as int),
            montgomery_rhs_int(fe51_as_canonical_nat(&MONTGOMERY_A) as int, u as int),
        ),
{
    let a = fe51_as_canonical_nat(&MONTGOMERY_A);
    let u2 = field_square(u);
    let t1 = field_mul(u, u2);
    let t2 = field_mul(a, u2);
    let s = field_add(t1, t2);
    let r = field_add(s, u);
    p_gt_2();

    lemma_field_congruent_field_mul(u, u);
    lemma_field_congruent_field_mul(u, u2);
    lemma_field_congruent_field_mul(a, u2);
    let ui = u as int;
    let ai = a as int;
    lemma_field_congruent_mul(ui, ui, u2 as int, ui * ui);
    lemma_field_congruent_mul(ai, ai, u2 as int, ui * ui);
    lemma_field_congruent_field_add(t1, t2);
    lemma_field_congruent_add(t1 as int, ui * (ui * ui), t2 as int, ai * (ui * ui));
    lemma_field_congruent_field_add(s, u);
    lemma_field_congruent_add(s as int, ui * (ui * ui) + ai * (ui * ui), ui, ui);
    assert(field_congruent(r as int, montgomery_rhs_int(a as int, u as int)));

    lemma_field_congruent_field_mul(v, v);
    lemma_mod_bound((s + u) as int, p() as int);
    lemma_mod_bound((v * v) as int, p() as int);
    lemma_small_mod(r, p());
    lemma_small_mod(field_square(v), p());
}

/// (x² - (u1 + u2)·x + u1·u2)·(x - c) expanded by powers of x.
proof fn lemma_monic_cubic_expand(x: int, u1: int, u2: int, c: int)
    ensures
        (x * x - (u1 + u2) * x + u1 * u2) * (x - c) == x * (x * x) - (u1 + u2 + c) * (x * x) + (u1
            * u2 + (u1 + u2) * c) * x - u1 * u2 * c,
{
    let q = x * x - (u1 + u2) * x + u1 * u2;
    assert(q * (x - c) == q * x - q * c) by (nonlinear_arith);
    assert(q * x == x * (x * x) - (u1 + u2) * (x * x) + u1 * u2 * x) by (nonlinear_arith)
        requires
            q == x * x - (u1 + u2) * x + u1 * u2,
    ;
    assert(q * c == c * (x * x) - (u1 + u2) * c * x + u1 * u2 * c) by (nonlinear_arith)
        requires
            q == x * x - (u1 + u2) * x + u1 * u2,
    ;
    assert((u1 + u2 + c) * (x * x) == (u1 + u2) * (x * x) + c * (x * x)) by (nonlinear_arith);
    assert((u1 * u2 + (u1 + u2) * c) * x == u1 * u2 * x + (u1 + u2) * c * x) by (nonlinear_arith);
}

/// The polynomial identity f(x) - L(x)² = (x - u1)(x - u2)(x - c) + α·x + β.
proof fn lemma_montgomery_line_gap_identity(a: int, u1: int, u2: int, v1: int, l: int, x: int)
    ensures
        montgomery_line_gap(a, u1, v1, l, x) == (x - u1) * (x - u2) * (x - (l * l - a - u1 - u2))
            + montgomery_line_alpha(a, u1, u2, v1, l) * x + montgomery_line_beta(a, u1, u2, v1, l),
{
    let c = l * l - a - u1 - u2;
    let ll = l * l;
    let y = x - u1;
    let alpha = montgomery_line_alpha(a, u1, u2, v1, l);
    let beta = montgomery_line_beta(a, u1, u2, v1, l);

    // L(x)² = l²·x² - 2l²u1·x + l²u1² + 2l·v1·x - 2l·v1·u1 + v1².
    assert((l * y + v1) * (l * y + v1) == ll * (y * y) + 2 * l * v1 * y + v1 * v1)
        by (nonlinear_arith)
        requires
            ll == l * l,
    ;
    assert(y * y == x * x - 2 * u1 * x + u1 * u1) by (nonlinear_arith)
        requires
            y == x - u1,
    ;
    assert(ll * (y * y) == ll * (x * x) - 2 * ll * u1 * x + ll * u1 * u1) by (nonlinear_arith)
        requires
            y * y == x * x - 2 * u1 * x + u1 * u1,
    ;
    assert(2 * l * v1 * y == 2 * l * v1 * x - 2 * l * v1 * u1) by (nonlinear_arith)
        requires
            y == x - u1,
    ;
    let sq_l = ll * (x * x) - 2 * ll * u1 * x + ll * u1 * u1 + 2 * l * v1 * x - 2 * l * v1 * u1 + v1
        * v1;
    assert((l * (x - u1) + v1) * (l * (x - u1) + v1) == sq_l);

    // (x - u1)(x - u2)(x - c) = x³ - (l² - A)·x² + (u1·u2 + (u1 + u2)·c)·x - u1·u2·c.
    assert((x - u1) * (x - u2) == x * x - (u1 + u2) * x + u1 * u2) by (nonlinear_arith);
    lemma_monic_cubic_expand(x, u1, u2, c);
    assert((u1 + u2 + c) * (x * x) == ll * (x * x) - a * (x * x)) by (nonlinear_arith)
        requires
            u1 + u2 + c == ll - a,
    ;
    let cubic = x * (x * x) - ll * (x * x) + a * (x * x) + (u1 * u2 + (u1 + u2) * c) * x - u1 * u2
        * c;
    assert((x - u1) * (x - u2) * (x - c) == cubic);

    // α·x + β collects the remaining terms.
    assert(alpha * x == x + 2 * ll * u1 * x - 2 * l * v1 * x - (u1 * u2 + (u1 + u2) * c) * x)
        by (nonlinear_arith)
        requires
            alpha == 1 + 2 * l * l * u1 - 2 * l * v1 - u1 * u2 - c * (u1 + u2),
            ll == l * l,
    ;
    assert(beta == -(ll * u1 * u1) + 2 * l * v1 * u1 - v1 * v1 + u1 * u2 * c) by (nonlinear_arith)
        requires
            beta == -(l * l * u1 * u1) + 2 * l * v1 * u1 - v1 * v1 + u1 * u2 * c,
            ll == l * l,
    ;
}

/// If the line meets the curve at u1 with α ≡ 0, then the third point (u3, v3) is on the curve.
proof fn lemma_montgomery_line_third_point(
    a: int,
    u1: int,
    u2: int,
    u3: int,
    v1: int,
    v3: int,
    l: int,
)
    requires
        field_congruent(montgomery_line_alpha(a, u1, u2, v1, l), 0),
        field_congruent(montgomery_line_gap(a, u1, v1, l, u1), 0),
        field_congruent(u3, l * l - a - u1 - u2),
        field_congruent(v3, l * (u1 - u3) - v1),
    ensures
        field_congruent(v3 * v3, montgomery_rhs_int(a, u3)),
{
    let c = l * l - a - u1 - u2;
    let alpha = montgomery_line_alpha(a, u1, u2, v1, l);
    let beta = montgomery_line_beta(a, u1, u2, v1, l);

    // At x = u1 the cubic term vanishes, so β ≡ gap(u1) - α·u1 ≡ 0.
    lemma_montgomery_line_gap_identity(a, u1, u2, v1, l, u1);
    assert((u1 - u1) * (u1 - u2) * (u1 - c) == 0) by (nonlinear_arith);
    lemma_field_congruent_mul(alpha, 0, u1, u1);
    lemma_field_congruent_sub(montgomery_line_gap(a, u1, v1, l, u1), 0, alpha * u1, 0 * u1);
    assert(field_congruent(beta, 0));

    // At x = u3 the factor (u3 - c) is ≡ 0, so gap(u3) ≡ 0.
    lemma_montgomery_line_gap_identity(a, u1, u2, v1, l, u3);
    let k = (u3 - u1) * (u3 - u2);
    lemma_field_congruent_sub(u3, c, c, c);
    lemma_field_congruent_mul(k, k, u3 - c, 0);
    lemma_field_congruent_mul(alpha, 0, u3, u3);
    lemma_field_congruent_add(k * (u3 - c), k * 0, alpha * u3, 0 * u3);
    lemma_field_congruent_add(k * (u3 - c) + alpha * u3, k * 0 + 0 * u3, beta, 0);
    assert(k * 0 + 0 * u3 + 0 == 0) by (nonlinear_arith);
    let gap3 = montgomery_line_gap(a, u1, v1, l, u3);
    assert(field_congruent(gap3, 0));

    // v3 ≡ -L(u3), so v3² ≡ L(u3)² ≡ f(u3).
    let lu3 = l * (u3 - u1) + v1;
    assert(l * (u1 - u3) - v1 == -(l * (u3 - u1) + v1)) by (nonlinear_arith);
    lemma_field_congruent_mul(v3, -lu3, v3, -lu3);
    assert((-lu3) * (-lu3) == lu3 * lu3) by (nonlinear_arith);
    lemma_field_congruent_add(gap3, 0, lu3 * lu3, v3 * v3);
}

/// gap(u1) ≡ 0 when (u1, v1) is on the curve.
proof fn lemma_montgomery_line_gap_at_u1(a: int, u1: int, v1: int, l: int)
    requires
        field_congruent(v1 * v1, montgomery_rhs_int(a, u1)),
    ensures
        field_congruent(montgomery_line_gap(a, u1, v1, l, u1), 0),
{
    assert(l * (u1 - u1) + v1 == v1) by (nonlinear_arith);
    lemma_field_congruent_sub(montgomery_rhs_int(a, u1), v1 * v1, v1 * v1, v1 * v1);
}

/// λ·d ≡ n when λ = n / d and d ≠ 0.
proof fn lemma_field_div_mul_fcong(n: nat, d: nat)
    requires
        n < p(),
        d < p(),
        d != 0,
    ensures
        field_congruent((field_mul(n, field_inv(d)) as int) * (d as int), n as int),
{
    let l = field_mul(n, field_inv(d));
    lemma_small_mod(d, p());
    lemma_inv_mul_cancel(d);
    lemma_field_mul_assoc(n, field_inv(d), d);
    lemma_field_mul_one_right(n);
    lemma_small_mod(n, p());
    assert(field_mul(l, d) == n);
    lemma_field_congruent_field_mul(l, d);
}

/// Chord branch: P ≠ ±Q with u1 ≠ u2.
proof fn lemma_montgomery_add_chord_on_curve(u1: nat, v1: nat, u2: nat, v2: nat)
    requires
        u1 < p(),
        v1 < p(),
        u2 < p(),
        v2 < p(),
        on_montgomery_curve(u1, v1),
        on_montgomery_curve(u2, v2),
        u1 != u2,
    ensures
        ({
            let a = fe51_as_canonical_nat(&MONTGOMERY_A);
            let lambda = field_mul(field_sub(v2, v1), field_inv(field_sub(u2, u1)));
            let u3 = field_sub(field_sub(field_sub(field_square(lambda), a), u1), u2);
            let v3 = field_sub(field_mul(lambda, field_sub(u1, u3)), v1);
            on_montgomery_curve(u3, v3)
        }),
{
    let a = fe51_as_canonical_nat(&MONTGOMERY_A);
    let d = field_sub(u2, u1);
    let n = field_sub(v2, v1);
    let l = field_mul(n, field_inv(d));
    let t1 = field_sub(field_square(l), a);
    let t2 = field_sub(t1, u1);
    let u3 = field_sub(t2, u2);
    let w = field_sub(u1, u3);
    let lw = field_mul(l, w);
    let v3 = field_sub(lw, v1);
    let (ai, li, x1, y1, x2, y2, x3, y3) = (
        a as int,
        l as int,
        u1 as int,
        v1 as int,
        u2 as int,
        v2 as int,
        u3 as int,
        v3 as int,
    );
    p_gt_2();

    // d ≡ u2 - u1 is non-zero, and λ·(u2 - u1) ≡ v2 - v1.
    lemma_field_congruent_field_sub(u2, u1);
    lemma_field_congruent_field_sub(v2, v1);
    lemma_mod_bound(u2 % p() + p() - u1 % p(), p() as int);
    lemma_mod_bound(v2 % p() + p() - v1 % p(), p() as int);
    assert(d != 0) by {
        if d == 0 {
            lemma_field_congruent_add(d as int, x2 - x1, x1, x1);
            lemma_field_congruent_reduced_eq(u1, u2);
        }
    }
    lemma_field_div_mul_fcong(n, d);
    lemma_field_congruent_mul(li, li, d as int, x2 - x1);
    assert(field_congruent(li * (x2 - x1), y2 - y1));

    // u3 ≡ λ² - A - u1 - u2 and v3 ≡ λ·(u1 - u3) - v1.
    lemma_field_congruent_field_mul(l, l);
    lemma_field_congruent_field_sub(field_square(l), a);
    lemma_field_congruent_sub(field_square(l) as int, li * li, ai, ai);
    lemma_field_congruent_field_sub(t1, u1);
    lemma_field_congruent_sub(t1 as int, li * li - ai, x1, x1);
    lemma_field_congruent_field_sub(t2, u2);
    lemma_field_congruent_sub(t2 as int, li * li - ai - x1, x2, x2);
    assert(field_congruent(x3, li * li - ai - x1 - x2));
    lemma_field_congruent_field_sub(u1, u3);
    lemma_field_congruent_field_mul(l, w);
    lemma_field_congruent_mul(li, li, w as int, x1 - x3);
    lemma_field_congruent_field_sub(lw, v1);
    lemma_field_congruent_sub(lw as int, li * (x1 - x3), y1, y1);
    assert(field_congruent(y3, li * (x1 - x3) - y1));

    // gap(u1) ≡ 0 and gap(u2) ≡ 0, so α·(u1 - u2) ≡ 0 and α ≡ 0.
    lemma_on_montgomery_curve_iff_fcong(u1, v1);
    lemma_on_montgomery_curve_iff_fcong(u2, v2);
    lemma_montgomery_line_gap_at_u1(ai, x1, y1, li);
    let lu2 = li * (x2 - x1) + y1;
    lemma_field_congruent_add(li * (x2 - x1), y2 - y1, y1, y1);
    lemma_field_congruent_mul(lu2, y2, lu2, y2);
    lemma_field_congruent_sub(montgomery_rhs_int(ai, x2), y2 * y2, lu2 * lu2, y2 * y2);
    let g1 = montgomery_line_gap(ai, x1, y1, li, x1);
    let g2 = montgomery_line_gap(ai, x1, y1, li, x2);
    assert(field_congruent(g2, 0));
    let alpha = montgomery_line_alpha(ai, x1, x2, y1, li);
    let beta = montgomery_line_beta(ai, x1, x2, y1, li);
    let c = li * li - ai - x1 - x2;
    lemma_montgomery_line_gap_identity(ai, x1, x2, y1, li, x1);
    lemma_montgomery_line_gap_identity(ai, x1, x2, y1, li, x2);
    assert((x1 - x1) * (x1 - x2) * (x1 - c) == 0) by (nonlinear_arith);
    assert((x2 - x1) * (x2 - x2) * (x2 - c) == 0) by (nonlinear_arith);
    assert(g1 - g2 == alpha * (x1 - x2)) by (nonlinear_arith)
        requires
            g1 == alpha * x1 + beta,
            g2 == alpha * x2 + beta,
    ;
    lemma_field_congruent_sub(g1, 0, g2, 0);
    assert(!field_congruent(x1 - x2, 0)) by {
        if field_congruent(x1 - x2, 0) {
            lemma_field_congruent_add(x1 - x2, 0, x2, x2);
            lemma_field_congruent_reduced_eq(u1, u2);
        }
    }
    lemma_field_congruent_mul_zero(alpha, x1 - x2);

    lemma_montgomery_line_third_point(ai, x1, x2, x3, y1, y3, li);
    lemma_on_montgomery_curve_iff_fcong(u3, v3);
}

/// Doubling branch: P = Q with v1 ≠ 0.
proof fn lemma_montgomery_add_double_on_curve(u1: nat, v1: nat)
    requires
        u1 < p(),
        v1 < p(),
        on_montgomery_curve(u1, v1),
        v1 != 0,
    ensures
        ({
            let a = fe51_as_canonical_nat(&MONTGOMERY_A);
            let num = field_add(
                field_add(field_mul(3, field_square(u1)), field_mul(field_mul(2, a), u1)),
                1,
            );
            let lambda = field_mul(num, field_inv(field_mul(2, v1)));
            let u3 = field_sub(field_sub(field_square(lambda), a), field_mul(2, u1));
            let v3 = field_sub(field_mul(lambda, field_sub(u1, u3)), v1);
            on_montgomery_curve(u3, v3)
        }),
{
    let a = fe51_as_canonical_nat(&MONTGOMERY_A);
    let sq = field_square(u1);
    let m3 = field_mul(3, sq);
    let a2 = field_mul(2, a);
    let m2 = field_mul(a2, u1);
    let s = field_add(m3, m2);
    let num = field_add(s, 1);
    let d = field_mul(2, v1);
    let l = field_mul(num, field_inv(d));
    let t1 = field_sub(field_square(l), a);
    let tu = field_mul(2, u1);
    let u3 = field_sub(t1, tu);
    let w = field_sub(u1, u3);
    let lw = field_mul(l, w);
    let v3 = field_sub(lw, v1);
    let (ai, li, x1, y1, x3, y3) = (a as int, l as int, u1 as int, v1 as int, u3 as int, v3 as int);
    p_gt_2();

    // num ≡ 3·u1² + 2A·u1 + 1.
    lemma_field_congruent_field_mul(u1, u1);
    lemma_field_congruent_field_mul(3, sq);
    lemma_field_congruent_mul(3, 3, sq as int, x1 * x1);
    lemma_field_congruent_field_mul(2, a);
    lemma_field_congruent_field_mul(a2, u1);
    lemma_field_congruent_mul(a2 as int, 2 * ai, x1, x1);
    lemma_field_congruent_field_add(m3, m2);
    lemma_field_congruent_add(m3 as int, 3 * (x1 * x1), m2 as int, (2 * ai) * x1);
    lemma_field_congruent_field_add(s, 1);
    lemma_field_congruent_add(s as int, 3 * (x1 * x1) + (2 * ai) * x1, 1, 1);
    let num_int = 3 * (x1 * x1) + (2 * ai) * x1 + 1;
    assert(field_congruent(num as int, num_int));

    // d = 2·v1 is non-zero, and λ·(2·v1) ≡ num.
    lemma_small_mod(2, p());
    lemma_small_mod(v1, p());
    lemma_nonzero_product(2, v1);
    lemma_mod_bound(s as int + 1, p() as int);
    lemma_mod_bound(2 * y1, p() as int);
    lemma_field_div_mul_fcong(num, d);
    lemma_field_congruent_field_mul(2, v1);
    lemma_field_congruent_mul(li, li, d as int, 2 * y1);
    assert(field_congruent(li * (2 * y1), num_int));

    // α ≡ 0 because α = num_int - λ·(2·v1) exactly when u2 = u1.
    let alpha = montgomery_line_alpha(ai, x1, x1, y1, li);
    assert(1 + 2 * li * li * x1 - 2 * li * y1 - x1 * x1 - (li * li - ai - x1 - x1) * (x1 + x1) == 3
        * (x1 * x1) + (2 * ai) * x1 + 1 - li * (2 * y1)) by (nonlinear_arith);
    assert(alpha == num_int - li * (2 * y1));
    lemma_field_congruent_sub(num_int, num_int, li * (2 * y1), num_int);
    assert(field_congruent(alpha, 0));

    // u3 ≡ λ² - A - u1 - u1 and v3 ≡ λ·(u1 - u3) - v1.
    lemma_field_congruent_field_mul(l, l);
    lemma_field_congruent_field_sub(field_square(l), a);
    lemma_field_congruent_sub(field_square(l) as int, li * li, ai, ai);
    lemma_field_congruent_field_mul(2, u1);
    lemma_field_congruent_field_sub(t1, tu);
    lemma_field_congruent_sub(t1 as int, li * li - ai, tu as int, 2 * x1);
    assert(field_congruent(x3, li * li - ai - x1 - x1));
    lemma_field_congruent_field_sub(u1, u3);
    lemma_field_congruent_field_mul(l, w);
    lemma_field_congruent_mul(li, li, w as int, x1 - x3);
    lemma_field_congruent_field_sub(lw, v1);
    lemma_field_congruent_sub(lw as int, li * (x1 - x3), y1, y1);
    assert(field_congruent(y3, li * (x1 - x3) - y1));

    lemma_on_montgomery_curve_iff_fcong(u1, v1);
    lemma_montgomery_line_gap_at_u1(ai, x1, y1, li);
    lemma_montgomery_line_third_point(ai, x1, x1, x3, y1, y3, li);
    lemma_on_montgomery_curve_iff_fcong(u3, v3);
}

/// Two curve points with the same u-coordinate have v2 = v1 or v2 = -v1.
proof fn lemma_same_u_on_curve_implies_v_or_neg_v(u: nat, v1: nat, v2: nat)
    requires
        u < p(),
        v1 < p(),
        v2 < p(),
        on_montgomery_curve(u, v1),
        on_montgomery_curve(u, v2),
    ensures
        v1 == v2 || field_add(v1, v2) == 0,
{
    let (y1, y2) = (v1 as int, v2 as int);
    lemma_on_montgomery_curve_iff_fcong(u, v1);
    lemma_on_montgomery_curve_iff_fcong(u, v2);
    assert((y1 - y2) * (y1 + y2) == y1 * y1 - y2 * y2) by (nonlinear_arith);
    let r = montgomery_rhs_int(fe51_as_canonical_nat(&MONTGOMERY_A) as int, u as int);
    lemma_field_congruent_sub(y1 * y1, r, y2 * y2, r);
    assert(field_congruent((y1 - y2) * (y1 + y2), 0));
    if !field_congruent(y1 + y2, 0) {
        lemma_field_congruent_mul_zero(y1 - y2, y1 + y2);
        lemma_field_congruent_add(y1 - y2, 0, y2, y2);
        lemma_field_congruent_reduced_eq(v1, v2);
    } else {
        p_gt_2();
        lemma_small_mod(0, p());
    }
}

/// Lemma: Montgomery addition keeps points on the curve, with reduced coordinates.
pub proof fn lemma_montgomery_add_canonical(P: MontgomeryAffine, Q: MontgomeryAffine)
    requires
        is_canonical_montgomery_affine(P),
        is_canonical_montgomery_affine(Q),
    ensures
        is_canonical_montgomery_affine(montgomery_add(P, Q)),
{
    if let (MontgomeryAffine::Finite { u: u1, v: v1 }, MontgomeryAffine::Finite { u: u2, v: v2 }) =
        (P, Q) {
        p_gt_2();
        if u1 == u2 && field_add(v1, v2) == 0 {
        } else {
            // The result coordinates are outputs of field_sub, so they are reduced.
            if let MontgomeryAffine::Finite { u: u3, v: v3 } = montgomery_add(P, Q) {
                lemma_mod_bound(u3 as int, p() as int);
                lemma_mod_bound(v3 as int, p() as int);
            }
            if u1 == u2 && v1 == v2 {
                assert(v1 != 0) by {
                    if v1 == 0 {
                        lemma_small_mod(0, p());
                    }
                }
                lemma_montgomery_add_double_on_curve(u1, v1);
            } else {
                assert(u1 != u2) by {
                    if u1 == u2 {
                        lemma_same_u_on_curve_implies_v_or_neg_v(u1, v1, v2);
                    }
                }
                lemma_montgomery_add_chord_on_curve(u1, v1, u2, v2);
            }
        }
    }
}

// =============================================================================
// DEGENERATE BASEPOINT (u=0) LEMMAS
// =============================================================================
//
// These lemmas handle the edge case where the basepoint u-coordinate is 0.
// The point (0,0) is the unique 2-torsion point on Curve25519's Montgomery form:
// it satisfies (0,0) + (0,0) = ∞.
//
// For the Montgomery ladder, if u(P-Q) = 0, all scalar multiples have u = 0.
// This is used in `mul_bits_be` to handle this degenerate case.
//
// Used by: `lemma_u_coordinate_scalar_mul_canonical_lift_zero` which is called
// from `mul_bits_be` for the u=0 edge case.
/// Lemma: the unique square root of 0 is 0.
pub proof fn lemma_field_sqrt_zero()
    ensures
        field_sqrt(0) == 0,
{
    // Witness: 0 is a square root of 0 mod p
    assert(exists|y: nat| y < p() && #[trigger] field_mul(y, y) == field_canonical(0)) by {
        let y: nat = 0;
        p_gt_2();
        assert(y < p() && field_mul(y, y) == field_canonical(0)) by {
            assert(0 * 0 == 0) by {
                lemma_mul_basics(0);
            }
            assert(0nat % p() == 0) by {
                lemma_small_mod(0, p());
            }
        }
    };

    reveal(field_sqrt);
    let y = field_sqrt(0);
    // From field_sqrt definition: y < p and y^2 ≡ 0 (mod p)
    assert(y < p() && field_canonical(y * y) == 0);

    // If y^2 ≡ 0 (mod p) and p is prime, then y ≡ 0 (mod p).
    // Since y < p, we have y = 0.
    assert(y == 0) by {
        axiom_p_is_prime();
        lemma_euclid_prime(y, y, p());
        lemma_small_mod(y, p());
    }
}

/// Lemma: canonical_sqrt(0) = 0.
pub proof fn lemma_canonical_sqrt_zero()
    ensures
        canonical_sqrt(0) == 0,
{
    lemma_field_sqrt_zero();
    let s1 = field_sqrt(0);
    assert(s1 == 0);

    // field_neg(0) == 0
    assert(field_neg(0) == 0) by {
        p_gt_2();
        assert(field_neg(0) == (p() - (0nat % p())) as nat % p());
        lemma_mod_self_0(p() as int);
    }

    // s1 is even (0 % 2 == 0), so canonical_sqrt returns s1.
    assert(canonical_sqrt(0) == s1);
}

/// Lemma: canonical_montgomery_lift(0) is the (0,0) 2-torsion point.
pub proof fn lemma_canonical_montgomery_lift_zero()
    ensures
        canonical_montgomery_lift(0) == (MontgomeryAffine::Finite { u: 0, v: 0 }),
{
    lemma_canonical_sqrt_zero();
    assert(montgomery_rhs(0) == 0) by {
        let A = fe51_as_canonical_nat(&MONTGOMERY_A);
        let u2 = field_mul(0, 0);
        let u3 = field_mul(u2, 0);
        let Au2 = field_mul(A, u2);
        assert(montgomery_rhs(0) == field_add(field_add(u3, Au2), 0));
        p_gt_2();
        lemma_small_mod(0, p());
        assert(0nat % p() == 0nat);
        assert(u2 == 0) by {
            lemma_field_mul_zero_left(0, 0);
        }
        assert(u3 == 0) by {
            lemma_field_mul_zero_left(u2, 0);
        }
        assert(Au2 == 0) by {
            lemma_field_mul_zero_right(A, u2);
        }
        assert(field_add(field_add(0, 0), 0) == 0) by {
            p_gt_2();
            assert(field_add(0, 0) == (0nat + 0nat) % p());
            assert(field_add(0, 0) == 0);
            assert(field_add(0, 0) + 0 == 0);
            assert(field_add(field_add(0, 0), 0) == (0nat + 0nat) % p());
            assert(field_add(field_add(0, 0), 0) == 0);
        }
        assert(montgomery_rhs(0) == 0);
    }
    assert(canonical_montgomery_lift(0) == MontgomeryAffine::Finite {
        u: 0nat % p(),
        v: canonical_sqrt(montgomery_rhs(0)),
    });
    assert(0nat % p() == 0nat) by {
        p_gt_2();
        lemma_mod_self_0(p() as int);
    }
    assert(canonical_sqrt(montgomery_rhs(0)) == 0);
}

/// Lemma: the (0,0) point doubles to infinity under montgomery_add.
pub proof fn lemma_montgomery_add_zero_point_doubles_to_infinity()
    ensures
        ({
            let P = canonical_montgomery_lift(0);
            montgomery_add(P, P) == MontgomeryAffine::Infinity
        }),
{
    let P = canonical_montgomery_lift(0);
    assert(P == MontgomeryAffine::Finite { u: 0, v: 0 }) by {
        lemma_canonical_montgomery_lift_zero();
    }
    // Unfold montgomery_add on (0,0)+(0,0): it matches the P = -Q case.
    assert(montgomery_add(P, P) == MontgomeryAffine::Infinity);
}

/// Lemma: scalar multiplication of the (0,0) 2-torsion point stays in {∞, P}.
pub proof fn lemma_montgomery_scalar_mul_zero_point_closed(n: nat)
    ensures
        ({
            let P = canonical_montgomery_lift(0);
            let R = montgomery_scalar_mul(P, n);
            R == MontgomeryAffine::Infinity || R == P
        }),
    decreases n,
{
    let P = canonical_montgomery_lift(0);
    if n == 0 {
        assert(montgomery_scalar_mul(P, 0) == MontgomeryAffine::Infinity);
    } else {
        lemma_montgomery_scalar_mul_zero_point_closed((n - 1) as nat);
        let R_prev = montgomery_scalar_mul(P, (n - 1) as nat);
        assert(R_prev == MontgomeryAffine::Infinity || R_prev == P);
        // Unfold scalar multiplication: [n]P = P + [n-1]P
        assert(montgomery_scalar_mul(P, n) == montgomery_add(P, R_prev));
        if R_prev == MontgomeryAffine::Infinity {
            // P + ∞ = P (by definition of montgomery_add)
            assert(montgomery_add(P, MontgomeryAffine::Infinity) == P);
            assert(montgomery_scalar_mul(P, n) == P);
        } else {
            // R_prev == P, so P + P = ∞
            assert(montgomery_scalar_mul(P, n) == MontgomeryAffine::Infinity) by {
                lemma_montgomery_add_zero_point_doubles_to_infinity();
            }
        }
    }
}

/// Lemma: u-coordinate of any scalar multiple of canonical_montgomery_lift(0) is 0.
pub proof fn lemma_u_coordinate_scalar_mul_canonical_lift_zero(n: nat)
    ensures
        ({
            let P = canonical_montgomery_lift(0);
            u_coordinate(montgomery_scalar_mul(P, n)) == 0
        }),
{
    lemma_montgomery_scalar_mul_zero_point_closed(n);
    lemma_canonical_montgomery_lift_zero();
    let P = canonical_montgomery_lift(0);
    let R = montgomery_scalar_mul(P, n);
    if R == MontgomeryAffine::Infinity {
        assert(u_coordinate(MontgomeryAffine::Infinity) == 0);
    } else {
        assert(R == P);
        assert(P == MontgomeryAffine::Finite { u: 0, v: 0 });
        assert(u_coordinate(MontgomeryAffine::Finite { u: 0, v: 0 }) == 0);
    }
}

/// Lemma: u-coordinate of any scalar multiple of a canonical lift is reduced (< p).
///
/// This follows from:
/// 1. canonical_montgomery_lift produces points with u < p (uses u % p())
/// 2. montgomery_add uses field operations which preserve u < p
/// 3. By induction, all scalar multiples have u < p
///
/// This lemma is used to show that `(u_coordinate(...) % p()) == u_coordinate(...)`,
/// which allows us to drop the redundant `% p()` when converting from projective representation
/// to u-coordinate equality.
pub proof fn lemma_canonical_scalar_mul_u_coord_reduced(u0: nat, n: nat)
    requires
        u0 != 0,
    ensures
        ({
            let P = canonical_montgomery_lift(u0);
            let R = montgomery_scalar_mul(P, n);
            u_coordinate(R) < p()
        }),
    decreases n,
{
    let P = canonical_montgomery_lift(u0);
    let R = montgomery_scalar_mul(P, n);
    p_gt_2();

    if n == 0 {
        // montgomery_scalar_mul(P, 0) = Infinity
        // u_coordinate(Infinity) = 0 < p()
        assert(R == MontgomeryAffine::Infinity);
        assert(u_coordinate(R) == 0);
    } else {
        // montgomery_scalar_mul(P, n) = montgomery_add(P, montgomery_scalar_mul(P, n-1))
        let R_prev = montgomery_scalar_mul(P, (n - 1) as nat);
        lemma_canonical_scalar_mul_u_coord_reduced(u0, (n - 1) as nat);
        assert(u_coordinate(R_prev) < p());

        // Now R = montgomery_add(P, R_prev)
        // montgomery_add returns either Infinity (u-coord 0) or Finite with u computed
        // via field_* operations which always return values < p()
        lemma_montgomery_add_u_coord_reduced(P, R_prev, u0);
    }
}

/// Helper lemma: montgomery_add preserves the property that u-coordinates are < p()
proof fn lemma_montgomery_add_u_coord_reduced(P: MontgomeryAffine, Q: MontgomeryAffine, u0: nat)
    requires
        u0 != 0,
        P == canonical_montgomery_lift(u0),
        u_coordinate(Q) < p(),
    ensures
        u_coordinate(montgomery_add(P, Q)) < p(),
{
    p_gt_2();
    let R = montgomery_add(P, Q);

    // P = canonical_montgomery_lift(u0) means P = Finite{u: u0 % p(), v: ...}
    // So u_coordinate(P) = u0 % p() < p()
    assert(u_coordinate(P) < p()) by {
        // canonical_montgomery_lift creates Finite{u: u % p(), v: ...}
        lemma_mod_division_less_than_divisor(u0 as int, p() as int);
    }

    match R {
        MontgomeryAffine::Infinity => {
            assert(u_coordinate(R) == 0);
        },
        MontgomeryAffine::Finite { u, v } => {
            // u is computed via field_sub which returns a value < p()
            // The montgomery_add formula computes u3 = field_sub(field_sub(...), ...)
            // All field_* operations return values % p() which are < p()
            assert(u < p()) by {
                // field_sub(a, b) = (((a % p()) + p()) - (b % p())) % p() < p()
                lemma_mod_division_less_than_divisor(u as int, p() as int);
            }
        },
    }
}

// =============================================================================
// ELLIGATOR2: u = -1 is unreachable
// =============================================================================
/// Axiom: 486660 (= A - 2) is not a quadratic residue mod p.
/// Equivalently, Legendre symbol (486660 / p) = -1.
/// Verified by runtime test `test_486660_not_qr`.
pub proof fn axiom_486660_not_quadratic_residue()
    ensures
        !is_square(486660nat),
{
    admit();
}

/// Axiom: 2 * 486661 (= 2*(A-1)) is not a quadratic residue mod p.
/// Since p ≡ 5 (mod 8), 2 is a non-QR; 486661 = A-1 is a QR; product is non-QR.
/// Verified by runtime test `test_2_times_486661_not_qr`.
pub proof fn axiom_2_times_486661_not_qr()
    ensures
        !is_square((2nat * 486661nat) % p()),
{
    admit();
}

/// Lemma: the modular inverse of a non-zero non-QR is also a non-QR.
///
/// Proof: suppose inv(a) is QR with witness y² = inv(a).
/// Then inv(y²) = inv(inv(a)) = a, and inv(y²) = inv(y)², so inv(y)² = a,
/// meaning a is QR — contradiction.
pub proof fn lemma_inv_preserves_non_qr(a: nat)
    requires
        !is_square(field_canonical(a)),
        field_canonical(a) != 0,
    ensures
        !is_square(field_inv(field_canonical(a))),
{
    let a_mod = field_canonical(a);
    let inv_a = field_inv(a_mod);

    if is_square(inv_a) {
        // Witness: y such that y² ≡ inv(a) (mod p)
        let y: nat = choose|y: nat| (#[trigger] field_mul(y, y)) == field_canonical(inv_a);
        p_gt_2();

        let y2 = field_square(y);

        assert(y2 == inv_a) by {
            lemma_mod_bound(a as int, p() as int);
            lemma_small_mod(a_mod, p());
            assert(inv_a < p()) by {
                field_inv_property(a_mod);
            }
            lemma_small_mod(inv_a, p());
        }

        // inv(inv(a)) = a_mod, so inv(y²) = a_mod
        assert(field_inv(y2) == a_mod) by {
            lemma_inv_of_inv(a_mod);
            lemma_mod_bound(a as int, p() as int);
            lemma_small_mod(a_mod, p());
        }

        // inv(y²) = inv(y)²
        assert(field_inv(y2) == field_square(field_inv(y))) by {
            lemma_inv_of_product(y, y);
        }

        // So inv(y)² = a_mod, meaning a is QR — contradiction
        assert(is_square(a_mod)) by {
            assert(exists|w: nat| (#[trigger] field_mul(w, w)) == field_canonical(a_mod)) by {
                let w = field_inv(y);
                assert(field_mul(w, w) == field_square(w));
                assert(a_mod == field_canonical(a_mod)) by {
                    lemma_small_mod(a_mod, p());
                }
            }
        }
        assert(false);
    }
}

/// Helper: fe51_as_canonical_nat(&MONTGOMERY_A) == 486662.
proof fn lemma_montgomery_a_value()
    ensures
        fe51_as_canonical_nat(&MONTGOMERY_A) == 486662nat,
{
    // MONTGOMERY_A.limbs = [486662, 0, 0, 0, 0]
    // u64_5_as_nat = 486662 + pow2(51)*0 + ... = 486662
    let limbs = MONTGOMERY_A.limbs;
    assert(limbs[0] == 486662u64);
    assert(limbs[1] == 0u64 && limbs[2] == 0u64 && limbs[3] == 0u64 && limbs[4] == 0u64);
    assert(u64_5_as_nat(limbs) == 486662nat) by {
        // All higher limbs are 0, so u64_5_as_nat = limbs[0] + 0 + 0 + 0 + 0
        lemma2_to64();
        assert(pow2(51) > 0 && pow2(102) > 0 && pow2(153) > 0 && pow2(204) > 0) by {
            lemma_pow2_strictly_increases(5, 51);
            lemma_pow2_strictly_increases(5, 102);
            lemma_pow2_strictly_increases(5, 153);
            lemma_pow2_strictly_increases(5, 204);
        }
    }
    assert(fe51_as_canonical_nat(&MONTGOMERY_A) == 486662nat) by {
        lemma_p_gt_small(486662nat);
        lemma_small_mod(486662nat, p());
    }
}

// Local helper specs for by(compute_only) evaluation.
spec fn local_pow2_m(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        2 * local_pow2_m((n - 1) as nat)
    }
}

spec fn local_u5_nat_m(limbs: [u64; 5]) -> nat {
    (limbs[0] as nat) + local_pow2_m(51) * (limbs[1] as nat) + local_pow2_m(102) * (limbs[2] as nat)
        + local_pow2_m(153) * (limbs[3] as nat) + local_pow2_m(204) * (limbs[4] as nat)
}

spec fn local_p_m() -> nat {
    (local_pow2_m(255) - 19) as nat
}

proof fn lemma_bridge_local_pow2_m()
    ensures
        local_pow2_m(51) == pow2(51),
        local_pow2_m(102) == pow2(102),
        local_pow2_m(153) == pow2(153),
        local_pow2_m(204) == pow2(204),
        local_pow2_m(255) == pow2(255),
{
    assert(local_pow2_m(51) == 2251799813685248nat) by (compute_only);
    assert(pow2(51) == 2251799813685248nat) by {
        lemma2_to64_rest();
    };
    assert(local_pow2_m(102) == local_pow2_m(51) * local_pow2_m(51)) by (compute_only);
    assert(pow2(102) == pow2(51) * pow2(51)) by {
        lemma_pow2_adds(51, 51);
    };
    assert(local_pow2_m(153) == local_pow2_m(51) * local_pow2_m(102)) by (compute_only);
    assert(pow2(153) == pow2(51) * pow2(102)) by {
        lemma_pow2_adds(51, 102);
    };
    assert(local_pow2_m(204) == local_pow2_m(51) * local_pow2_m(153)) by (compute_only);
    assert(pow2(204) == pow2(51) * pow2(153)) by {
        lemma_pow2_adds(51, 153);
    };
    assert(local_pow2_m(255) == local_pow2_m(51) * local_pow2_m(204)) by (compute_only);
    assert(pow2(255) == pow2(51) * pow2(204)) by {
        lemma_pow2_adds(51, 204);
    };
}

/// MONTGOMERY_A_NEG encodes field_neg(MONTGOMERY_A) = p - 486662 in 51-bit limb form.
///
/// Proved by concrete computation with by(compute_only).
pub proof fn lemma_montgomery_a_neg_is_neg_a()
    ensures
        fe51_as_canonical_nat(&MONTGOMERY_A_NEG) == field_neg(fe51_as_canonical_nat(&MONTGOMERY_A)),
{
    assert(fe51_as_canonical_nat(&MONTGOMERY_A_NEG) == field_neg(
        fe51_as_canonical_nat(&MONTGOMERY_A),
    )) by {
        assert({
            let lp = local_p_m();
            let neg_a_val = local_u5_nat_m(MONTGOMERY_A_NEG.limbs) % lp;
            let a_val = local_u5_nat_m(MONTGOMERY_A.limbs) % lp;
            neg_a_val == ((lp - (a_val % lp)) as nat) % lp
        }) by (compute_only);

        lemma_bridge_local_pow2_m();
    };
}

/// Helper: show that small constants (< 1048576) are less than p.
proof fn lemma_p_gt_small(n: nat)
    requires
        n < 1048576,
    ensures
        n < p(),
{
    // pow2(21) = 2097152 > 1048576. pow2(255) >= pow2(21), so p() > 1048576 > n.
    pow255_gt_19();
    lemma2_to64();
    assert(pow2(5) == 32nat) by {
        lemma2_to64();
    }
    vstd::arithmetic::power2::lemma_pow2_adds(5, 5);
    assert(pow2(10) == 1024nat);
    vstd::arithmetic::power2::lemma_pow2_adds(10, 10);
    assert(pow2(20) == 1048576nat);
    vstd::arithmetic::power2::lemma_pow2_adds(20, 1);
    assert(pow2(1) == 2nat) by {
        lemma2_to64();
    }
    assert(pow2(21) == 2097152nat);
    lemma_pow2_strictly_increases(21, 255);
    // pow2(255) > pow2(21) = 2097152, so p = pow2(255) - 19 >= 2097134 > 1048576 > n
}

/// Algebraic lemma for the square branch: when d = -1 (mod p),
///   d * (d² + A*d + 1) = A - 2 = 486660 (mod p).
proof fn lemma_eps_when_d_is_minus_one(d: nat, A: nat)
    requires
        d == field_sub(0, 1),
        A == 486662nat,
    ensures
        ({
            let d_sq = field_square(d);
            let A_d = field_mul(A, d);
            let inner = field_add(field_add(d_sq, A_d), 1);
            let eps = field_mul(d, inner);
            eps == 486660nat
        }),
{
    let pp = p();
    p_gt_2();
    lemma_p_gt_small(486662nat);

    // d = neg(1) = p - 1
    assert(d == field_neg(1)) by {
        lemma_small_mod(0nat, pp);
        lemma_small_mod(1nat, pp);
    }

    // d² = (-1)² = 1² = 1
    let d_sq = field_square(d);
    assert(d_sq == 1nat) by {
        lemma_neg_square_eq(1);
        lemma_small_mod(1nat, pp);
        assert(field_square(d) == field_square(1nat % pp));
        assert(field_square(1nat) == (1nat * 1nat) % pp);
        lemma_small_mod(1nat, pp);
    }

    // A*d = A*(-1) = -A
    let A_d = field_mul(A, d);
    assert(A_d == field_neg(A)) by {
        lemma_field_mul_neg(A, 1);
        assert(field_mul(A, field_neg(1)) == field_neg(field_mul(A, 1)));
        lemma_field_mul_one_right(A);
        lemma_small_mod(A, pp);
    }

    // d² + A*d = 1 + neg(A) = sub(1, A)
    let sum1 = field_add(d_sq, A_d);
    assert(sum1 == field_sub(1, A)) by {
        lemma_field_sub_eq_add_neg(1, A);
    }

    // Compute sub(1, A) = p - 486661 concretely
    let val_486661 = (pp - 486661) as nat;
    assert(sum1 == val_486661) by {
        lemma_small_mod(1nat, pp);
        lemma_small_mod(A, pp);
        lemma_p_gt_small(486662nat);
        lemma_small_mod(val_486661, pp);
    }

    // inner = add(sum1, 1) = add(p - 486661, 1) = p - 486660
    let inner = field_add(sum1, 1);
    let val_486660 = (pp - 486660) as nat;
    assert(inner == val_486660) by {
        lemma_p_gt_small(486660nat);
        lemma_small_mod(val_486660, pp);
    }

    // eps = mul(neg(1), inner) = neg(inner) = neg(p - 486660) = 486660
    let eps = field_mul(d, inner);
    assert(eps == 486660nat) by {
        lemma_neg_one_times_is_neg(inner);
        // eps == neg(inner) == neg(p - 486660) == 486660
        lemma_p_gt_small(486660nat);
        lemma_small_mod(val_486660, pp);
        lemma_small_mod(486660nat, pp);
    }
}

/// If d = -A/(1+2r²) and d+A = 1 (mod p), then r² = inv(2·(A-1)).
proof fn lemma_nonsquare_branch_r_sq(A: nat, d: nat, d_denom: nat, r_sq: nat)
    requires
        A == 486662nat,
        r_sq < p(),
        d_denom == field_add(1, field_mul(2, r_sq)),
        d == field_mul(field_neg(A), field_inv(d_denom)),
        field_neg(field_add(d, A)) == field_sub(0, 1),
    ensures
        r_sq == field_inv((2nat * 486661nat) % p()),
{
    let pp = p();
    p_gt_2();

    // Step 1: field_add(d, A) == 1
    let dpa = field_add(d, A);
    assert(field_sub(0, 1) == (pp - 1) as nat) by {
        lemma_small_mod(0, pp);
        lemma_small_mod(1, pp);
        lemma_small_mod((pp - 1) as nat, pp);
    };
    assert(dpa < pp) by {
        lemma_mod_bound((d + A) as int, pp as int);
    };
    if dpa == 0 {
        assert(field_neg(0) == 0nat) by {
            lemma_mod_self_0(pp as int);
        };
        assert(false);
    }
    assert(field_neg(dpa) == (pp - dpa) as nat) by {
        lemma_small_mod(dpa, pp);
        lemma_small_mod((pp - dpa) as nat, pp);
    };
    assert(dpa == 1);

    // Step 2: d_denom % p != 0 (otherwise d=0, d+A=A=486662≠1)
    assert(d_denom % pp != 0) by {
        if d_denom % pp == 0 {
            assert(field_inv(d_denom) == 0);
            lemma_field_mul_zero_right(field_neg(A), field_inv(d_denom));
            assert(d == 0);
            lemma_p_gt_small(A);
            assert(field_add(0, A) == A) by {
                lemma_small_mod(A, pp);
            };
            assert(false);
        }
    };

    // Step 3: d * d_denom = -A (by associativity + inverse cancellation)
    let neg_a = field_neg(A);
    let inv_dd = field_inv(d_denom);
    lemma_field_mul_assoc(neg_a, inv_dd, d_denom);
    assert(field_mul(field_mul(neg_a, inv_dd), d_denom) == field_mul(
        neg_a,
        field_mul(inv_dd, d_denom),
    ));
    assert(d == field_mul(neg_a, inv_dd));
    lemma_inv_mul_cancel(d_denom);
    assert(field_mul(inv_dd, d_denom) == 1);
    lemma_field_mul_one_right(neg_a);
    assert(neg_a < pp) by {
        lemma_mod_bound((pp - A % pp) as int, pp as int);
    };
    lemma_small_mod(neg_a, pp);
    assert(field_mul(neg_a, 1) == neg_a);
    assert(field_mul(d, d_denom) == neg_a);

    // Step 4: (d+A) * d_denom = d*d_denom + A*d_denom (distributivity)
    lemma_field_mul_distributes_over_add(d_denom, d, A);
    lemma_field_mul_comm(d_denom, d);
    lemma_field_mul_comm(d_denom, A);
    lemma_field_mul_comm(d_denom, dpa);
    assert(field_mul(dpa, d_denom) == field_add(field_mul(d, d_denom), field_mul(A, d_denom)));

    // Step 5: Since dpa=1, 1*d_denom = d_denom
    lemma_field_mul_one_left(d_denom);
    assert(d_denom < pp) by {
        lemma_mod_bound((1 + (2 * r_sq) % pp) as int, pp as int);
    };
    lemma_small_mod(d_denom, pp);
    assert(field_mul(dpa, d_denom) == d_denom);

    // Step 6: d_denom = -A + A*d_denom
    assert(d_denom == field_add(field_neg(A), field_mul(A, d_denom)));

    // Step 7: A*(1 + 2*r_sq) = A + A*2*r_sq (expand via distributivity)
    let two_rsq = field_mul(2, r_sq);
    lemma_field_mul_distributes_over_add(A, 1, two_rsq);
    lemma_field_mul_one_right(A);
    lemma_p_gt_small(A);
    lemma_small_mod(A, pp);
    let a_two_rsq = field_mul(A, two_rsq);

    // Step 8: -A + (A + A*2*r_sq) = (-A + A) + A*2*r_sq = 0 + A*2*r_sq = A*2*r_sq
    lemma_field_add_assoc(field_neg(A), A, a_two_rsq);
    assert(field_neg(A) == (pp - A) as nat) by {
        lemma_small_mod(A, pp);
        lemma_small_mod((pp - A) as nat, pp);
    };
    assert(field_add(field_neg(A), A) == 0) by {
        lemma_mod_self_0(pp as int);
    };
    assert(a_two_rsq < pp) by {
        lemma_mod_bound((A * two_rsq) as int, pp as int);
    };
    assert(field_add(0, a_two_rsq) == a_two_rsq) by {
        lemma_small_mod(a_two_rsq, pp);
    };
    assert(d_denom == a_two_rsq);

    // Step 9: A*2*r_sq = (A*2)*r_sq by associativity
    lemma_field_mul_assoc(A, 2, r_sq);
    assert(a_two_rsq == field_mul(field_mul(A, 2), r_sq));
    assert(field_mul(A, 2) == 973324nat) by {
        assert(486662nat * 2 == 973324nat) by (compute);
        lemma_p_gt_small(973324nat);
        lemma_small_mod(973324nat, pp);
    };

    // Step 10: Subtract 2*r_sq from both sides: 1 = (973324 - 2)*r_sq = 973322*r_sq
    assert(two_rsq < pp) by {
        lemma_mod_bound((2 * r_sq) as int, pp as int);
    };
    assert(1nat < pp);
    lemma_field_sub_add_cancel(1, two_rsq);
    assert(field_sub(d_denom, two_rsq) == 1);
    assert(field_sub(field_mul(973324nat, r_sq), two_rsq) == 1);
    lemma_field_mul_distributes_over_sub_right(973324nat, 2nat, r_sq);
    assert(field_sub(973324nat, 2nat) == 973322nat) by {
        lemma_small_mod(973324nat, pp);
        lemma_small_mod(2nat, pp);
        lemma_mod_add_multiples_vanish(973322int, pp as int);
        lemma_small_mod(973322nat, pp);
    };
    assert(field_mul(973322nat, r_sq) == 1);

    // Step 11: 973322 = 2*486661, so r_sq = inv(2*486661)
    assert(973322nat == 2nat * 486661nat) by (compute);
    let two_a1 = (2nat * 486661nat) % pp;
    assert(two_a1 == 973322nat) by {
        lemma_small_mod(973322nat, pp);
    };
    assert(field_mul(two_a1, r_sq) == 1);

    lemma_field_mul_comm(two_a1, r_sq);
    assert(1nat % pp == 1nat) by {
        lemma_small_mod(1nat, pp);
    };
    lemma_solve_for_left_factor(r_sq, two_a1, 1);
    lemma_field_mul_one_left(field_inv(two_a1));
    field_inv_property(two_a1);
    lemma_small_mod(field_inv(two_a1), pp);
    lemma_small_mod(r_sq, pp);
}

// =============================================================================
// EDWARDS → MONTGOMERY MAP AXIOMS
//
// Reference: <https://www.rfc-editor.org/rfc/rfc7748#section-4.1>
// =============================================================================
/// Axiom: The Edwards-to-Montgomery map sends valid Edwards points to valid Montgomery u-coordinates.
///
/// If (x, y) is on the twisted Edwards curve -x² + y² = 1 + d·x²·y²,
/// then u = (1+y)/(1-y) satisfies u³ + Au² + u being a quadratic residue (mod p).
///
/// Reference: <https://www.rfc-editor.org/rfc/rfc7748#section-4.1>
pub proof fn axiom_edwards_to_montgomery_preserves_validity(x: nat, y: nat)
    requires
        is_on_edwards_curve(x, y),
    ensures
        is_valid_u_coordinate(montgomery_u_from_edwards_y(y)),
{
    admit();
}

/// Axiom: Elligator2 always outputs a valid Montgomery u-coordinate (on the curve, not the twist).
pub proof fn axiom_elligator_encode_outputs_valid_u(r: nat)
    ensures
        is_valid_u_coordinate(spec_elligator_encode(r)),
{
    admit();
}

/// Axiom: For a valid Montgomery u-coordinate (and u != -1), the birational map
/// y = (u-1)/(u+1) yields a valid Edwards y-coordinate.
///
/// This is one direction of the Montgomery↔Edwards birational equivalence.
pub proof fn axiom_montgomery_valid_u_implies_edwards_y_valid(u: nat)
    requires
        is_valid_u_coordinate(u),
        u != field_sub(0, 1),
    ensures
        is_valid_edwards_y_coordinate(edwards_y_from_montgomery_u(u)),
{
    admit();
}

/// Elligator2 encoding never produces u = -1 (mod p).
///
/// Proof by contradiction in each branch of `spec_elligator_encode`:
/// - Square branch (u = d): d = -1 ⟹ eps ≡ 486660 (non-QR), contradicts square branch.
/// - Non-square branch (u = -(d+A)): u = -1 ⟹ r² = inv(2*486661) (non-QR), contradicts r² being QR.
pub proof fn lemma_elligator_never_minus_one(r: nat)
    ensures
        !is_equal_to_minus_one(spec_elligator_encode(r)),
{
    axiom_486660_not_quadratic_residue();

    let A = fe51_as_canonical_nat(&MONTGOMERY_A);
    let r_sq = field_square(r);
    let two_r_sq = field_mul(2, r_sq);
    let d_denom = field_add(1, two_r_sq);
    let d = field_mul(field_neg(A), field_inv(d_denom));
    let d_sq = field_square(d);
    let A_d = field_mul(A, d);
    let inner = field_add(field_add(d_sq, A_d), 1);
    let eps = field_mul(d, inner);

    let minus_one = field_sub(0, 1);

    if is_square(eps) {
        // Square branch: u = d. Suppose d == -1.
        if d == minus_one {
            assert(eps == 486660nat) by {
                lemma_montgomery_a_value();
                lemma_eps_when_d_is_minus_one(d, A);
            }
            // is_square(eps) with eps = 486660 implies is_square(486660) — contradiction
            assert(is_square(486660nat)) by {
                p_gt_2();
                lemma_p_gt_small(486660nat);
                lemma_small_mod(eps, p());
                lemma_small_mod(486660nat, p());
                let y_w: nat = choose|y: nat| (#[trigger] (y * y) % p()) == (eps % p());
            }
            assert(false);
        }
    } else {
        // Non-square branch: u = -(d + A). Suppose u == -1.
        let u = field_neg(field_add(d, A));
        if u == minus_one {
            let two_a1 = (2nat * 486661nat) % p();

            // r² = inv(2*486661) by axiom
            assert(r_sq < p()) by {
                p_gt_2();
                lemma_mod_bound((r * r) as int, p() as int);
            };
            assert(r_sq == field_inv(two_a1)) by {
                lemma_montgomery_a_value();
                lemma_nonsquare_branch_r_sq(A, d, d_denom, r_sq);
            }

            // inv(2*486661) is not a QR
            assert(!is_square(field_inv(two_a1))) by {
                axiom_2_times_486661_not_qr();
                assert(two_a1 != 0nat) by {
                    p_gt_2();
                    lemma_p_gt_small(973322nat);
                    assert(2nat * 486661nat == 973322nat) by (compute);
                    lemma_small_mod(973322nat, p());
                }
                lemma_inv_preserves_non_qr(2nat * 486661nat);
            }

            // But r² is always a QR — contradiction
            assert(is_square(r_sq)) by {
                p_gt_2();
                assert(exists|y: nat| (#[trigger] field_mul(y, y)) == field_canonical(r_sq)) by {
                    assert(field_mul(r, r) < p()) by {
                        lemma_mod_bound((r * r) as int, p() as int);
                    }
                    assert(r_sq == field_canonical(r_sq)) by {
                        lemma_small_mod(r_sq, p());
                    }
                }
            }
            assert(false);
        }
    }
}

/// Lemma: The Ed25519 basepoint maps to the X25519 basepoint under the Edwards→Montgomery map.
///
/// The map φ sends (x, y) to u = (1+y)/(1-y). For the Ed25519 basepoint, φ(B).u = 9.
/// Proved by concrete modular arithmetic: 9·(1-y) ≡ (1+y) (mod p).
///
/// Reference: <https://www.rfc-editor.org/rfc/rfc7748#section-4.1>
pub proof fn lemma_edwards_basepoint_maps_to_montgomery_basepoint()
    ensures
        montgomery_u_from_edwards_y(spec_ed25519_basepoint().1) == spec_x25519_basepoint_u(),
{
    let y_limbs: [u64; 5] = [
        1801439850948184u64,
        1351079888211148,
        450359962737049,
        900719925474099,
        1801439850948198,
    ];
    lemma_ed25519_basepoint_y();
    let y = spec_ed25519_basepoint().1;
    assert(y == u64_5_as_nat(y_limbs));

    let pp = p();

    // Key fact: the basepoint y-coordinate satisfies 5y = 4p + 4 (i.e. y = 4/5 mod p)
    assert(5 * y == 4 * pp + 4) by {
        assert({
            let y_local = local_u5_nat_m(
                [
                    1801439850948184u64,
                    1351079888211148u64,
                    450359962737049u64,
                    900719925474099u64,
                    1801439850948198u64,
                ],
            );
            let lp = local_p_m();
            5 * y_local == 4 * lp + 4
        }) by (compute_only);
        lemma_bridge_local_pow2_m();
    };

    // From 5y = 4p+4: y < p (since y = (4p+4)/5 < p for p > 1)
    assert(y < pp) by {
        p_gt_2();
    };

    let denom = field_sub(1nat, y);
    let numer = field_add(1nat, y);

    // Since 5y = 4p+4 and p > 9: y > 1 and y < p-1
    assert(y > 1) by {
        p_gt_2();
    };
    assert(y < pp - 1) by {
        lemma_p_gt_small(9);
    };
    assert(1 + y < pp);

    // field_sub(1, y) = ((1%p + p - y%p) as nat) % p
    // Since 1 < p and y < p: this simplifies to (1 + p - y) % p = p + 1 - y (since y > 1)
    assert(field_canonical(1nat) == 1nat) by {
        lemma_p_gt_small(1);
        lemma_small_mod(1nat, pp);
    };
    assert(field_canonical(y) == y) by {
        lemma_small_mod(y, pp);
    };
    assert(denom == ((1 + pp - y) as nat) % pp);
    let sub_val: nat = (pp + 1 - y) as nat;
    assert(sub_val < pp);
    assert(denom == sub_val) by {
        lemma_small_mod(sub_val, pp);
    };

    // field_add(1, y) = (1 + y) % p = 1 + y (since 1 + y < p)
    assert(numer == 1 + y) by {
        lemma_small_mod(1 + y, pp);
    };

    // denom != 0 follows from y < p (so p+1-y >= 2)
    assert(denom != 0);

    // 9*denom = 9(p+1-y) = 9p + 9 - 9y = 9p + 9 - 9y
    // numer + p = 1 + y + p
    // Check: 9(p+1-y) = (1+y) + p  ⟺  9p+9-9y = p+1+y  ⟺  8p+8 = 10y  ⟺  4p+4 = 5y ✓
    assert(9 * denom == numer + pp) by {
        assert(9 * ((pp + 1 - y) as nat) == (1 + y) + pp);
    };

    // field_mul(9, denom) = (9*denom) % p = (numer + p) % p = numer
    assert(field_mul(9nat, denom) == numer) by {
        p_gt_2();
        assert(numer < pp);
        assert(9 * denom == numer + pp);
        // (numer + 1*pp) % pp == numer % pp == numer
        lemma_mod_multiples_vanish(1, numer as int, pp as int);
        lemma_small_mod(numer, pp);
    };

    // Algebraic: numer = 9*denom implies (1+y)*inv(1-y) = 9
    assert(montgomery_u_from_edwards_y(y) == 9nat) by {
        assert(numer == field_mul(9nat, denom));
        assert(field_mul(field_mul(9nat, denom), field_inv(denom)) == field_mul(
            9nat,
            field_mul(denom, field_inv(denom)),
        )) by {
            lemma_field_mul_assoc(9nat, denom, field_inv(denom));
        };
        assert(field_mul(denom, field_inv(denom)) == 1) by {
            lemma_inv_mul_cancel(denom);
            lemma_field_mul_comm(field_inv(denom), denom);
        };
        assert(field_mul(9nat, 1) == 9nat) by {
            lemma_field_mul_one_right(9nat);
            lemma_p_gt_small(9);
            lemma_small_mod(9, p());
        };
    };

    // spec_x25519_basepoint_u() == 9
    lemma_x25519_basepoint_u_is_9();
}

/// Axiom: The Edwards-to-Montgomery map commutes with scalar multiplication.
///
/// The map φ: Edwards → Montgomery is a group homomorphism:
///   φ([n]P_ed).u = [n](φ(P_ed).u)
///
/// Additionally ensures scalar multiplication preserves the curve (closure).
///
/// Reference: <https://www.rfc-editor.org/rfc/rfc7748#section-4.1>
pub proof fn axiom_edwards_to_montgomery_commutes_with_scalar_mul(x: nat, y: nat, n: nat)
    requires
        is_on_edwards_curve(x, y),
    ensures
// Scalar multiplication preserves the Edwards curve

        is_on_edwards_curve(edwards_scalar_mul((x, y), n).0, edwards_scalar_mul((x, y), n).1),
        // The Edwards-to-Montgomery map commutes with scalar multiplication
        montgomery_u_from_edwards_y(edwards_scalar_mul((x, y), n).1) == montgomery_scalar_mul_u(
            montgomery_u_from_edwards_y(y),
            n,
        ),
{
    admit();
}

} // verus!
#[cfg(test)]
mod test_qr_axioms {
    use num_bigint::BigUint;
    use num_traits::One;

    /// p = 2^255 - 19
    fn p() -> BigUint {
        (BigUint::one() << 255) - BigUint::from(19u32)
    }

    /// Euler's criterion: a is a QR mod p iff a^((p-1)/2) ≡ 1 (mod p)
    fn is_qr(a: &BigUint, p: &BigUint) -> bool {
        let exp = (p - BigUint::one()) / BigUint::from(2u32);
        a.modpow(&exp, p) == BigUint::one()
    }

    #[test]
    fn test_486660_not_qr() {
        let p = p();
        assert!(
            !is_qr(&BigUint::from(486660u32), &p),
            "486660 should NOT be a QR mod p"
        );
    }

    #[test]
    fn test_2_times_486661_not_qr() {
        let p = p();
        let val = (BigUint::from(2u32) * BigUint::from(486661u32)) % &p;
        assert!(!is_qr(&val, &p), "2*486661 should NOT be a QR mod p");
    }

    /// Modular inverse via Fermat's little theorem: a^(-1) = a^(p-2) mod p
    fn mod_inv(a: &BigUint, p: &BigUint) -> BigUint {
        a.modpow(&(p - BigUint::from(2u32)), p)
    }

    // test_edwards_basepoint_maps_to_montgomery_9 removed: now formally proved as
    // lemma_edwards_basepoint_maps_to_montgomery_basepoint.
}
