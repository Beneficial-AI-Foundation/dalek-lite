//! Lemmas and axioms for Montgomery curve operations
//!
//! This module provides the foundational axioms and derived lemmas needed to verify
//! the Montgomery ladder scalar multiplication algorithm.
//!
//! ## Architecture
//!
//! The verification uses a layered approach:
//!
//! 1. **Group Axioms** — Standard abelian group properties (associativity, identity, inverse)
//! 2. **X-Only Algorithm Axioms** — Correctness of xDBL and xADD formulas (Costello–Smith 2017)
//! 3. **Scalar Multiplication Lemmas** — Properties like `[m+n]P = [m]P + [n]P`
//! 4. **Projective Representation Lemmas** — Connecting projective (U:W) to affine u-coordinates
//!
//! ## X-Only Algorithm Axioms (xDBL, xADD)
//!
//! These are the key axioms that bridge the algebraic formulas to curve semantics:
//!
//! - **xADD Axiom**: The projective differential addition formula computes `P + Q`
//!   given projective representations of P, Q, and the affine u-coordinate of `P - Q`.
//!
//! - **xDBL Axiom**: The projective doubling formula computes `[2]P` given a
//!   projective representation of P.
//!
//! These axioms are purely algebraic contracts — they state *what* the formulas compute,
//! not *why* they are correct. The algebraic formulas themselves are defined in
//! `specs/montgomery_specs.rs` as `spec_xadd_projective` and `spec_xdbl_projective`.
//!
//! ## Group Axioms
//!
//! - `axiom_montgomery_add_associative`: (P + Q) + R = P + (Q + R)
//! - `axiom_montgomery_add_identity`: P + ∞ = P
//! - `axiom_montgomery_add_identity_left`: ∞ + P = P
//! - `axiom_montgomery_add_inverse`: P + (-P) = ∞

#![allow(unused)]
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::constants::MONTGOMERY_A;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use crate::specs::primality_specs::*;
use crate::specs::montgomery_specs::*;
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// GROUP AXIOMS
// =============================================================================
// These are fundamental properties of the Montgomery curve group structure.
// They follow from the algebraic definition but are complex to verify formally.

/// Axiom: Montgomery addition is associative
/// (P + Q) + R = P + (Q + R)
pub proof fn axiom_montgomery_add_associative(P: MontgomeryAffine, Q: MontgomeryAffine, R: MontgomeryAffine)
    ensures
        montgomery_add(montgomery_add(P, Q), R) == montgomery_add(P, montgomery_add(Q, R)),
{
    admit();
}

/// Axiom: Left identity element
/// ∞ + P = P
pub proof fn axiom_montgomery_add_identity_left(P: MontgomeryAffine)
    ensures
        montgomery_add(MontgomeryAffine::Infinity, P) == P,
{
    admit();
}

/// Axiom: Infinity is the identity element (right identity)
/// P + ∞ = P
pub proof fn axiom_montgomery_add_identity(P: MontgomeryAffine)
    ensures
        montgomery_add(P, MontgomeryAffine::Infinity) == P,
{
    admit();
}

/// Axiom: every point has an inverse
/// P + (-P) = ∞
pub proof fn axiom_montgomery_add_inverse(P: MontgomeryAffine)
    ensures
        montgomery_add(P, montgomery_neg(P)) == MontgomeryAffine::Infinity,
{
    admit();
}

// =============================================================================
// X-ONLY ALGORITHM AXIOMS (Costello–Smith 2017, Equations 9–10)
// =============================================================================
//
// These axioms state that the projective xDBL and xADD formulas (defined algebraically
// in `specs/montgomery_specs.rs`) compute the correct group operations on the
// Montgomery curve.
//
// ## Why Axioms?
//
// Proving these from first principles requires verifying the Montgomery curve
// addition law — a substantial algebraic effort involving the curve equation
// B·v² = u³ + A·u² + u. We treat them as axioms because:
//
// 1. The formulas are well-established (Costello–Smith 2017, RFC 7748).
// 2. The correctness proof is purely algebraic and orthogonal to the ladder logic.
// 3. This separation keeps the verification tractable and modular.
//
// ## References
//
// - Costello & Smith, "Montgomery curves and their arithmetic", 2017 (ePrint 2017/212)
// - RFC 7748: Elliptic Curves for Security

/// **xDBL Axiom**: Montgomery doubling formula correctness.
///
/// If `(U:W)` is a projective representation of point P, then `spec_xdbl_projective(U, W)`
/// produces a projective representation of `[2]P = P + P`.
///
/// ## Algebraic Statement
///
/// Let `(U':W') = spec_xdbl_projective(U, W)`. Then:
/// - If P is finite with u-coordinate u, then `U' = u([2]P) · W'` (projective encoding)
/// - If P is infinity (W=0), the formula degenerates appropriately
///
/// ## Reference
///
/// Costello–Smith 2017, Equation 10.
pub(crate) proof fn axiom_xdbl_projective_correct(P: MontgomeryAffine, U: nat, W: nat)
    requires
        projective_represents_montgomery_or_infinity_nats(U, W, P),
    ensures
        ({
            let (U2, W2) = spec_xdbl_projective(U, W);
            projective_represents_montgomery_or_infinity_nats(U2, W2, montgomery_add(P, P))
        }),
{
    admit();
}

/// **xADD Axiom**: Montgomery differential addition formula correctness.
///
/// If `(U_P:W_P)` represents P, `(U_Q:W_Q)` represents Q, and `affine_PmQ` is the
/// u-coordinate of `P - Q`, then `spec_xadd_projective(...)` produces a projective
/// representation of `P + Q`.
///
/// ## Preconditions
///
/// - `P ≠ Q` (use xDBL for doubling)
/// - `affine_PmQ ≠ 0` (the difference P-Q is not the 2-torsion point (0,0))
/// - `affine_PmQ` equals `u(P-Q)` or `u(Q-P)` (symmetric since u is even in v)
///
/// ## Algebraic Statement
///
/// Let `(U':W') = spec_xadd_projective(U_P, W_P, U_Q, W_Q, affine_PmQ)`. Then:
/// - `U' = u(P+Q) · W'` (projective encoding of the sum)
///
/// ## Reference
///
/// Costello–Smith 2017, Equation 9.
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
        projective_represents_montgomery_or_infinity_nats(U_P, W_P, P),
        projective_represents_montgomery_or_infinity_nats(U_Q, W_Q, Q),
        P != Q,
        affine_PmQ != 0,
        // u-coordinate is symmetric: u(P-Q) = u(Q-P) since u is invariant under negation
        affine_PmQ == spec_u_coordinate(montgomery_sub(P, Q))
            || affine_PmQ == spec_u_coordinate(montgomery_sub(Q, P)),
    ensures
        ({
            let (U_PpQ, W_PpQ) = spec_xadd_projective(U_P, W_P, U_Q, W_Q, affine_PmQ);
            projective_represents_montgomery_or_infinity_nats(U_PpQ, W_PpQ, montgomery_add(P, Q))
        }),
{
    admit();
}

// =============================================================================
// SCALAR MULTIPLICATION LEMMAS
// =============================================================================

/// Lemma: If an affine point has reduced u-coordinate (< p), then any projective representation
/// of its u-coordinate yields the same value via `spec_projective_u_coordinate`.
pub proof fn lemma_projective_represents_implies_u_coordinate(
    P_proj: crate::montgomery::ProjectivePoint,
    P_aff: MontgomeryAffine,
)
    requires
        projective_represents_montgomery_or_infinity(P_proj, P_aff),
    ensures
        spec_projective_u_coordinate(P_proj) == (spec_u_coordinate(P_aff) % p()),
{
    match P_aff {
        MontgomeryAffine::Infinity => {
            // Representation gives W == 0, and both u-coordinate conventions map ∞ to 0.
            assert(spec_field_element(&P_proj.W) == 0);
            assert(spec_projective_u_coordinate(P_proj) == 0);
            assert(spec_u_coordinate(P_aff) == 0);
            p_gt_2();
            lemma_small_mod(0, p());
            assert(spec_u_coordinate(P_aff) % p() == 0);
        },
        MontgomeryAffine::Finite { u, v: _ } => {
            let U = spec_field_element(&P_proj.U);
            let W = spec_field_element(&P_proj.W);
            assert(W != 0);
            assert(U == math_field_mul(u, W));
            assert(W % p() != 0) by {
                let W_raw = spec_field_element_as_nat(&P_proj.W);
                assert(W == W_raw % p());
                p_gt_2();
                lemma_mod_division_less_than_divisor(W_raw as int, p() as int);
                assert(W_raw % p() < p());
                lemma_small_mod(W, p());
                assert(W % p() == W);
            }

            // spec_projective_u_coordinate = U / W = (u*W) / W = u
            assert(spec_projective_u_coordinate(P_proj) == math_field_mul(U, math_field_inv(W)));
            assert(spec_projective_u_coordinate(P_proj) == math_field_mul(math_field_mul(u, W), math_field_inv(W)));

            lemma_field_mul_assoc(u, W, math_field_inv(W));
            assert(spec_projective_u_coordinate(P_proj) == math_field_mul(u, math_field_mul(W, math_field_inv(W))));

            lemma_inv_mul_cancel(W);
            lemma_field_mul_comm(math_field_inv(W), W);
            assert(math_field_mul(W, math_field_inv(W)) == 1);

            lemma_field_mul_one_right(u);
            assert(math_field_mul(u, 1) == u % p());
            assert(spec_projective_u_coordinate(P_proj) == u % p());
        },
    }
}

// -----------------------------------------------------------------------------
// Basic scalar multiplication lemmas
// -----------------------------------------------------------------------------

/// Lemma: scalar multiplication by 0 gives the identity (infinity)
///
/// NOTE: Currently unused; kept for completeness.
pub proof fn lemma_montgomery_scalar_mul_zero(P: MontgomeryAffine)
    ensures
        montgomery_scalar_mul(P, 0) == MontgomeryAffine::Infinity,
{
    // Follows directly from the definition
}

/// Lemma: scalar multiplication by 1 gives P
///
/// Used by: `lemma_montgomery_double_is_add`
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
/// Used by: `differential_add_and_double` proof
pub proof fn lemma_montgomery_scalar_mul_succ(P: MontgomeryAffine, n: nat)
    ensures
        montgomery_scalar_mul(P, n + 1) == montgomery_add(P, montgomery_scalar_mul(P, n)),
{
    // Follows directly from the recursive definition
}

/// Lemma: [2]P = P + P (doubling is adding point to itself)
///
/// NOTE: Currently unused; kept for reference.
pub proof fn lemma_montgomery_double_is_add(P: MontgomeryAffine)
    ensures
        montgomery_scalar_mul(P, 2) == montgomery_add(P, P),
{
    // [2]P = P + [1]P = P + P
    lemma_montgomery_scalar_mul_one(P);
    assert(montgomery_scalar_mul(P, 2) == montgomery_add(P, montgomery_scalar_mul(P, 1)));
    assert(montgomery_scalar_mul(P, 1) == P);
}

/// Lemma: scalar multiplication distributes over addition of scalars
/// [m + n]P = [m]P + [n]P
///
/// This is a fundamental property that follows from associativity and identity.
/// Proof by induction on m.
///
/// Used by: `differential_add_and_double` proof (to connect [k]P + [k+1]P = [2k+1]P)
pub proof fn lemma_montgomery_scalar_mul_add(P: MontgomeryAffine, m: nat, n: nat)
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
        axiom_montgomery_add_identity_left(montgomery_scalar_mul(P, n));
    } else {
        let m_minus_1 = (m - 1) as nat;

        lemma_montgomery_scalar_mul_add(P, m_minus_1, n);

        // [m+n]P = P + [m+n-1]P = P + [m-1+n]P
        assert(m + n >= 1);
        assert(m + n - 1 == m_minus_1 + n) by {
            assert(m >= 1);
            assert(m_minus_1 == m - 1);
        }
        assert(montgomery_scalar_mul(P, m + n) == montgomery_add(P, montgomery_scalar_mul(P, m_minus_1 + n)));

        // Expand IH on [m-1+n]P.
        assert(montgomery_scalar_mul(P, m_minus_1 + n) == montgomery_add(
            montgomery_scalar_mul(P, m_minus_1),
            montgomery_scalar_mul(P, n),
        ));

        axiom_montgomery_add_associative(P, montgomery_scalar_mul(P, m_minus_1), montgomery_scalar_mul(P, n));
        assert(montgomery_add(P, montgomery_add(montgomery_scalar_mul(P, m_minus_1), montgomery_scalar_mul(P, n)))
            == montgomery_add(montgomery_add(P, montgomery_scalar_mul(P, m_minus_1)), montgomery_scalar_mul(P, n)));

        // By definition: [m]P = P + [m-1]P.
        assert(montgomery_scalar_mul(P, m) == montgomery_add(P, montgomery_scalar_mul(P, m_minus_1)));

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
    ensures
        montgomery_scalar_mul(P, 2 * n) == montgomery_add(
            montgomery_scalar_mul(P, n),
            montgomery_scalar_mul(P, n),
        ),
{
    // [2n]P = [n + n]P = [n]P + [n]P
    assert(2 * n == n + n);
    lemma_montgomery_scalar_mul_add(P, n, n);
}

/// Lemma: [n]P + [n+1]P = [2n+1]P (adding consecutive scalar multiples)
///
/// NOTE: Currently unused; `lemma_montgomery_scalar_mul_add` is used directly instead.
pub proof fn lemma_montgomery_scalar_mul_consecutive(P: MontgomeryAffine, n: nat)
    ensures
        montgomery_add(montgomery_scalar_mul(P, n), montgomery_scalar_mul(P, n + 1))
            == montgomery_scalar_mul(P, 2 * n + 1),
{
    // [n]P + [n+1]P = [n]P + [n]P + P = [2n]P + P = [2n+1]P
    // Using scalar_mul_add: [n + (n+1)]P = [n]P + [n+1]P
    assert(n + (n + 1) == 2 * n + 1);
    lemma_montgomery_scalar_mul_add(P, n, n + 1);
}

/// Lemma: extracting u-coordinate from [0]P = Infinity gives 0
pub proof fn lemma_spec_u_coordinate_infinity()
    ensures
        spec_u_coordinate(MontgomeryAffine::Infinity) == 0,
{
    // By definition of spec_u_coordinate
}

/// Lemma: For a finite point, spec_u_coordinate extracts the u value
pub proof fn lemma_spec_u_coordinate_finite(u: nat, v: nat)
    ensures
        spec_u_coordinate(MontgomeryAffine::Finite { u, v }) == u,
{
    // By definition of spec_u_coordinate
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
pub proof fn lemma_math_sqrt_zero()
    ensures
        math_sqrt(0) == 0,
{
    assert(math_is_square(0)) by {
        assert(exists|y: nat| (#[trigger] (y * y) % p()) == (0nat % p())) by {
            let y: nat = 0;
            assert((y * y) % p() == 0nat % p());
        };
    }
    assert(exists|y: nat| y < p() && #[trigger] ((y * y) % p()) == (0nat % p())) by {
        let y: nat = 0;
        p_gt_2();
        assert(y < p());
        assert((y * y) % p() == 0nat % p());
    };
    reveal(math_sqrt);
    let y = math_sqrt(0);
    assert(y < p() && ((y * y) % p()) == (0nat % p()));
    // From the definition of math_sqrt (choose), we have:
    assert(y < p());
    assert(((y * y) % p()) == (0nat % p()));
    assert((y * y) % p() == 0);

    // If y^2 ≡ 0 (mod p) and p is prime, then y ≡ 0 (mod p).
    axiom_p_is_prime();
    lemma_euclid_prime(y, y, p());
    assert(y % p() == 0);

    // Since y < p, y % p = y, so y = 0.
    lemma_small_mod(y, p());
    assert(y == 0);
}

/// Lemma: canonical_sqrt(0) = 0.
pub proof fn lemma_canonical_sqrt_zero()
    ensures
        canonical_sqrt(0) == 0,
{
    lemma_math_sqrt_zero();
    assert(math_is_square(0)) by {
        assert(exists|y: nat| (#[trigger] (y * y) % p()) == (0nat % p())) by {
            let y: nat = 0;
            assert((y * y) % p() == 0nat % p());
        };
    }
    let s1 = math_sqrt(0);
    assert(s1 == 0);
    let s2 = math_field_neg(s1);
    assert(s2 == 0) by {
        assert(s1 % p() == 0) by {
            assert(s1 == 0);
            p_gt_2();
            lemma_small_mod(0, p());
        }
        assert(math_field_neg(0) == 0) by {
            p_gt_2();
            assert(0nat % p() == 0nat);
            assert(math_field_neg(0) == (p() - (0nat % p())) as nat % p());
            assert(math_field_neg(0) == p() % p());
            lemma_mod_self_0(p() as int);
        }
    };
    // s1 is even, so canonical_sqrt returns s1.
    assert(canonical_sqrt(0) == s1);
}

/// Lemma: canonical_montgomery_lift(0) is the (0,0) 2-torsion point.
pub proof fn lemma_canonical_montgomery_lift_zero()
    ensures
        canonical_montgomery_lift(0) == (MontgomeryAffine::Finite { u: 0, v: 0 }),
{
    lemma_canonical_sqrt_zero();
    assert(montgomery_rhs(0) == 0) by {
        let A = spec_field_element(&MONTGOMERY_A);
        let u2 = math_field_mul(0, 0);
        let u3 = math_field_mul(u2, 0);
        let Au2 = math_field_mul(A, u2);
        assert(montgomery_rhs(0) == math_field_add(math_field_add(u3, Au2), 0));
        p_gt_2();
        lemma_small_mod(0, p());
        assert(0nat % p() == 0nat);
        assert(u2 == 0) by { lemma_field_mul_zero_left(0, 0); }
        assert(u2 % p() == 0) by { assert(u2 == 0); }
        assert(u3 == 0) by { lemma_field_mul_zero_left(u2, 0); }
        assert(Au2 == 0) by { lemma_field_mul_zero_right(A, u2); }
        assert(math_field_add(math_field_add(0, 0), 0) == 0) by {
            p_gt_2();
            assert(math_field_add(0, 0) == (0nat + 0nat) % p());
            assert(math_field_add(0, 0) == 0);
            assert(math_field_add(0, 0) + 0 == 0);
            assert(math_field_add(math_field_add(0, 0), 0) == (0nat + 0nat) % p());
            assert(math_field_add(math_field_add(0, 0), 0) == 0);
        }
        assert(montgomery_rhs(0) == 0);
    }
    assert(canonical_montgomery_lift(0) == MontgomeryAffine::Finite { u: 0nat % p(), v: canonical_sqrt(montgomery_rhs(0)) });
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
    lemma_canonical_montgomery_lift_zero();
    let P = canonical_montgomery_lift(0);
    assert(P == MontgomeryAffine::Finite { u: 0, v: 0 });
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
            lemma_montgomery_add_zero_point_doubles_to_infinity();
            assert(montgomery_scalar_mul(P, n) == MontgomeryAffine::Infinity);
        }
    }
}

/// Lemma: u-coordinate of any scalar multiple of canonical_montgomery_lift(0) is 0.
pub proof fn lemma_u_coordinate_scalar_mul_canonical_lift_zero(n: nat)
    ensures
        ({
            let P = canonical_montgomery_lift(0);
            spec_u_coordinate(montgomery_scalar_mul(P, n)) == 0
        }),
{
    lemma_montgomery_scalar_mul_zero_point_closed(n);
    lemma_canonical_montgomery_lift_zero();
    let P = canonical_montgomery_lift(0);
    let R = montgomery_scalar_mul(P, n);
    if R == MontgomeryAffine::Infinity {
        lemma_spec_u_coordinate_infinity();
    } else {
        assert(R == P);
        assert(P == MontgomeryAffine::Finite { u: 0, v: 0 });
        lemma_spec_u_coordinate_finite(0, 0);
    }
}

} // verus!
