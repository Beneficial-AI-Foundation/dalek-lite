// Specifications for Montgomery curve operations on Curve25519
#[allow(unused_imports)]
use super::field_specs::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::constants::MONTGOMERY_A;
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
use vstd::prelude::*;

verus! {

/// Affine Montgomery point (u, v)
/// Curve equation is: v² = u³ + A·u² + u for Montgomery curve parameter A = 486662
pub struct MontgomeryPointAffine { pub u: nat, pub v: nat }

/// Montgomery curve points including the point at infinity
pub enum MontgomeryAffine {
    Infinity,
    Finite{ u: nat, v: nat }
}

/// Montgomery curve equation: B·v² = u³ + A·u² + u
/// For Curve25519: v² = u³ + 486662·u² + u (with B = 1, A = 486662)
/// Check if a point (u, v) satisfies the Montgomery curve equation
pub open spec fn math_on_montgomery_curve(u: nat, v: nat) -> bool {
    let a = spec_field_element(&MONTGOMERY_A);
    let u2 = math_field_square(u);
    let u3 = math_field_mul(u, u2);
    let v2 = math_field_square(v);

    // v² = u³ + A·u² + u
    let rhs = math_field_add(math_field_add(u3, math_field_mul(a, u2)), u);

    v2 == rhs
}

/// Negation on the Montgomery curve.
/// For the Montgomery curve v² = u³ + A·u² + u, the negation of a point is:
/// - Infinity → Infinity (the identity element is its own inverse)
/// - (u, v) → (u, -v) (negate the v-coordinate)
pub open spec fn montgomery_neg(P: MontgomeryAffine) -> MontgomeryAffine {
    match P {
        MontgomeryAffine::Infinity => MontgomeryAffine::Infinity,
        MontgomeryAffine::Finite{u, v} => {
            MontgomeryAffine::Finite{ u, v: math_field_neg(v) }
        }
    }
}

/// Addition on the Montgomery curve using the chord-tangent method.
/// For the Montgomery curve B·v² = u³ + A·u² + u (with B=1, A=486662):
///
/// Addition formulas:
/// - If P = ∞ or Q = ∞: return the other point (identity element)
/// - If P = -Q (same u, opposite v): return ∞
/// - If P = Q (point doubling): λ = (3u₁² + 2Au₁ + 1) / (2v₁)
/// - Otherwise (distinct points): λ = (v₂ - v₁) / (u₂ - u₁)
///
/// Then: u₃ = λ² - A - u₁ - u₂  and  v₃ = λ(u₁ - u₃) - v₁
pub open spec fn montgomery_add(
    P: MontgomeryAffine,
    Q: MontgomeryAffine
) -> MontgomeryAffine
{
    match (P, Q) {
        (MontgomeryAffine::Infinity, _) => Q,
        (_, MontgomeryAffine::Infinity) => P,

        (MontgomeryAffine::Finite{u: u1, v: v1},
         MontgomeryAffine::Finite{u: u2, v: v2}) => {

            let A = spec_field_element(&MONTGOMERY_A);

            // P = -Q (same u, opposite v)
            if u1 == u2 && math_field_add(v1, v2) == 0 {
                MontgomeryAffine::Infinity
            }
            // P = Q (doubling)
            else if u1 == u2 && v1 == v2 {
                let u1_sq = math_field_square(u1);
                let numerator   = math_field_add(
                    math_field_add(
                        math_field_mul(3, u1_sq),
                        math_field_mul(math_field_mul(2, A), u1)
                    ),
                    1
                );
                let denominator = math_field_mul(2, v1);
                let lambda      = math_field_mul(numerator, math_field_inv(denominator));

                let lambda_sq = math_field_square(lambda);
                let u3 = math_field_sub(
                    math_field_sub(lambda_sq, A),
                    math_field_mul(2, u1)
                );
                let v3 = math_field_sub(
                    math_field_mul(lambda, math_field_sub(u1, u3)),
                    v1
                );

                MontgomeryAffine::Finite{u: u3, v: v3}
            }
            // Add for distinct points P != Q
            else {
                let numerator   = math_field_sub(v2, v1);
                let denominator = math_field_sub(u2, u1);
                let lambda      = math_field_mul(numerator, math_field_inv(denominator));

                let lambda_sq = math_field_square(lambda);
                let u3 = math_field_sub(
                    math_field_sub(
                        math_field_sub(lambda_sq, A),
                        u1
                    ),
                    u2
                );
                let v3 = math_field_sub(
                    math_field_mul(lambda, math_field_sub(u1, u3)),
                    v1
                );

                MontgomeryAffine::Finite{u: u3, v: v3}
            }
        }
    }
}

/// Subtraction on the Montgomery curve, defined as P - Q = P + (-Q).
pub open spec fn montgomery_sub(P: MontgomeryAffine, Q: MontgomeryAffine) -> MontgomeryAffine {
    montgomery_add(P, montgomery_neg(Q))
}

/// Returns the u-coordinate of a Montgomery point as a field element
/// Montgomery points only store the u-coordinate; sign information is lost
pub open spec fn spec_montgomery_point(point: crate::montgomery::MontgomeryPoint) -> nat {
    spec_field_element_from_bytes(&point.0)
}

/// Returns the field element values (U, W) from a Montgomery ProjectivePoint.
/// A Montgomery ProjectivePoint (U:W) is in projective coordinates on the Montgomery curve.
pub open spec fn spec_projective_point_montgomery(point: crate::montgomery::ProjectivePoint) -> (nat, nat) {
    let u = spec_field_element(&point.U);
    let w = spec_field_element(&point.W);
    (u, w)
}

/// Returns the abstract affine u-coordinate from a Montgomery ProjectivePoint.
/// A Montgomery ProjectivePoint (U:W) represents affine point u = U/W.
pub open spec fn affine_projective_point_montgomery(point: crate::montgomery::ProjectivePoint) -> nat {
    let (u, w) = spec_projective_point_montgomery(point);
    if w == 0 {
        0  // Identity case
    } else {
        math_field_mul(u, math_field_inv(w))
    }
}

/// Check if a Montgomery u-coordinate is invalid for conversion to Edwards
/// u = -1 is invalid because it corresponds to a point on the twist
pub open spec fn is_equal_to_minus_one(u: nat) -> bool {
    u == math_field_sub(0, 1)  // u == -1
}

/// Map Edwards affine y to Montgomery u via u = (1+y)/(1-y). Special-case y=1 -> u=0.
pub open spec fn montgomery_u_from_edwards_y(y: nat) -> nat {
    let denom = math_field_sub(1, y);
    if denom == 0 {
        0
    } else {
        let numer = math_field_add(1, y);
        math_field_mul(numer, math_field_inv(denom))
    }
}

/// Map Montgomery u to Edwards affine y via y = (u-1)/(u+1).
/// Recommends u != -1 to avoid division by zero.
pub open spec fn edwards_y_from_montgomery_u(u: nat) -> nat
    recommends
        u != math_field_sub(0, 1),
{
    let denom = math_field_add(u, 1);
    let numer = math_field_sub(u, 1);
    math_field_mul(numer, math_field_inv(denom))
}

} // verus!
