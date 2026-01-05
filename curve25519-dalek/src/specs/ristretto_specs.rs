// Specifications for mathematical operations on the Ristretto group
//
// ## References
//
// The mathematical formulas and specifications in this file are based on:
//
// - [RISTRETTO] Ristretto Group Specification
//   https://ristretto.group/
//   https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448
//
// - [DECAF] Hamburg, M. (2015). "Decaf: Eliminating cofactors through point compression"
//   https://eprint.iacr.org/2015/673.pdf
//
// - The Ristretto group is a prime-order quotient group constructed from the
//   cofactor-8 Edwards curve Curve25519. Points are equivalence classes of
//   Edwards points that differ by 4-torsion elements.
//
#[allow(unused_imports)]
use super::edwards_specs::*;
#[allow(unused_imports)]
use super::field_specs::*;
#[allow(unused_imports)]
use super::field_specs_u64::*;
#[allow(unused_imports)]
use super::scalar_specs::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::constants::EDWARDS_D;
#[allow(unused_imports)]
use crate::constants;
#[allow(unused_imports)]
use crate::edwards::EdwardsPoint;
#[allow(unused_imports)]
use crate::field::FieldElement;
use vstd::prelude::*;

verus! {

// =============================================================================
// Ristretto Group Mathematical Specifications
// =============================================================================
// Note: Since RistrettoPoint is declared outside verus! blocks, we define
// specs in terms of the underlying EdwardsPoint representation.

/// The Ristretto basepoint in affine coordinates.
/// This is the image of the Ed25519 basepoint under the quotient map.
///
/// Reference: [RISTRETTO] Section 4
pub open spec fn spec_ristretto_basepoint() -> (nat, nat) {
    // The Ristretto basepoint is the coset containing the Ed25519 basepoint
    spec_ed25519_basepoint()
}

// =============================================================================
// Ristretto Identity
// =============================================================================

/// The identity element in the Ristretto group.
/// This is the coset containing the Edwards identity point (0, 1).
///
/// Reference: [RISTRETTO] Section 2
pub open spec fn spec_ristretto_identity() -> (nat, nat) {
    math_edwards_identity()  // (0, 1)
}

// =============================================================================
// Ristretto Group Operations (at mathematical level)
// =============================================================================

/// Ristretto addition is inherited from Edwards addition.
/// Since the 4-torsion subgroup is normal, the quotient group is well-defined.
///
/// For Ristretto points P and Q with representatives P' and Q':
///   P + Q = [P' + Q']
/// where [...] denotes the equivalence class (coset).
///
/// Reference: [RISTRETTO] Section 2
pub open spec fn ristretto_add(p1: (nat, nat), p2: (nat, nat)) -> (nat, nat) {
    edwards_add(p1.0, p1.1, p2.0, p2.1)
}

/// Ristretto subtraction is inherited from Edwards subtraction.
pub open spec fn ristretto_sub(p1: (nat, nat), p2: (nat, nat)) -> (nat, nat) {
    edwards_sub(p1.0, p1.1, p2.0, p2.1)
}

/// Ristretto negation is inherited from Edwards negation.
/// For twisted Edwards curves, the negation of (x, y) is (-x, y).
pub open spec fn ristretto_neg(p: (nat, nat)) -> (nat, nat) {
    (math_field_neg(p.0), p.1)
}

/// Ristretto doubling is inherited from Edwards doubling.
pub open spec fn ristretto_double(p: (nat, nat)) -> (nat, nat) {
    edwards_double(p.0, p.1)
}

// =============================================================================
// Ristretto Scalar Multiplication
// =============================================================================

/// Scalar multiplication on Ristretto points.
/// Computes n * P where P is a Ristretto point.
///
/// This is inherited directly from Edwards scalar multiplication since
/// scalar multiplication commutes with the quotient map.
///
/// Reference: [RISTRETTO] Section 2
pub open spec fn ristretto_scalar_mul(point_affine: (nat, nat), n: nat) -> (nat, nat) {
    edwards_scalar_mul(point_affine, n)
}

/// Signed scalar multiplication for Ristretto (handles negative scalars).
pub open spec fn ristretto_scalar_mul_signed(point_affine: (nat, nat), n: int) -> (nat, nat) {
    edwards_scalar_mul_signed(point_affine, n)
}

// =============================================================================
// Ristretto Equality (mathematical level)
// =============================================================================

/// Two points (given as affine coordinates of their Edwards representatives)
/// are Ristretto-equal if they differ by an element of the 4-torsion subgroup.
///
/// The equality check uses: X1*Y2 == Y1*X2 OR X1*X2 == Y1*Y2
/// This checks if the points are in the same coset.
///
/// Reference: [RISTRETTO] Section 3.1
pub open spec fn ristretto_affine_eq(x1: nat, y1: nat, x2: nat, y2: nat) -> bool {
    // X1*Y2 == Y1*X2 checks if points are equal or negatives of each other
    // X1*X2 == Y1*Y2 checks if points differ by the 2-torsion point (0, -1)
    // Together they check equality in the quotient group E/E[4]
    math_field_mul(x1, y2) == math_field_mul(y1, x2)
    || math_field_mul(x1, x2) == math_field_mul(y1, y2)
}

// =============================================================================
// Compressed Ristretto Specifications
// =============================================================================

/// Check if a 32-byte array represents the compressed identity (all zeros).
pub open spec fn is_identity_compressed_ristretto_bytes(bytes: &[u8; 32]) -> bool {
    forall|i: int| 0 <= i < 32 ==> bytes[i] == 0u8
}

// =============================================================================
// Helper Specifications for Ristretto Operations
// =============================================================================

/// Spec function to compute sum of affine points (Ristretto addition chain).
pub open spec fn sum_of_ristretto_affine_points(points: Seq<(nat, nat)>) -> (nat, nat)
    decreases points.len(),
{
    if points.len() == 0 {
        spec_ristretto_identity()  // (0, 1)
    } else {
        let last = (points.len() - 1) as int;
        let prev = sum_of_ristretto_affine_points(points.subrange(0, last));
        ristretto_add(prev, points[last])
    }
}

// =============================================================================
// Multiscalar Multiplication Specifications
// =============================================================================

/// Spec for multiscalar multiplication: Σ(scalars[i] * points[i])
pub open spec fn spec_ristretto_multiscalar_mul(
    scalars: Seq<nat>,
    points: Seq<(nat, nat)>,
) -> (nat, nat)
    recommends
        scalars.len() == points.len(),
    decreases scalars.len(),
{
    if scalars.len() == 0 || points.len() == 0 {
        spec_ristretto_identity()
    } else {
        let last = (scalars.len() - 1) as int;
        let prev = spec_ristretto_multiscalar_mul(
            scalars.subrange(0, last),
            points.subrange(0, last),
        );
        let term = ristretto_scalar_mul(points[last], scalars[last]);
        ristretto_add(prev, term)
    }
}

} // verus!
