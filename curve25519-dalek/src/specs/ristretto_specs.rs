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
//   cofactor-8 Edwards curve Curve25519. The curve has an 8-torsion subgroup
//   E[8] = {T[0], T[1], ..., T[7]} where T[i] = i·P for a generator P of order 8.
//   The 4-torsion subgroup is E[4] = {T[0], T[2], T[4], T[6]} (the even multiples).
//   
//   Ristretto points are equivalence classes [Q] = {Q + T : T ∈ E[4]}, i.e.,
//   Edwards points that differ by a 4-torsion element are considered equal.
//   The quotient G/E[4] is well-defined because the curve group is abelian.
//   This construction eliminates the cofactor, yielding a prime-order group.
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
use crate::backend::serial::u64::constants::EIGHT_TORSION;
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

/// The canonical representative of the Ristretto basepoint.
/// 
/// The Ristretto basepoint is the equivalence class [B] where B is the 
/// Ed25519 basepoint. We use B itself as the canonical representative.
pub open spec fn spec_ristretto_basepoint() -> (nat, nat) {
    spec_ed25519_basepoint()
}

/// Axiom: `RISTRETTO_BASEPOINT_TABLE` is a valid precomputed table for the Ristretto basepoint.
///
/// Since `RistrettoBasepointTable` wraps `EdwardsBasepointTable` and
/// `RISTRETTO_BASEPOINT_TABLE` is a pointer cast of `ED25519_BASEPOINT_TABLE`,
/// this follows from `axiom_ed25519_basepoint_table_valid()`.
#[cfg(feature = "precomputed-tables")]
pub proof fn axiom_ristretto_basepoint_table_valid()
    ensures
        is_valid_edwards_basepoint_table(
            constants::RISTRETTO_BASEPOINT_TABLE.0,
            spec_ristretto_basepoint(),
        ),
{
    axiom_ed25519_basepoint_table_valid();
    // The assume is needed because RISTRETTO_BASEPOINT_TABLE is external_body 
    // so Verus cannot see that .0 is the same as ED25519_BASEPOINT_TABLE to conclude the proof
    assume(is_valid_edwards_basepoint_table(
        constants::RISTRETTO_BASEPOINT_TABLE.0,
        spec_ristretto_basepoint(),
    ));
}

// =============================================================================
// Ristretto Equivalence Classes (Cosets)
// =============================================================================

/// Check if 4 Edwards points form a coset of the 4-torsion subgroup E[4].
/// 
/// A coset P + E[4] = {P, P + T[2], P + T[4], P + T[6]} represents a single
/// Ristretto equivalence class - all 4 points map to the same Ristretto point.
pub open spec fn is_ristretto_coset(
    points: [EdwardsPoint; 4],
    base: EdwardsPoint,
) -> bool {
    let base_affine = edwards_point_as_affine(base);
    let t2 = edwards_point_as_affine(EIGHT_TORSION[2]);
    let t4 = edwards_point_as_affine(EIGHT_TORSION[4]);
    let t6 = edwards_point_as_affine(EIGHT_TORSION[6]);
    
    // points[0] = base (T[0] is identity)
    edwards_point_as_affine(points[0]) == base_affine
    // points[1] = base + T[2]
    && edwards_point_as_affine(points[1]) == edwards_add(base_affine.0, base_affine.1, t2.0, t2.1)
    // points[2] = base + T[4]  
    && edwards_point_as_affine(points[2]) == edwards_add(base_affine.0, base_affine.1, t4.0, t4.1)
    // points[3] = base + T[6]
    && edwards_point_as_affine(points[3]) == edwards_add(base_affine.0, base_affine.1, t6.0, t6.1)
}

/// Two Edwards points are Ristretto-equivalent if they differ by a 4-torsion element.
pub open spec fn ristretto_equivalent(
    p1: EdwardsPoint,
    p2: EdwardsPoint,
) -> bool {
    let p1_affine = edwards_point_as_affine(p1);
    let p2_affine = edwards_point_as_affine(p2);
    let diff = edwards_sub(p1_affine.0, p1_affine.1, p2_affine.0, p2_affine.1);
    
    // The difference must be a 4-torsion element (one of T[0], T[2], T[4], T[6])
    let t0 = edwards_point_as_affine(EIGHT_TORSION[0]);
    let t2 = edwards_point_as_affine(EIGHT_TORSION[2]);
    let t4 = edwards_point_as_affine(EIGHT_TORSION[4]);
    let t6 = edwards_point_as_affine(EIGHT_TORSION[6]);
    
    diff == t0 || diff == t2 || diff == t4 || diff == t6
}

} // verus!
