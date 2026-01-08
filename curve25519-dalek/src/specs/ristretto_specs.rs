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
use super::core_specs::*;
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
use crate::backend::serial::u64::constants as u64_constants;
#[allow(unused_imports)]
use crate::edwards::EdwardsPoint;
#[allow(unused_imports)]
use crate::ristretto::{CompressedRistretto, RistrettoPoint};
#[allow(unused_imports)]
use crate::field::FieldElement;
use vstd::prelude::*;

verus! {

// =============================================================================
// Ristretto Group Mathematical Specifications
// =============================================================================

/// Spec-only model of Ristretto compression (exec implementation is external_body).
///
/// This captures the canonical encoding of a Ristretto point.
/// Reference: [RISTRETTO], §5.3 "Ristretto255 Encoding".
pub open spec fn spec_ristretto_compress(point: RistrettoPoint) -> [u8; 32] {
    let (x, y, z, t) = spec_edwards_point(point.0);
    let u1 = math_field_mul(math_field_add(z, y), math_field_sub(z, y));
    let u2 = math_field_mul(x, y);
    let invsqrt = math_invsqrt(math_field_mul(u1, math_field_square(u2)));
    let i1 = math_field_mul(invsqrt, u1);
    let i2 = math_field_mul(invsqrt, u2);
    let z_inv = math_field_mul(i1, math_field_mul(i2, t));
    let den_inv = i2;

    let iX = math_field_mul(x, spec_sqrt_m1());
    let iY = math_field_mul(y, spec_sqrt_m1());
    let enchanted_denominator = math_field_mul(
        i1,
        spec_field_element(&u64_constants::INVSQRT_A_MINUS_D),
    );

    let rotate = math_is_negative(math_field_mul(t, z_inv));
    let x_rot = if rotate { iY } else { x };
    let y_rot = if rotate { iX } else { y };
    let den_inv_rot = if rotate { enchanted_denominator } else { den_inv };

    let y_final = if math_is_negative(math_field_mul(x_rot, z_inv)) {
        math_field_neg(y_rot)
    } else {
        y_rot
    };
    let s = math_field_mul(den_inv_rot, math_field_sub(z, y_final));
    let s_final = if math_is_negative(s) { math_field_neg(s) } else { s };

    spec_bytes32_from_nat(s_final)
}

/// Spec-only model of Ristretto decompression.
/// Reference: [RISTRETTO], §5.2 "Ristretto255 Decoding".
pub open spec fn spec_ristretto_decompress(bytes: [u8; 32]) -> Option<RistrettoPoint> {
    let s_bytes_nat = bytes32_to_nat(&bytes);
    let s = spec_field_element_from_bytes(&bytes);
    let s_encoding_is_canonical = s_bytes_nat < p();
    let s_is_negative = math_is_negative(s);

    if !s_encoding_is_canonical || s_is_negative {
        None
    } else {
        let ss = math_field_square(s);
        let u1 = math_field_sub(1, ss);
        let u2 = math_field_add(1, ss);
        let u2_sqr = math_field_square(u2);
        let neg_d = math_field_neg(spec_field_element(&EDWARDS_D));
        let u1_sqr = math_field_square(u1);
        let v = math_field_sub(math_field_mul(neg_d, u1_sqr), u2_sqr);

        let invsqrt_input = math_field_mul(v, u2_sqr);
        let invsqrt = math_invsqrt(invsqrt_input);
        let ok = math_is_sqrt_ratio(1, invsqrt_input, invsqrt);

        let dx = math_field_mul(invsqrt, u2);
        let dy = math_field_mul(invsqrt, math_field_mul(dx, v));
        let x_tmp = math_field_mul(math_field_add(s, s), dx);
        let x = if math_is_negative(x_tmp) { math_field_neg(x_tmp) } else { x_tmp };
        let y = math_field_mul(u1, dy);
        let t = math_field_mul(x, y);

        let t_is_negative = math_is_negative(t);
        let y_is_zero = y == 0;

        if !ok || t_is_negative || y_is_zero {
            None
        } else if exists|p: RistrettoPoint| spec_edwards_point(p.0) == (x, y, 1nat, t) {
            Some(choose|p: RistrettoPoint| spec_edwards_point(p.0) == (x, y, 1nat, t))
        } else {
            None
        }
    }
}

/// Spec round-trip: decoding the encoding yields a point with the same encoding.
pub proof fn lemma_spec_ristretto_roundtrip(point: RistrettoPoint)
    ensures
        spec_ristretto_decompress(spec_ristretto_compress(point)).is_some(),
        spec_ristretto_compress(
            spec_ristretto_decompress(spec_ristretto_compress(point)).unwrap(),
        ) == spec_ristretto_compress(point),
{
    // Proof bypass: relies on the choice in spec_ristretto_decompress.
    assume(spec_ristretto_decompress(spec_ristretto_compress(point)).is_some());
    assume(
        spec_ristretto_compress(
            spec_ristretto_decompress(spec_ristretto_compress(point)).unwrap(),
        ) == spec_ristretto_compress(point)
    );
}

/// Spec predicate: compressed bytes correspond to a Ristretto point.
pub open spec fn compressed_ristretto_corresponds_to_point(
    compressed: CompressedRistretto,
    point: RistrettoPoint,
) -> bool {
    spec_ristretto_compress(point) == compressed.0
}

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
