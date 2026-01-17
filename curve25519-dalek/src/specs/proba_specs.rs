//! Probabilistic specifications and axioms for uniform distribution.
//!
//! This module collects all specifications related to uniform distribution,
//! which are cryptographic properties that cannot be proven in standard program logic.
//!
//! ## Overview
//!
//! The uniform distribution properties form a chain:
//! 1. `is_uniform_bytes` - uniform random bytes (from RNG or hash)
//! 2. `is_uniform_field_element` - uniform field element (from bytes via from_bytes)
//! 3. `is_uniform_ristretto_point` - uniform group element (from field element via Elligator)
//!
//! ## Axioms
//!
//! Each axiom corresponds to a cryptographic/mathematical fact:
//! - `axiom_uniform_bytes_split`: Splitting uniform bytes yields independent uniform halves
//! - `axiom_from_bytes_uniform`: Clearing bit 255 preserves uniformity (negligible bias)
//! - `axiom_uniform_elligator`: Elligator map produces uniform points
//! - `axiom_uniform_point_add`: Sum of *independent* uniform group elements is uniform
#[allow(unused_imports)]
use super::edwards_specs::*;
#[allow(unused_imports)]
use super::field_specs::*;
#[allow(unused_imports)]
use super::ristretto_specs::*;
#[allow(unused_imports)]
use crate::field::FieldElement;
#[allow(unused_imports)]
use crate::ristretto::RistrettoPoint;
#[allow(unused_imports)]
use crate::Scalar;

use vstd::prelude::*;

#[cfg(feature = "rand_core")]
use rand_core::RngCore;

verus! {

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::core_specs::bytes32_to_nat;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::arithmetic::power2::pow2;

// =============================================================================
// Uninterpreted Spec Functions for Uniform Distribution
// =============================================================================
/// Uniform distribution predicate for a single byte.
pub uninterp spec fn is_uniform(x: u8) -> bool;

/// Uniform distribution predicate for a byte slice.
/// True if the bytes are uniformly distributed over their domain.
pub uninterp spec fn is_uniform_bytes(bytes: &[u8]) -> bool;

/// Uniform distribution predicate for a field element.
/// True if the field element is uniformly distributed over F_p.
pub uninterp spec fn is_uniform_field_element(fe: &FieldElement) -> bool;

/// Uniform distribution predicate for a scalar.
/// True if the scalar is uniformly distributed over [0, l) where l is the group order.
pub uninterp spec fn is_uniform_scalar(scalar: &Scalar) -> bool;

/// Uniform distribution predicate for a Ristretto point.
/// True if the point is uniformly distributed over the Ristretto group.
pub uninterp spec fn is_uniform_ristretto_point(point: &RistrettoPoint) -> bool;

/// Independence predicate for two 32-byte strings.
///
/// This is intended to be used together with `is_uniform_bytes(..)` to model
/// two *independent uniform* samples when needed.
pub uninterp spec fn is_independent_uniform_bytes32(first: &[u8; 32], second: &[u8; 32]) -> bool;

/// Independence predicate for two field elements.
///
/// This is intended to be used together with `is_uniform_field_element(..)` to
/// model two *independent uniform* samples when needed.
pub uninterp spec fn is_independent_uniform_field_elements(
    fe1: &FieldElement,
    fe2: &FieldElement,
) -> bool;

/// Independence predicate for two Ristretto points.
///
/// This is intended to be used together with `is_uniform_ristretto_point(..)` to
/// model two *independent uniform* samples when needed.
pub uninterp spec fn is_independent_uniform_ristretto_points(
    p1: &RistrettoPoint,
    p2: &RistrettoPoint,
) -> bool;

// =============================================================================
// Axiom 1: Splitting uniform bytes preserves uniformity
// =============================================================================
/// Axiom: Splitting uniform bytes preserves uniformity on each half.
///
/// Mathematical justification:
/// If X is uniform over [0, 2^512), then the first 256 bits and last 256 bits
/// are each uniform over [0, 2^256) (they are independent uniform samples).
pub proof fn axiom_uniform_bytes_split(bytes: &[u8; 64], first: &[u8; 32], second: &[u8; 32])
    requires
        first@ == bytes@.subrange(0, 32),
        second@ == bytes@.subrange(32, 64),
    ensures
        is_uniform_bytes(bytes) ==> is_uniform_bytes(first),
        is_uniform_bytes(bytes) ==> is_uniform_bytes(second),
        is_uniform_bytes(bytes) ==> is_independent_uniform_bytes32(first, second),
{
    assume(is_uniform_bytes(bytes) ==> is_uniform_bytes(first));
    assume(is_uniform_bytes(bytes) ==> is_uniform_bytes(second));
    assume(is_uniform_bytes(bytes) ==> is_independent_uniform_bytes32(first, second));
}

// =============================================================================
// Axiom 2: from_bytes preserves uniformity
// =============================================================================
/// Axiom: Clearing bit 255 of uniform bytes preserves uniform distribution.
///
/// Mathematical justification:
/// - If X is uniform over [0, 2^256), then X mod 2^255 is uniform over [0, 2^255)
/// - This is because the high bit is independent of the lower 255 bits
/// - The limb representation is a bijection from 255-bit values to FieldElement
///
/// Note: There's negligible bias (19/2^255 ≈ 5.4e-77) from values in [p, 2^255)
/// that wrap when used in field arithmetic, but this is cryptographically negligible.
pub proof fn axiom_from_bytes_uniform(bytes: &[u8; 32], fe: &FieldElement)
    requires
        spec_field_element_as_nat(fe) == bytes32_to_nat(bytes) % pow2(255),
    ensures
        is_uniform_bytes(bytes) ==> is_uniform_field_element(fe),
{
    assume(is_uniform_bytes(bytes) ==> is_uniform_field_element(fe));
}

/// Axiom: `from_bytes` preserves independence.
///
/// If two 32-byte strings are sampled independently, then the corresponding
/// field elements produced by `from_bytes` are also sampled independently.
pub proof fn axiom_from_bytes_independent(
    bytes1: &[u8; 32],
    bytes2: &[u8; 32],
    fe1: &FieldElement,
    fe2: &FieldElement,
)
    requires
        spec_field_element_as_nat(fe1) == bytes32_to_nat(bytes1) % pow2(255),
        spec_field_element_as_nat(fe2) == bytes32_to_nat(bytes2) % pow2(255),
    ensures
        is_independent_uniform_bytes32(bytes1, bytes2) ==> is_independent_uniform_field_elements(
            fe1,
            fe2,
        ),
{
    assume(is_independent_uniform_bytes32(bytes1, bytes2) ==> is_independent_uniform_field_elements(
        fe1,
        fe2,
    ));
}

// =============================================================================
// Axiom 3: Elligator map preserves uniformity
// =============================================================================
/// Axiom: Elligator map on uniform field element produces uniform point.
///
/// Mathematical justification:
/// The Elligator map is designed to be a uniform map from field elements to curve points.
/// See: Bernstein et al., "Elligator: Elliptic-curve points indistinguishable from uniform random strings"
pub proof fn axiom_uniform_elligator(fe: &FieldElement, point: &RistrettoPoint)
    requires
        edwards_point_as_affine(point.0) == spec_elligator_ristretto_flavor(spec_field_element(fe)),
    ensures
        is_uniform_field_element(fe) ==> is_uniform_ristretto_point(point),
{
    assume(is_uniform_field_element(fe) ==> is_uniform_ristretto_point(point));
}

/// Axiom: Elligator preserves independence.
///
/// If two field elements are sampled independently, then applying the Elligator
/// map to each yields independently sampled Ristretto points.
pub proof fn axiom_uniform_elligator_independent(
    fe1: &FieldElement,
    fe2: &FieldElement,
    p1: &RistrettoPoint,
    p2: &RistrettoPoint,
)
    requires
        edwards_point_as_affine(p1.0) == spec_elligator_ristretto_flavor(spec_field_element(fe1)),
        edwards_point_as_affine(p2.0) == spec_elligator_ristretto_flavor(spec_field_element(fe2)),
    ensures
        is_independent_uniform_field_elements(fe1, fe2) ==> is_independent_uniform_ristretto_points(
            p1,
            p2,
        ),
{
    admit();
}

// =============================================================================
// Axiom 4: Group addition preserves uniformity
// =============================================================================
/// Axiom: Sum of two *independent* uniform points is uniform (group theory property).
///
/// Mathematical justification:
/// In a prime-order group G, if X and Y are independent uniform elements of G,
/// then X + Y is also uniform over G. Without independence this is false
/// (e.g. if Y = -X then X + Y is always the identity).
pub proof fn axiom_uniform_point_add(p1: &RistrettoPoint, p2: &RistrettoPoint, sum: &RistrettoPoint)
    requires
        edwards_point_as_affine(sum.0) == edwards_add(
            edwards_point_as_affine(p1.0).0,
            edwards_point_as_affine(p1.0).1,
            edwards_point_as_affine(p2.0).0,
            edwards_point_as_affine(p2.0).1,
        ),
    ensures
        (is_uniform_ristretto_point(p1) && is_uniform_ristretto_point(p2)
            && is_independent_uniform_ristretto_points(p1, p2)) ==> is_uniform_ristretto_point(sum),
{
    admit();
}

// =============================================================================
// External Functions with Uniform Ensures
// =============================================================================
#[cfg(feature = "rand_core")]
#[verifier::external_body]
/// Fill bytes from a cryptographic RNG, producing uniform random bytes.
pub fn fill_bytes<R: RngCore>(rng: &mut R, bytes: &mut [u8; 64])
    ensures
        is_uniform_bytes(bytes),
{
    rng.fill_bytes(bytes)
}

/// Uninterpreted spec function for SHA-512 hash.
/// Models the SHA-512 hash as a function from input bytes to 64 output bytes.
pub uninterp spec fn spec_sha512(input: Seq<u8>) -> Seq<u8>;

/// Axiom: SHA-512 always produces exactly 64 bytes of output.
pub proof fn axiom_sha512_output_length(input: Seq<u8>)
    ensures
        spec_sha512(input).len() == 64,
{
    admit();
}

#[cfg(feature = "digest")]
#[verifier::external_body]
/// Compute SHA-512 hash of input bytes.
/// If input is uniform, output is computationally indistinguishable from uniform.
pub fn sha512_hash_bytes(input: &[u8]) -> (result: [u8; 64])
    ensures
        result@ == spec_sha512(input@),
        is_uniform_bytes(input) ==> is_uniform_bytes(&result),
{
    use digest::Digest;
    let mut hasher = sha2::Sha512::new();
    hasher.update(input);
    hasher.finalize().into()
}

} // verus!
