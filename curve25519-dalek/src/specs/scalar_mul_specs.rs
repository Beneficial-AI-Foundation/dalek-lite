//! Verus specifications for multiscalar multiplication algorithms.
//!
//! This module provides specs shared by Straus and Pippenger multiscalar multiplication.

#[allow(unused_imports)]
use crate::backend::serial::curve_models::ProjectiveNielsPoint;
#[allow(unused_imports)]
use crate::edwards::EdwardsPoint;
#[allow(unused_imports)]
use crate::scalar::Scalar;
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;
#[allow(unused_imports)]
use crate::window::LookupTable;
#[allow(unused_imports)]
use crate::window::NafLookupTable5;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

// =============================================================================
// Spec functions for iterator-based inputs
// =============================================================================

/// Spec function: extracts the scalars from an IntoIterator
pub uninterp spec fn spec_scalars_from_into_iter<I>(iter: I) -> Seq<Scalar>;

/// Spec function: extracts the points from an IntoIterator
pub uninterp spec fn spec_points_from_into_iter<I>(iter: I) -> Seq<EdwardsPoint>;

/// Spec function: extracts the optional points from an IntoIterator
/// Returns None if any point is None, otherwise returns Some(Seq<EdwardsPoint>)
pub uninterp spec fn spec_optional_points_from_into_iter<I>(iter: I) -> Option<Seq<EdwardsPoint>>;

/// Spec function: length of scalars from an IntoIterator
pub uninterp spec fn spec_scalars_len<I>(iter: I) -> nat;

/// Spec function: length of points from an IntoIterator
pub uninterp spec fn spec_points_len<I>(iter: I) -> nat;

// =============================================================================
// Spec functions for lookup tables
// =============================================================================

/// Spec: maps a LookupTable to the EdwardsPoint it was constructed from
pub uninterp spec fn spec_lookup_table_point(table: &LookupTable<ProjectiveNielsPoint>) -> EdwardsPoint;

/// Spec: maps a NafLookupTable5 to the EdwardsPoint it was constructed from
pub uninterp spec fn spec_naf_lookup_table_point(table: &NafLookupTable5<ProjectiveNielsPoint>) -> EdwardsPoint;

/// Spec: maps a ProjectiveNielsPoint to the EdwardsPoint it represents
pub uninterp spec fn spec_projective_niels_to_edwards(p: &ProjectiveNielsPoint) -> EdwardsPoint;

// =============================================================================
// Spec functions for radix representations
// =============================================================================

/// Spec: maps radix-16 digits back to the scalar value they represent
pub uninterp spec fn spec_radix16_digits_to_scalar(digits: &[i8; 64]) -> Scalar;

/// Spec: maps NAF digits back to the scalar value they represent
pub uninterp spec fn spec_naf_digits_to_scalar(digits: &[i8; 256]) -> Scalar;

/// Spec: maps radix-2^w digits back to the scalar value they represent
pub uninterp spec fn spec_radix2w_digits_to_scalar(digits: &Vec<i8>, w: usize) -> Scalar;

/// Spec: extracts a Scalar from an iterator item (handles Borrow<Scalar>)
pub uninterp spec fn spec_scalar_item_to_scalar<T>(item: &T) -> Scalar;

// =============================================================================
// Multiscalar multiplication specification
// =============================================================================

/// Spec for multiscalar multiplication: computes Σ(scalars[i] * points[i])
/// Returns affine coordinates (x, y) of the result.
///
/// This is the mathematical specification of:
///   Q = s_1 * P_1 + s_2 * P_2 + ... + s_n * P_n
pub open spec fn spec_multiscalar_mul(
    scalars: Seq<Scalar>,
    points: Seq<EdwardsPoint>,
) -> (nat, nat)
    decreases scalars.len(),
{
    if scalars.len() == 0 || points.len() == 0 {
        // Identity point in affine coordinates: (0, 1)
        (0nat, 1nat)
    } else {
        let last = (scalars.len() - 1) as int;
        // Recursively compute sum of all but last
        let prev = spec_multiscalar_mul(scalars.subrange(0, last), points.subrange(0, last));
        // Compute scalar[last] * point[last]
        let point_affine = edwards_point_as_affine(points[last]);
        let scalar_val = spec_scalar(&scalars[last]);
        let term = edwards_scalar_mul(point_affine, scalar_val);
        // Add to the sum
        edwards_add(prev.0, prev.1, term.0, term.1)
    }
}

} // verus!
