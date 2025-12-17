//! Verus specifications for multiscalar multiplication algorithms.
//!
//! This module provides specs shared by Straus and Pippenger multiscalar multiplication.

#[allow(unused_imports)]
use crate::edwards::EdwardsPoint;
#[allow(unused_imports)]
use crate::scalar::Scalar;
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;
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
