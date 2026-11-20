//! Verus specifications for multiscalar multiplication and point sums.
//!
//! Contains spec functions over sequences of optional and Ristretto points. The verified
//! multiscalar functions take slices, so their contracts use `scalars@` and `points@`
//! directly.
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::edwards::EdwardsPoint;
#[allow(unused_imports)]
use crate::ristretto::RistrettoPoint;
#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::{edwards_add, edwards_point_as_affine, sum_of_points};

verus! {

// ============================================================================
// Spec functions for optional point sequences
// ============================================================================
/// Check if all optional points in a sequence are Some.
pub open spec fn all_points_some(points: Seq<Option<EdwardsPoint>>) -> bool {
    forall|i: int| 0 <= i < points.len() ==> points[i].is_some()
}

/// Extract EdwardsPoints from an Option sequence (assumes all are Some).
pub open spec fn unwrap_points(points: Seq<Option<EdwardsPoint>>) -> Seq<EdwardsPoint>
    recommends
        all_points_some(points),
{
    points.map(|_i, opt: Option<EdwardsPoint>| opt.unwrap())
}

// ============================================================================
// RistrettoPoint sequence specs
// RistrettoPoint wraps EdwardsPoint, so these extract the inner Edwards points.
// ============================================================================
/// The Edwards points inside a sequence of RistrettoPoints.
pub open spec fn ristretto_points_to_edwards(points: Seq<RistrettoPoint>) -> Seq<EdwardsPoint> {
    points.map(|_i, p: RistrettoPoint| p.0)
}

/// The Edwards point inside an optional RistrettoPoint.
pub open spec fn optional_ristretto_to_edwards(point: Option<RistrettoPoint>) -> Option<
    EdwardsPoint,
> {
    match point {
        Some(p) => Some(p.0),
        None => None,
    }
}

/// The Edwards points inside a sequence of optional RistrettoPoints. `None` stays `None`.
pub open spec fn optional_ristretto_points_to_edwards(points: Seq<Option<RistrettoPoint>>) -> Seq<
    Option<EdwardsPoint>,
> {
    points.map(|_i, p: Option<RistrettoPoint>| optional_ristretto_to_edwards(p))
}

/// Spec function to compute sum of all RistrettoPoints in a sequence.
/// Returns the affine coordinates of the result.
pub open spec fn sum_of_ristretto_points(points: Seq<RistrettoPoint>) -> (nat, nat)
    decreases points.len(),
{
    if points.len() == 0 {
        // Identity point in affine coordinates: (0, 1)
        (0, 1)
    } else {
        let last = (points.len() - 1) as int;
        let prev = sum_of_ristretto_points(points.subrange(0, last));
        let point_affine = edwards_point_as_affine(points[last].0);
        edwards_add(prev.0, prev.1, point_affine.0, point_affine.1)
    }
}

/// Lemma: sum_of_ristretto_points equals sum_of_points when Edwards points are extracted.
/// This allows translating between Ristretto and Edwards sum specs.
pub proof fn lemma_sum_ristretto_edwards_equiv(ristretto_points: Seq<RistrettoPoint>)
    ensures
        sum_of_ristretto_points(ristretto_points) == sum_of_points(
            Seq::new(ristretto_points.len(), |i: int| ristretto_points[i].0),
        ),
    decreases ristretto_points.len(),
{
    let edwards_points = Seq::new(ristretto_points.len(), |i: int| ristretto_points[i].0);
    if ristretto_points.len() == 0 {
        // Base case: both return (0, 1)
    } else {
        let last = (ristretto_points.len() - 1) as int;
        // Inductive step
        lemma_sum_ristretto_edwards_equiv(ristretto_points.subrange(0, last));
        // Show subranges map correctly
        assert(Seq::new(
            ristretto_points.subrange(0, last).len(),
            |i: int| ristretto_points.subrange(0, last)[i].0,
        ) =~= edwards_points.subrange(0, last));
        assert(ristretto_points[last].0 == edwards_points[last]);
    }
}

} // verus!
