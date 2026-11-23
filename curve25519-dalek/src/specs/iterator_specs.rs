//! Specifications for multiscalar multiplication on iterator inputs and on slices.
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::edwards::EdwardsPoint;
#[cfg(verus_keep_ghost)]
use crate::ristretto::RistrettoPoint;
#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::{edwards_add, edwards_point_as_affine, sum_of_points};

#[cfg(verus_keep_ghost)]
use crate::core_assumes::by_ref_preserves_items;
#[cfg(verus_keep_ghost)]
use crate::scalar::Scalar;
#[cfg(verus_keep_ghost)]
use core::borrow::Borrow;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;

verus! {

/// Each value is a permitted result of borrowing the corresponding yielded item.
/// Different calls to `borrow` can return different values.
pub open spec fn borrowed_values<A: Borrow<B>, B>(items: Seq<A>, values: Seq<B>) -> bool {
    &&& items.len() == values.len()
    &&& forall|k: int|
        0 <= k < items.len() ==> #[trigger] call_ensures(Borrow::borrow, (&items[k],), &values[k])
}

#[verifier::prophetic]
pub open spec fn valid_msm_iters<P, I: Iterator, J: Iterator>(
    scalars: I,
    points: J,
    valid_point: spec_fn(P) -> bool,
    point_hint: spec_fn(J) -> bool,
) -> bool where I::Item: Borrow<Scalar>, J::Item: Borrow<P> {
    &&& scalars.obeys_prophetic_iter_laws() && points.obeys_prophetic_iter_laws()
    &&& by_ref_preserves_items(scalars) && point_hint(points)
    &&& scalars.remaining().len() == points.remaining().len()
    &&& forall|k: int, s: Scalar|
        0 <= k < scalars.remaining().len() && scalars.produces()[k] && #[trigger] call_ensures(
            Borrow::borrow,
            (&scalars.remaining()[k],),
            &s,
        ) ==> s.bytes[31] <= 127
    &&& forall|k: int, p: P|
        0 <= k < points.remaining().len() && points.produces()[k] && #[trigger] call_ensures(
            Borrow::borrow,
            (&points.remaining()[k],),
            &p,
        ) ==> valid_point(p)
}

#[verifier::prophetic]
pub open spec fn valid_msm_sources<P, I: IntoIterator, J: IntoIterator>(
    scalars: I,
    points: J,
    valid_point: spec_fn(P) -> bool,
    point_hint: spec_fn(J::IntoIter) -> bool,
) -> bool where I::Item: Borrow<Scalar>, J::Item: Borrow<P> {
    forall|si: I::IntoIter, pi: J::IntoIter| #[trigger]
        call_ensures(I::into_iter, (scalars,), si) && #[trigger] call_ensures(
            J::into_iter,
            (points,),
            pi,
        ) ==> valid_msm_iters(si, pi, valid_point, point_hint)
}

/// Both iterators produced every item in the sum. Each value used in the sum
/// satisfies the postcondition of borrowing the corresponding item.
#[verifier::prophetic]
pub open spec fn msm_outcome<P, I: IntoIterator, J: IntoIterator>(
    scalars: I,
    points: J,
    sum: spec_fn(Seq<Scalar>, Seq<P>) -> bool,
) -> bool where I::Item: Borrow<Scalar>, J::Item: Borrow<P> {
    exists|si: I::IntoIter, pi: J::IntoIter, ss: Seq<Scalar>, ps: Seq<P>|
        {
            &&& #[trigger] call_ensures(I::into_iter, (scalars,), si)
            &&& #[trigger] call_ensures(J::into_iter, (points,), pi)
            &&& #[trigger] borrowed_values(si.remaining(), ss)
            &&& #[trigger] borrowed_values(pi.remaining(), ps)
            &&& forall|k: int| 0 <= k < ss.len() ==> #[trigger] si.produces()[k]
            &&& forall|k: int| 0 <= k < ps.len() ==> #[trigger] pi.produces()[k]
            &&& sum(ss, ps)
        }
}

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
