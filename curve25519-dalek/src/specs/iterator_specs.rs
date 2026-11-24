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

/// The iterator obeys the vstd iterator laws. Every permitted borrow of a yielded item
/// satisfies `valid_value`.
#[verifier::prophetic]
pub open spec fn valid_msm_items<I: Iterator, T>(
    iter: I,
    valid_value: spec_fn(T) -> bool,
) -> bool where I::Item: Borrow<T> {
    &&& iter.obeys_prophetic_iter_laws()
    &&& forall|k: int, value: T|
        0 <= k < iter.remaining().len() && iter.produces()[k] && #[trigger] call_ensures(
            Borrow::borrow,
            (&iter.remaining()[k],),
            &value,
        ) ==> valid_value(value)
}

/// Both iterators obey the vstd iterator laws and have the same number of items remaining.
/// Every permitted borrow of a yielded scalar has bit 255 clear. Every permitted borrow of
/// a yielded point satisfies `valid_point`.
///
/// `scalars.by_ref().size_hint()` must report the remaining length and preserve the items.
/// `point_hint` specifies the corresponding size check for points. Edwards requires the same
/// reborrow guarantee. Ristretto requires an exact `size_hint()` on the underlying point iterator.
#[verifier::prophetic]
pub open spec fn valid_msm_iters<P, I: Iterator, J: Iterator>(
    scalars: I,
    points: J,
    valid_point: spec_fn(P) -> bool,
    point_hint: spec_fn(J) -> bool,
) -> bool where I::Item: Borrow<Scalar>, J::Item: Borrow<P> {
    &&& valid_msm_items(scalars, |s: Scalar| s.bytes[31] <= 127)
    &&& valid_msm_items(points, valid_point)
    &&& by_ref_preserves_items(scalars) && point_hint(points)
    &&& scalars.remaining().len() == points.remaining().len()
}

/// Every pair of iterators permitted by `scalars.into_iter()` and `points.into_iter()`
/// must satisfy `valid_msm_iters` with the given point validity and size-hint predicates.
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

/// The variable-time Edwards dispatcher sends fewer than 190 inputs to Straus, which needs
/// bit 255 clear, and the rest to Pippenger, which accepts any scalar.
pub open spec fn vartime_dispatch_scalar(s: Scalar, n: nat) -> bool {
    n < 190 ==> s.bytes[31] <= 127
}

/// Edwards checks the scalar length before dispatch. Pippenger checks it again to choose a window.
#[verifier::prophetic]
pub open spec fn valid_dispatch_scalar_hint<I: Iterator>(iter: I) -> bool {
    &&& by_ref_preserves_items(iter)
    &&& forall|after: I, hint: (usize, Option<usize>)| #[trigger]
        crate::core_assumes::by_ref_hint_outcome(iter, after, hint) && hint.0 >= 190
            ==> by_ref_preserves_items(after)
}

/// Every yielded point that is present satisfies `valid_point`.
#[verifier::prophetic]
pub open spec fn valid_optional_points<P, J: Iterator<Item = Option<P>>>(
    iter: J,
    valid_point: spec_fn(P) -> bool,
) -> bool {
    &&& iter.obeys_prophetic_iter_laws()
    &&& forall|k: int|
        0 <= k < iter.remaining().len() && iter.produces()[k] && (
        #[trigger] iter.remaining()[k]).is_some() ==> valid_point(iter.remaining()[k].unwrap())
}

/// Each source must produce admissible iterators, and every pair has equal remaining lengths.
/// `valid_scalar(s, n)` is the condition on each scalar `s` when there are `n` inputs.
#[verifier::prophetic]
pub open spec fn valid_optional_msm_sources<P, I: IntoIterator, J: IntoIterator<Item = Option<P>>>(
    scalars: I,
    points: J,
    valid_scalar: spec_fn(Scalar, nat) -> bool,
    valid_point: spec_fn(P) -> bool,
    scalar_hint: spec_fn(I::IntoIter) -> bool,
    point_hint: spec_fn(J::IntoIter) -> bool,
) -> bool where I::Item: Borrow<Scalar> {
    &&& forall|si: I::IntoIter| #[trigger]
        call_ensures(I::into_iter, (scalars,), si) ==> valid_msm_items(
            si,
            |s: Scalar| valid_scalar(s, si.remaining().len()),
        ) && scalar_hint(si)
    &&& forall|pi: J::IntoIter| #[trigger]
        call_ensures(J::into_iter, (points,), pi) ==> valid_optional_points(pi, valid_point)
            && point_hint(pi)
    &&& forall|si: I::IntoIter, pi: J::IntoIter| #[trigger]
        call_ensures(I::into_iter, (scalars,), si) && #[trigger] call_ensures(
            J::into_iter,
            (points,),
            pi,
        ) ==> si.remaining().len() == pi.remaining().len()
}

/// A successful call sums every scalar-point pair. A failing call encountered a yielded `None`.
#[verifier::prophetic]
pub open spec fn optional_iter_outcome<P, I: Iterator, J: Iterator<Item = Option<P>>>(
    si: I,
    pi: J,
    result: Option<P>,
    sum: spec_fn(Seq<Scalar>, Seq<P>, P) -> bool,
) -> bool where I::Item: Borrow<Scalar> {
    match result {
        None => exists|k: int|
            0 <= k < pi.remaining().len() && pi.produces()[k] && (
            #[trigger] pi.remaining()[k]).is_none(),
        Some(r) => {
            &&& forall|k: int| 0 <= k < si.remaining().len() ==> #[trigger] si.produces()[k]
            &&& forall|k: int|
                #![trigger pi.produces()[k]]
                #![trigger pi.remaining()[k]]
                0 <= k < pi.remaining().len() ==> pi.produces()[k] && pi.remaining()[k].is_some()
            &&& exists|ss: Seq<Scalar>| #[trigger]
                borrowed_values(si.remaining(), ss) && sum(
                    ss,
                    pi.remaining().map(|_, p: Option<P>| p.unwrap()),
                    r,
                )
        },
    }
}

/// The optional result describes a pair of iterator conversions permitted for this call.
#[verifier::prophetic]
pub open spec fn optional_msm_outcome<P, I: IntoIterator, J: IntoIterator<Item = Option<P>>>(
    scalars: I,
    points: J,
    result: Option<P>,
    sum: spec_fn(Seq<Scalar>, Seq<P>, P) -> bool,
) -> bool where I::Item: Borrow<Scalar> {
    exists|si: I::IntoIter, pi: J::IntoIter| #[trigger]
        call_ensures(I::into_iter, (scalars,), si) && #[trigger] call_ensures(
            J::into_iter,
            (points,),
            pi,
        ) && optional_iter_outcome(si, pi, result, sum)
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
/// The Edwards point inside an optional RistrettoPoint.
pub open spec fn optional_ristretto_to_edwards(point: Option<RistrettoPoint>) -> Option<
    EdwardsPoint,
> {
    match point {
        Some(p) => Some(p.0),
        None => None,
    }
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
