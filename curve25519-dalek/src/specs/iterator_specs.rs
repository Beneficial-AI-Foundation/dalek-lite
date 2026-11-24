//! Specifications for multiscalar multiplication on iterator inputs.
//!
//! # How to read the contracts
//!
//! The methods take any `IntoIterator` arguments, and their items are any type that
//! implements `Borrow<Scalar>` or `Borrow<Point>`. The contracts use the vstd model of an
//! iterator. `iter.remaining()` is the sequence of items that `iter` can return, and
//! `iter.produces()[k]` says whether `iter` actually returns item `k` instead of getting
//! stuck, for example in a diverging closure. These are prophecies: they describe this run,
//! so they also cover iterators whose items depend on shared state.
//!
//! `into_iter()`, `next()`, `size_hint()`, `by_ref()` and `borrow()` can all be user code.
//! The contracts therefore quantify over the possible results of these calls instead of
//! naming one value.
//!
//! A requirement (`valid_msm_sources`, `valid_optional_msm_sources`) says that every
//! iterator the arguments may produce obeys the iterator laws, has exact length checks,
//! and yields valid scalars and points. An outcome (`msm_outcome`, `optional_msm_outcome`)
//! says that the iterators returned every item and that the result is the sum of the
//! products of the borrowed values. The variable-time outcome can instead be `None`, which
//! means that the point iterator returned a `None` item.
//!
//! # The common case
//!
//! For arguments that are slices or vectors, with items `T` or `&T`, the requirements reduce
//! to equal lengths and conditions on the elements, and the outcome reduces to
//! `sum_of_scalar_muls(scalars@, points@)`. Use `broadcast use group_multiscalar_inputs`
//! (in `traits.rs`) to get these facts. `check_multiscalar_mul_slices` and
//! `check_optional_multiscalar_mul_vec` in `traits.rs` show both methods.
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

/// `values[k]` is a value that `items[k].borrow()` may return, for every `k`.
/// `Borrow::borrow` is user code, so two calls on the same item need not agree.
/// For items of type `T` or `&T`, `values` equals the items themselves
/// (see `lemma_msm_owned_values` and `lemma_msm_referenced_values` in `traits.rs`).
pub open spec fn borrowed_values<A: Borrow<B>, B>(items: Seq<A>, values: Seq<B>) -> bool {
    &&& items.len() == values.len()
    &&& forall|k: int|
        0 <= k < items.len() ==> #[trigger] call_ensures(Borrow::borrow, (&items[k],), &values[k])
}

/// Every item that `iter` returns passes `valid_value` after borrowing.
/// `iter` must obey the vstd iterator laws, so `remaining()` lists the items it can return.
/// For a slice or a vector, this says that every element satisfies `valid_value`.
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

/// The requirements of the constant-time method on two concrete iterators:
/// - both obey the vstd iterator laws and have the same number of items left;
/// - every scalar they yield has bit 255 clear, and every point satisfies `valid_point`;
/// - `scalars.by_ref().size_hint()` reports the exact length and leaves the items unchanged,
///   and `point_hint` states the check on the point iterator. For Edwards it is the same
///   reborrow guarantee. For Ristretto it is an exact `size_hint()` on the point iterator.
/// For slices or vectors of equal length, only the conditions on the elements remain.
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

/// The requirement of `MultiscalarMul::multiscalar_mul` on its arguments.
/// `into_iter()` is user code, so the requirement is stated for every pair of iterators
/// that `scalars.into_iter()` and `points.into_iter()` may return.
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

/// The result of `MultiscalarMul::multiscalar_mul`, stated with `sum`.
/// There are iterators `si` and `pi` returned by the two `into_iter()` calls, and values
/// `ss` and `ps` returned by `borrow()` on their items, such that the iterators returned
/// every item and `sum(ss, ps)` holds.
/// For slices or vectors, `ss` and `ps` are the elements, so the result is the sum of the
/// products of the elements.
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

/// The condition on scalar `s` in a variable-time call with `n` inputs.
/// The Edwards dispatcher sends fewer than 190 inputs to Straus, which needs bit 255 clear,
/// and the rest to Pippenger, which accepts any scalar.
pub open spec fn vartime_dispatch_scalar(s: Scalar, n: nat) -> bool {
    n < 190 ==> s.bytes[31] <= 127
}

/// The length checks of the variable-time Edwards dispatcher do not disturb `iter`.
/// The dispatcher checks the length once. If it picks Pippenger, Pippenger checks it again to
/// choose its window size, so the second check must also leave the items unchanged.
/// Slice and vector iterators satisfy this.
#[verifier::prophetic]
pub open spec fn valid_dispatch_scalar_hint<I: Iterator>(iter: I) -> bool {
    &&& by_ref_preserves_items(iter)
    &&& forall|after: I, hint: (usize, Option<usize>)| #[trigger]
        crate::core_assumes::by_ref_hint_outcome(iter, after, hint) && hint.0 >= 190
            ==> by_ref_preserves_items(after)
}

/// Every `Some(point)` that `iter` returns satisfies `valid_point`.
/// `None` items are allowed and make the variable-time method return `None`.
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

/// The requirement of `VartimeMultiscalarMul::optional_multiscalar_mul` on its arguments.
/// For every iterator that `into_iter()` may return:
/// - each scalar `s` satisfies `valid_scalar(s, n)`, where `n` is the number of inputs,
///   and the length checks satisfy `scalar_hint`;
/// - each present point satisfies `valid_point`, and the length check satisfies `point_hint`;
/// - the scalar and point iterators have the same number of items left.
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

/// The result of the variable-time method on two concrete iterators.
/// `None` means that the point iterator yielded a `None`.
/// `Some(r)` means that the iterators returned every item, every point was present, and
/// `sum(ss, points, r)` holds, where `ss` are values returned by `borrow()` on the scalars.
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

/// The result of `VartimeMultiscalarMul::optional_multiscalar_mul`, stated with `sum`.
/// It is `optional_iter_outcome` for some pair of iterators returned by the two
/// `into_iter()` calls.
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
