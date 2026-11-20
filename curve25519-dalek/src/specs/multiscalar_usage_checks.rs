//! Verified callers of the multiscalar slice functions.
//!
//! Each function below builds small slices, proves the preconditions of a multiscalar function,
//! and asserts consequences of its postcondition. Verus checks them; normal builds do not
//! contain this module.
#![allow(unused_imports)]

use alloc::vec::Vec;

use vstd::prelude::*;

use crate::edwards::EdwardsPoint;
use crate::ristretto::RistrettoPoint;
use crate::scalar::Scalar;
use crate::scalar_helpers::{lemma_scalar_one_properties, lemma_scalar_zero_properties};
use crate::specs::edwards_specs::*;
use crate::specs::iterator_specs::*;
use crate::specs::scalar_specs::*;
use crate::traits::Identity;

verus! {

/// Two canonical scalars, [1, 0].
fn two_scalars() -> (scalars: Vec<Scalar>)
    ensures
        scalars@.len() == 2,
        forall|i: int| #![auto] 0 <= i < scalars@.len() ==> is_canonical_scalar(&scalars@[i]),
{
    proof {
        lemma_scalar_one_properties();
        lemma_scalar_zero_properties();
    }
    let mut scalars: Vec<Scalar> = Vec::new();
    scalars.push(Scalar::ONE);
    scalars.push(Scalar::ZERO);
    scalars
}

/// Two well-formed Edwards points.
fn two_points() -> (points: Vec<EdwardsPoint>)
    ensures
        points@.len() == 2,
        forall|i: int|
            0 <= i < points@.len() ==> is_well_formed_edwards_point(#[trigger] points@[i]),
{
    let mut points: Vec<EdwardsPoint> = Vec::new();
    points.push(EdwardsPoint::identity());
    points.push(EdwardsPoint::identity());
    points
}

/// Edwards, constant time: the result is the sum of the scalar multiples, and the empty sum is
/// the identity.
fn check_edwards_multiscalar_mul_slices() {
    let scalars = two_scalars();
    let points = two_points();
    let r = EdwardsPoint::multiscalar_mul_slices(scalars.as_slice(), points.as_slice());
    assert(is_well_formed_edwards_point(r));
    assert(edwards_point_as_affine(r) == sum_of_scalar_muls(scalars@, points@));

    let no_scalars: Vec<Scalar> = Vec::new();
    let no_points: Vec<EdwardsPoint> = Vec::new();
    let e = EdwardsPoint::multiscalar_mul_slices(no_scalars.as_slice(), no_points.as_slice());
    assert(edwards_point_as_affine(e) == (0nat, 1nat));
}

/// Edwards, variable time: `Some` exactly when all points are `Some`.
fn check_edwards_optional_multiscalar_mul_slices() {
    let scalars = two_scalars();
    let p = EdwardsPoint::identity();

    let mut all_some: Vec<Option<EdwardsPoint>> = Vec::new();
    all_some.push(Some(p));
    all_some.push(Some(p));
    let r = EdwardsPoint::optional_multiscalar_mul_slices(scalars.as_slice(), all_some.as_slice());
    assert(all_some@[0].is_some() && all_some@[1].is_some());
    assert(r.is_some());
    assert(is_well_formed_edwards_point(r.unwrap()));
    assert(edwards_point_as_affine(r.unwrap()) == sum_of_scalar_muls(
        scalars@,
        unwrap_points(all_some@),
    ));

    let mut one_none: Vec<Option<EdwardsPoint>> = Vec::new();
    one_none.push(Some(p));
    one_none.push(None);
    let n = EdwardsPoint::optional_multiscalar_mul_slices(scalars.as_slice(), one_none.as_slice());
    assert(one_none@[1].is_none());
    assert(n.is_none());

    let no_scalars: Vec<Scalar> = Vec::new();
    let no_points: Vec<Option<EdwardsPoint>> = Vec::new();
    let e = EdwardsPoint::optional_multiscalar_mul_slices(
        no_scalars.as_slice(),
        no_points.as_slice(),
    );
    assert(e.is_some());
    assert(edwards_point_as_affine(e.unwrap()) == (0nat, 1nat));
}

/// Ristretto, constant time.
fn check_ristretto_multiscalar_mul_slices() {
    let scalars = two_scalars();
    let p = RistrettoPoint::identity();
    let mut points: Vec<RistrettoPoint> = Vec::new();
    points.push(p);
    points.push(p);
    let r = RistrettoPoint::multiscalar_mul_slices(scalars.as_slice(), points.as_slice());
    assert(is_well_formed_edwards_point(r.0));
    assert(ristretto_points_to_edwards(points@)[0] == p.0);
    assert(edwards_point_as_affine(r.0) == sum_of_scalar_muls(
        scalars@,
        ristretto_points_to_edwards(points@),
    ));

    let no_scalars: Vec<Scalar> = Vec::new();
    let no_points: Vec<RistrettoPoint> = Vec::new();
    let e = RistrettoPoint::multiscalar_mul_slices(no_scalars.as_slice(), no_points.as_slice());
    assert(edwards_point_as_affine(e.0) == (0nat, 1nat));
}

/// Ristretto, variable time: `Some` exactly when all points are `Some`.
fn check_ristretto_optional_multiscalar_mul_slices() {
    let scalars = two_scalars();
    let p = RistrettoPoint::identity();

    let mut all_some: Vec<Option<RistrettoPoint>> = Vec::new();
    all_some.push(Some(p));
    all_some.push(Some(p));
    let r = RistrettoPoint::optional_multiscalar_mul_slices(
        scalars.as_slice(),
        all_some.as_slice(),
    );
    assert(optional_ristretto_points_to_edwards(all_some@)[0] == Some(p.0));
    assert(optional_ristretto_points_to_edwards(all_some@)[1] == Some(p.0));
    assert(r.is_some());
    assert(is_well_formed_edwards_point(r.unwrap().0));

    let mut one_none: Vec<Option<RistrettoPoint>> = Vec::new();
    one_none.push(None);
    one_none.push(Some(p));
    let n = RistrettoPoint::optional_multiscalar_mul_slices(
        scalars.as_slice(),
        one_none.as_slice(),
    );
    assert(optional_ristretto_points_to_edwards(one_none@)[0].is_none());
    assert(n.is_none());

    let no_scalars: Vec<Scalar> = Vec::new();
    let no_points: Vec<Option<RistrettoPoint>> = Vec::new();
    let e = RistrettoPoint::optional_multiscalar_mul_slices(
        no_scalars.as_slice(),
        no_points.as_slice(),
    );
    assert(e.is_some());
    assert(edwards_point_as_affine(e.unwrap().0) == (0nat, 1nat));
}

/// The crate-internal backend functions.
fn check_backend_multiscalar_functions() {
    let scalars = two_scalars();
    let points = two_points();
    let p = EdwardsPoint::identity();
    let mut opt_points: Vec<Option<EdwardsPoint>> = Vec::new();
    opt_points.push(Some(p));
    opt_points.push(None);

    let r = crate::backend::straus_multiscalar_mul_verus(scalars.as_slice(), points.as_slice());
    assert(edwards_point_as_affine(r) == sum_of_scalar_muls(scalars@, points@));

    let s = crate::backend::straus_optional_multiscalar_mul_verus(
        scalars.as_slice(),
        opt_points.as_slice(),
    );
    assert(opt_points@[1].is_none());
    assert(s.is_none());

    let t = crate::backend::pippenger_optional_multiscalar_mul_verus(
        scalars.as_slice(),
        opt_points.as_slice(),
    );
    assert(t.is_none());
}

/// The Pippenger backend accepts any scalar, also one with bit 255 set.
fn check_pippenger_any_scalar() {
    // 2^256 - 1: bit 255 set.
    let t = Scalar {
        bytes: [
            255u8,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
        ],
    };
    let p = EdwardsPoint::identity();
    let mut scalars: Vec<Scalar> = Vec::new();
    scalars.push(t);
    let mut opt_points: Vec<Option<EdwardsPoint>> = Vec::new();
    opt_points.push(Some(p));

    let q = crate::backend::pippenger_optional_multiscalar_mul_verus(
        scalars.as_slice(),
        opt_points.as_slice(),
    );
    assert(q.is_some());
    assert(edwards_point_as_affine(q.unwrap()) == sum_of_scalar_muls(
        scalars@,
        unwrap_points(opt_points@),
    ));
}

/// The public dispatchers accept a scalar above the group order when bit 255 is clear.
fn check_unreduced_scalars() {
    // 2^255 - 1: above the group order, bit 255 clear.
    let s = Scalar {
        bytes: [
            255u8,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            127,
        ],
    };
    let p = EdwardsPoint::identity();

    let mut scalars: Vec<Scalar> = Vec::new();
    scalars.push(s);
    let mut points: Vec<EdwardsPoint> = Vec::new();
    points.push(p);
    let mut opt_points: Vec<Option<EdwardsPoint>> = Vec::new();
    opt_points.push(Some(p));

    let r = EdwardsPoint::multiscalar_mul_slices(scalars.as_slice(), points.as_slice());
    assert(edwards_point_as_affine(r) == sum_of_scalar_muls(scalars@, points@));

    let o = EdwardsPoint::optional_multiscalar_mul_slices(
        scalars.as_slice(),
        opt_points.as_slice(),
    );
    assert(opt_points@[0].is_some());
    assert(o.is_some());
}

} // verus!
