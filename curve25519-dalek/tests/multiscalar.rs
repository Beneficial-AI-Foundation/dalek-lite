//! Deterministic tests for the multiscalar iterator methods.
#![cfg(feature = "alloc")]

use curve25519_dalek::constants::{ED25519_BASEPOINT_POINT, RISTRETTO_BASEPOINT_POINT};
use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{Identity, MultiscalarMul, VartimeMultiscalarMul};

fn scalars(n: usize) -> Vec<Scalar> {
    (0..n).map(|i| Scalar::from(3 * i as u64 + 7)).collect()
}

fn edwards_points(n: usize) -> Vec<EdwardsPoint> {
    (0..n)
        .map(|i| ED25519_BASEPOINT_POINT * Scalar::from(5 * i as u64 + 1))
        .collect()
}

fn ristretto_points(n: usize) -> Vec<RistrettoPoint> {
    (0..n)
        .map(|i| RISTRETTO_BASEPOINT_POINT * Scalar::from(5 * i as u64 + 1))
        .collect()
}

fn edwards_expected(s: &[Scalar], p: &[EdwardsPoint]) -> EdwardsPoint {
    s.iter()
        .zip(p)
        .fold(EdwardsPoint::identity(), |acc, (s, p)| acc + p * s)
}

fn ristretto_expected(s: &[Scalar], p: &[RistrettoPoint]) -> RistrettoPoint {
    s.iter()
        .zip(p)
        .fold(RistrettoPoint::identity(), |acc, (s, p)| acc + p * s)
}

// ---------------------------------------------------------------------------------------------
// Empty slices
// ---------------------------------------------------------------------------------------------

#[test]
fn empty_slices() {
    assert_eq!(
        EdwardsPoint::multiscalar_mul(&[] as &[Scalar], &[] as &[EdwardsPoint]),
        EdwardsPoint::identity()
    );
    assert_eq!(
        EdwardsPoint::optional_multiscalar_mul(&[] as &[Scalar], []),
        Some(EdwardsPoint::identity())
    );
    assert_eq!(
        RistrettoPoint::multiscalar_mul(&[] as &[Scalar], &[] as &[RistrettoPoint]),
        RistrettoPoint::identity()
    );
    assert_eq!(
        RistrettoPoint::optional_multiscalar_mul(&[] as &[Scalar], []),
        Some(RistrettoPoint::identity())
    );
}

// ---------------------------------------------------------------------------------------------
// `None` at the first, middle and last position
// ---------------------------------------------------------------------------------------------

#[test]
fn none_at_each_position() {
    let n = 5;
    let s = scalars(n);
    for pos in [0, n / 2, n - 1] {
        let mut e: Vec<Option<EdwardsPoint>> = edwards_points(n).into_iter().map(Some).collect();
        e[pos] = None;
        assert_eq!(EdwardsPoint::optional_multiscalar_mul(&s, e), None);

        let mut r: Vec<Option<RistrettoPoint>> =
            ristretto_points(n).into_iter().map(Some).collect();
        r[pos] = None;
        assert_eq!(RistrettoPoint::optional_multiscalar_mul(&s, r), None);
    }
}

// ---------------------------------------------------------------------------------------------
// Straus/Pippenger dispatch at 190 and Pippenger window changes at 500 and 800
// ---------------------------------------------------------------------------------------------

#[test]
fn dispatch_and_pippenger_windows() {
    for n in [1, 189, 190, 500, 800] {
        let s = scalars(n);

        let e = edwards_points(n);
        let e_opt: Vec<_> = e.iter().copied().map(Some).collect();
        let expected = edwards_expected(&s, &e);
        assert_eq!(EdwardsPoint::multiscalar_mul(&s, &e), expected);
        assert_eq!(
            EdwardsPoint::optional_multiscalar_mul(&s, e_opt),
            Some(expected)
        );

        let r = ristretto_points(n);
        let r_opt: Vec<_> = r.iter().copied().map(Some).collect();
        let expected = ristretto_expected(&s, &r);
        assert_eq!(RistrettoPoint::multiscalar_mul(&s, &r), expected);
        assert_eq!(
            RistrettoPoint::optional_multiscalar_mul(&s, r_opt),
            Some(expected)
        );
    }
}

// ---------------------------------------------------------------------------------------------
// Length mismatches panic
// ---------------------------------------------------------------------------------------------

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn edwards_more_scalars_panics() {
    EdwardsPoint::multiscalar_mul(&scalars(3), &edwards_points(2));
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn edwards_more_points_panics() {
    EdwardsPoint::multiscalar_mul(&scalars(2), &edwards_points(3));
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn edwards_optional_more_scalars_panics() {
    let p: Vec<_> = edwards_points(2).into_iter().map(Some).collect();
    EdwardsPoint::optional_multiscalar_mul(&scalars(3), p);
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn edwards_optional_more_points_with_none_panics() {
    let p = vec![Some(ED25519_BASEPOINT_POINT), None, None];
    EdwardsPoint::optional_multiscalar_mul(&scalars(2), p);
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn edwards_optional_more_scalars_with_none_panics() {
    EdwardsPoint::optional_multiscalar_mul(&scalars(3), [None]);
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn ristretto_more_scalars_panics() {
    RistrettoPoint::multiscalar_mul(&scalars(3), &ristretto_points(2));
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn ristretto_more_points_panics() {
    RistrettoPoint::multiscalar_mul(&scalars(2), &ristretto_points(3));
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn ristretto_optional_more_scalars_panics() {
    let p: Vec<_> = ristretto_points(2).into_iter().map(Some).collect();
    RistrettoPoint::optional_multiscalar_mul(&scalars(3), p);
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn ristretto_optional_more_points_with_none_panics() {
    let p = vec![Some(RISTRETTO_BASEPOINT_POINT), None, None];
    RistrettoPoint::optional_multiscalar_mul(&scalars(2), p);
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn ristretto_optional_more_scalars_with_none_panics() {
    RistrettoPoint::optional_multiscalar_mul(&scalars(3), [None]);
}
