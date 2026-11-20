//! The multiscalar slice functions accept unreduced scalars whose bit 255 is clear, and they
//! multiply by the integer value of each scalar, not by its reduction modulo the group order.
#![cfg(feature = "alloc")]

use curve25519_dalek::constants::{
    ED25519_BASEPOINT_POINT, EIGHT_TORSION, RISTRETTO_BASEPOINT_POINT,
};
use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::Identity;

/// The group order ℓ as an unreduced scalar. Its reduction is zero.
#[allow(deprecated)]
const ELL: Scalar = curve25519_dalek::constants::BASEPOINT_ORDER;

/// 2^255 - 1: above ℓ, bit 255 clear.
const MAX_BIT_255_CLEAR: Scalar = Scalar {
    bytes: [
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0x7f,
    ],
};

/// Sizes that select Straus (1) and the Pippenger windows 6, 7 and 8 (200, 600, 900) in the
/// variable-time functions.
const SIZES: [usize; 4] = [1, 200, 600, 900];

/// The point of order 2, (0, -1).
fn order_two_point() -> EdwardsPoint {
    let t = EIGHT_TORSION[4];
    assert_ne!(t, EdwardsPoint::identity());
    assert_eq!(t + t, EdwardsPoint::identity());
    t
}

/// `n` inputs: `s` at position 0 and zero scalars elsewhere, all with point `p`. The sum is
/// `[s]p` for every `n`. Repeating `s` would cancel for the order-2 point when `n` is even.
fn padded(n: usize, s: Scalar, p: EdwardsPoint) -> (Vec<Scalar>, Vec<EdwardsPoint>) {
    let mut scalars = vec![Scalar::ZERO; n];
    scalars[0] = s;
    (scalars, vec![p; n])
}

fn reduced(s: Scalar) -> Scalar {
    Scalar::from_bytes_mod_order(s.bytes)
}

#[test]
fn ell_times_order_two_point_is_the_point() {
    // ℓ is odd, so [ℓ]T = T. Reducing ℓ first would give the identity.
    let t = order_two_point();
    for n in SIZES {
        let (scalars, points) = padded(n, ELL, t);
        let opt_points: Vec<_> = points.iter().copied().map(Some).collect();
        assert_eq!(
            EdwardsPoint::multiscalar_mul_slices(&scalars, &points),
            t,
            "n = {n}"
        );
        assert_eq!(
            EdwardsPoint::optional_multiscalar_mul_slices(&scalars, &opt_points),
            Some(t),
            "n = {n}"
        );
    }
}

#[test]
fn unreduced_scalar_times_basepoint() {
    let b = ED25519_BASEPOINT_POINT;
    let expected = b * reduced(MAX_BIT_255_CLEAR);
    for n in SIZES {
        let (scalars, points) = padded(n, MAX_BIT_255_CLEAR, b);
        let opt_points: Vec<_> = points.iter().copied().map(Some).collect();
        assert_eq!(
            EdwardsPoint::multiscalar_mul_slices(&scalars, &points),
            expected,
            "n = {n}"
        );
        assert_eq!(
            EdwardsPoint::optional_multiscalar_mul_slices(&scalars, &opt_points),
            Some(expected),
            "n = {n}"
        );
    }
}

#[test]
fn unreduced_scalars_ristretto() {
    let b = RISTRETTO_BASEPOINT_POINT;
    for s in [ELL, MAX_BIT_255_CLEAR] {
        let expected = b * reduced(s);
        for n in SIZES {
            let mut scalars = vec![Scalar::ZERO; n];
            scalars[0] = s;
            let points = vec![b; n];
            let opt_points: Vec<_> = points.iter().copied().map(Some).collect();
            assert_eq!(
                RistrettoPoint::multiscalar_mul_slices(&scalars, &points),
                expected,
                "n = {n}"
            );
            assert_eq!(
                RistrettoPoint::optional_multiscalar_mul_slices(&scalars, &opt_points),
                Some(expected),
                "n = {n}"
            );
        }
    }
}
