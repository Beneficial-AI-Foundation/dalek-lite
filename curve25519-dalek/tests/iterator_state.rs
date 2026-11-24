//! Run-time behavior of scalar aggregation and multiscalar multiplication for iterators
//! with external state. These tests exercise the order of size checks, borrows, and iteration
//! in the public iterator methods and the legacy `*_multiscalar_mul_verus` adapters.
#![cfg(feature = "alloc")]
#![allow(non_snake_case)]

use core::cell::Cell;
use core::sync::atomic::{AtomicU64, Ordering};

use curve25519_dalek::constants::{ED25519_BASEPOINT_POINT, RISTRETTO_BASEPOINT_POINT};
use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{Identity, VartimeMultiscalarMul};

// ---------------------------------------------------------------------------------------------
// Iterators with outside state
// ---------------------------------------------------------------------------------------------

/// Yields `left` scalars read from a global counter. Two equal values yield different items.
struct CounterIter<'a> {
    left: usize,
    ctr: &'a AtomicU64,
}

impl Iterator for CounterIter<'_> {
    type Item = Scalar;
    fn next(&mut self) -> Option<Scalar> {
        if self.left == 0 {
            return None;
        }
        self.left -= 1;
        Some(Scalar::from(self.ctr.fetch_add(1, Ordering::SeqCst)))
    }
}

/// Sets the shared flag in `next`. Exact size hint without side effects.
#[derive(Clone)]
struct SetsFlagOnNext<'a, T: Clone> {
    items: Vec<T>,
    flag: &'a Cell<bool>,
}

impl<T: Clone> Iterator for SetsFlagOnNext<'_, T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        self.flag.set(true);
        if self.items.is_empty() {
            None
        } else {
            Some(self.items.remove(0))
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.items.len(), Some(self.items.len()))
    }
}

/// Sets the shared flag in `size_hint`. The hint itself is exact.
#[derive(Clone)]
struct SetsFlagOnHint<'a, T: Clone> {
    items: Vec<T>,
    flag: &'a Cell<bool>,
}

impl<T: Clone> Iterator for SetsFlagOnHint<'_, T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if self.items.is_empty() {
            None
        } else {
            Some(self.items.remove(0))
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.flag.set(true);
        (self.items.len(), Some(self.items.len()))
    }
}

/// Yields the identity in place of each item once the shared flag is set.
#[derive(Clone)]
struct IdentityAfterFlag<'a, T: Clone + Identity> {
    items: Vec<T>,
    flag: &'a Cell<bool>,
}

impl<T: Clone + Identity> Iterator for IdentityAfterFlag<'_, T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if self.items.is_empty() {
            return None;
        }
        let p = self.items.remove(0);
        Some(if self.flag.get() { T::identity() } else { p })
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.items.len(), Some(self.items.len()))
    }
}

/// Yields `left` scalars: 10 if the shared flag is set, 1 otherwise.
#[derive(Clone)]
struct ScalarReadsFlag<'a> {
    left: usize,
    flag: &'a Cell<bool>,
}

impl Iterator for ScalarReadsFlag<'_> {
    type Item = Scalar;
    fn next(&mut self) -> Option<Scalar> {
        if self.left == 0 {
            return None;
        }
        self.left -= 1;
        Some(Scalar::from(if self.flag.get() { 10u64 } else { 1u64 }))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.left, Some(self.left))
    }
}

/// Yields its items, with the inexact size hint `(0, None)`.
#[derive(Clone)]
struct NoHint<T: Clone>(Vec<T>);

impl<T: Clone> Iterator for NoHint<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if self.0.is_empty() {
            None
        } else {
            Some(self.0.remove(0))
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }
}

fn s(x: u64) -> Scalar {
    Scalar::from(x)
}

// ---------------------------------------------------------------------------------------------
// Case 1 of the issue: equal iterator values, different items
// ---------------------------------------------------------------------------------------------

#[test]
fn scalar_sum_equal_iterators() {
    let ctr = AtomicU64::new(1);
    let r1: Scalar = CounterIter { left: 2, ctr: &ctr }.sum();
    let r2: Scalar = CounterIter { left: 2, ctr: &ctr }.sum();
    assert_eq!(r1, s(1) + s(2));
    assert_eq!(r2, s(3) + s(4));
}

#[test]
fn scalar_product_equal_iterators() {
    let ctr = AtomicU64::new(1);
    let r1: Scalar = CounterIter { left: 2, ctr: &ctr }.product();
    let r2: Scalar = CounterIter { left: 2, ctr: &ctr }.product();
    assert_eq!(r1, s(1) * s(2));
    assert_eq!(r2, s(3) * s(4));
}

// ---------------------------------------------------------------------------------------------
// Case 2 of the issue: the two iterators share state
// ---------------------------------------------------------------------------------------------

/// The Edwards functions collect `scalars` first. That sets the flag, so the points iterator
/// then yields the identity for every point.
#[test]
fn edwards_multiscalar_mul_verus_shared_flag() {
    let B = ED25519_BASEPOINT_POINT;
    let flag = Cell::new(false);
    let scalars = SetsFlagOnNext {
        items: vec![s(2), s(5)],
        flag: &flag,
    };
    let points = IdentityAfterFlag {
        items: vec![B, B + B],
        flag: &flag,
    };
    let r = EdwardsPoint::multiscalar_mul_verus(scalars, points);
    assert_eq!(r, EdwardsPoint::identity());
}

#[test]
fn edwards_optional_multiscalar_mul_verus_shared_flag() {
    let B = ED25519_BASEPOINT_POINT;
    let flag = Cell::new(false);
    let scalars = SetsFlagOnNext {
        items: vec![s(2), s(5)],
        flag: &flag,
    };
    let points = IdentityAfterFlag {
        items: vec![B, B + B],
        flag: &flag,
    }
    .map(Some);
    let r = EdwardsPoint::optional_multiscalar_mul_verus(scalars, points);
    assert_eq!(r, Some(EdwardsPoint::identity()));
}

/// The Ristretto functions collect `points` first, before the flag is set, so the result is
/// 2·B + 5·(2B) = 12B.
#[test]
fn ristretto_multiscalar_mul_verus_shared_flag() {
    let B = RISTRETTO_BASEPOINT_POINT;
    let flag = Cell::new(false);
    let scalars = SetsFlagOnNext {
        items: vec![s(2), s(5)],
        flag: &flag,
    };
    let points = IdentityAfterFlag {
        items: vec![B, B + B],
        flag: &flag,
    };
    let r = RistrettoPoint::multiscalar_mul_verus(scalars, points);
    assert_eq!(r, B * s(12));
}

#[test]
fn ristretto_optional_multiscalar_mul_verus_shared_flag() {
    let B = RISTRETTO_BASEPOINT_POINT;
    let flag = Cell::new(false);
    let scalars = SetsFlagOnNext {
        items: vec![s(2), s(5)],
        flag: &flag,
    };
    let points = IdentityAfterFlag {
        items: vec![B, B + B],
        flag: &flag,
    }
    .map(Some);
    let r = RistrettoPoint::optional_multiscalar_mul_verus(scalars, points);
    assert_eq!(r, Some(B * s(12)));
}

/// Ristretto projects each point when Straus asks for it, after Straus has read the scalars.
#[test]
fn ristretto_optional_multiscalar_mul_projects_points_lazily() {
    let flag = Cell::new(false);
    let scalars = SetsFlagOnNext {
        items: vec![s(1)],
        flag: &flag,
    };
    let points = IdentityAfterFlag {
        items: vec![RISTRETTO_BASEPOINT_POINT],
        flag: &flag,
    };
    assert_eq!(
        RistrettoPoint::optional_multiscalar_mul(scalars, points.map(Some)),
        Some(RistrettoPoint::identity()),
    );
}

// ---------------------------------------------------------------------------------------------
// Side effects in `size_hint`
// ---------------------------------------------------------------------------------------------

/// The Edwards functions call `points.size_hint()` before they collect `scalars`, so the scalar
/// is 10.
#[test]
fn edwards_multiscalar_mul_verus_size_hint_side_effect() {
    let B = ED25519_BASEPOINT_POINT;
    let flag = Cell::new(false);
    let scalars = ScalarReadsFlag {
        left: 1,
        flag: &flag,
    };
    let points = SetsFlagOnHint {
        items: vec![B],
        flag: &flag,
    };
    let r = EdwardsPoint::multiscalar_mul_verus(scalars, points);
    assert_eq!(r, B * s(10));
}

#[test]
fn edwards_optional_multiscalar_mul_verus_size_hint_side_effect() {
    let B = ED25519_BASEPOINT_POINT;
    let flag = Cell::new(false);
    let scalars = ScalarReadsFlag {
        left: 1,
        flag: &flag,
    };
    let points = SetsFlagOnHint {
        items: vec![Some(B)],
        flag: &flag,
    };
    let r = EdwardsPoint::optional_multiscalar_mul_verus(scalars, points);
    assert_eq!(r, Some(B * s(10)));
}

/// The Ristretto functions collect `points` first. Collection into a `Vec` calls `size_hint`,
/// which sets the flag before `scalars` is collected, so the scalar is 10.
#[test]
fn ristretto_multiscalar_mul_verus_size_hint_side_effect() {
    let B = RISTRETTO_BASEPOINT_POINT;
    let flag = Cell::new(false);
    let scalars = ScalarReadsFlag {
        left: 1,
        flag: &flag,
    };
    let points = SetsFlagOnHint {
        items: vec![B],
        flag: &flag,
    };
    let r = RistrettoPoint::multiscalar_mul_verus(scalars, points);
    assert_eq!(r, B * s(10));
}

#[test]
fn ristretto_optional_multiscalar_mul_verus_size_hint_side_effect() {
    let B = RISTRETTO_BASEPOINT_POINT;
    let flag = Cell::new(false);
    let scalars = ScalarReadsFlag {
        left: 1,
        flag: &flag,
    };
    let points = SetsFlagOnHint {
        items: vec![Some(B)],
        flag: &flag,
    };
    let r = RistrettoPoint::optional_multiscalar_mul_verus(scalars, points);
    assert_eq!(r, Some(B * s(10)));
}

// ---------------------------------------------------------------------------------------------
// Inexact size hints: the Edwards functions assert that the hints are exact and equal
// ---------------------------------------------------------------------------------------------

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn edwards_multiscalar_mul_verus_inexact_hint_panics() {
    let B = ED25519_BASEPOINT_POINT;
    let _ = EdwardsPoint::multiscalar_mul_verus(NoHint(vec![s(1), s(2)]), NoHint(vec![B, B]));
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn edwards_optional_multiscalar_mul_verus_inexact_hint_panics() {
    let B = ED25519_BASEPOINT_POINT;
    let _ = EdwardsPoint::optional_multiscalar_mul_verus(
        NoHint(vec![s(1), s(2)]),
        NoHint(vec![Some(B), Some(B)]),
    );
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn ristretto_multiscalar_mul_verus_inexact_hint_panics() {
    let B = RISTRETTO_BASEPOINT_POINT;
    let _ = RistrettoPoint::multiscalar_mul_verus(NoHint(vec![s(1), s(2)]), NoHint(vec![B, B]));
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn ristretto_optional_multiscalar_mul_verus_inexact_hint_panics() {
    let B = RISTRETTO_BASEPOINT_POINT;
    let _ = RistrettoPoint::optional_multiscalar_mul_verus(
        NoHint(vec![s(1), s(2)]),
        NoHint(vec![Some(B), Some(B)]),
    );
}

/// Straus prepares all scalars first. Pippenger checks the scalar length a second time
/// and borrows each scalar immediately before consuming the corresponding optional point.
#[test]
fn edwards_optional_msm_stops_at_first_missing_point() {
    struct CountByRef<'a, I>(I, &'a Cell<usize>);
    impl<I: Iterator> Iterator for CountByRef<'_, I> {
        type Item = I::Item;

        fn next(&mut self) -> Option<Self::Item> {
            self.0.next()
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            self.0.size_hint()
        }

        fn by_ref(&mut self) -> &mut Self {
            self.1.set(self.1.get() + 1);
            self
        }
    }

    struct CountBorrow<'a>(&'a Cell<usize>);
    impl core::borrow::Borrow<Scalar> for CountBorrow<'_> {
        fn borrow(&self) -> &Scalar {
            self.0.set(self.0.get() + 1);
            &Scalar::ONE
        }
    }

    for (len, expected_hint_calls) in [(189, 1), (190, 2)] {
        let hint_calls = Cell::new(0);
        let borrows = Cell::new(0);
        let points_read = Cell::new(0);
        let scalars = CountByRef((0..len).map(|_| CountBorrow(&borrows)), &hint_calls);
        let points = (0..len).map(|i| {
            points_read.set(points_read.get() + 1);
            assert_eq!(borrows.get(), if len < 190 { len } else { i + 1 });
            (i != 1).then_some(ED25519_BASEPOINT_POINT)
        });

        assert_eq!(
            EdwardsPoint::optional_multiscalar_mul(scalars, points),
            None
        );
        assert_eq!(points_read.get(), 2);
        assert_eq!(hint_calls.get(), expected_hint_calls);
    }
}
