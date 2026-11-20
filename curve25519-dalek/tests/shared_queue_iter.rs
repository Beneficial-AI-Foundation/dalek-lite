//! Regression tests for issue #793.
//!
//! The iterators below share a queue with their clones, as the `Clone` documentation allows for
//! types that hold references, so consuming a clone drains the original. Other legal iterators
//! can also change shared state in `Clone` or `Drop`. The `*_verus` multiscalar functions state
//! their `ensures` over the sequences that the inputs yield, so they must not clone their inputs.
//! Each test checks the result and uses a shared counter to check that no clone was made.
#![cfg(feature = "alloc")]

use core::cell::{Cell, RefCell};
use std::collections::VecDeque;

use curve25519_dalek::constants::{ED25519_BASEPOINT_POINT as EB, RISTRETTO_BASEPOINT_POINT as RB};
use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{MultiscalarMul, VartimeMultiscalarMul};

/// Sizes to test. `optional_multiscalar_mul_verus` uses Straus below 190 and Pippenger from 190.
const SIZES: [usize; 3] = [0, 2, 190];

/// An iterator over a shared queue. Clones share the queue and increment a shared counter.
/// `size_hint` is exact.
struct SharedQueueIter<'a, T> {
    queue: &'a RefCell<VecDeque<T>>,
    remaining: usize,
    clones: &'a Cell<usize>,
}

impl<T> Clone for SharedQueueIter<'_, T> {
    fn clone(&self) -> Self {
        self.clones.set(self.clones.get() + 1);
        SharedQueueIter {
            queue: self.queue,
            remaining: self.remaining,
            clones: self.clones,
        }
    }
}

impl<T> Iterator for SharedQueueIter<'_, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        self.queue.borrow_mut().pop_front()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.remaining.min(self.queue.borrow().len());
        (n, Some(n))
    }
}

fn shared<'a, T>(
    queue: &'a RefCell<VecDeque<T>>,
    clones: &'a Cell<usize>,
) -> SharedQueueIter<'a, T> {
    let remaining = queue.borrow().len();
    SharedQueueIter {
        queue,
        remaining,
        clones,
    }
}

fn scalars(n: usize) -> Vec<Scalar> {
    (0..n).map(|i| Scalar::from(2 * i as u64 + 3)).collect()
}

fn edwards_points(n: usize) -> Vec<EdwardsPoint> {
    (0..n).map(|i| EB * Scalar::from(i as u64 + 1)).collect()
}

fn ristretto_points(n: usize) -> Vec<RistrettoPoint> {
    (0..n).map(|i| RB * Scalar::from(i as u64 + 1)).collect()
}

fn edwards_sum(s: &[Scalar], p: &[EdwardsPoint]) -> EdwardsPoint {
    s.iter().zip(p).map(|(a, b)| a * b).sum()
}

fn ristretto_sum(s: &[Scalar], p: &[RistrettoPoint]) -> RistrettoPoint {
    s.iter().zip(p).map(|(a, b)| a * b).sum()
}

#[test]
fn edwards_optional_multiscalar_mul_verus_shared_queue() {
    for n in SIZES {
        let (s, p) = (scalars(n), edwards_points(n));
        let stated = edwards_sum(&s, &p);
        let opt: Vec<Option<EdwardsPoint>> = p.into_iter().map(Some).collect();

        let clones = Cell::new(0);
        let qs = RefCell::new(VecDeque::from(s.clone()));
        let qp = RefCell::new(VecDeque::from(opt.clone()));
        let r = EdwardsPoint::optional_multiscalar_mul_verus(
            shared(&qs, &clones),
            shared(&qp, &clones),
        );
        assert_eq!(r, Some(stated), "n = {n}");
        assert_eq!(clones.get(), 0, "n = {n}: inputs were cloned");

        // Control: the original API on the same kind of input.
        let qs = RefCell::new(VecDeque::from(s));
        let orig = EdwardsPoint::optional_multiscalar_mul(shared(&qs, &clones), opt);
        assert_eq!(orig, Some(stated), "n = {n}: original API");
    }
}

#[test]
fn edwards_multiscalar_mul_verus_shared_queue() {
    for n in SIZES {
        let (s, p) = (scalars(n), edwards_points(n));
        let stated = edwards_sum(&s, &p);

        let clones = Cell::new(0);
        let qs = RefCell::new(VecDeque::from(s.clone()));
        let qp = RefCell::new(VecDeque::from(p.clone()));
        let r = EdwardsPoint::multiscalar_mul_verus(shared(&qs, &clones), shared(&qp, &clones));
        assert_eq!(r, stated, "n = {n}");
        assert_eq!(clones.get(), 0, "n = {n}: inputs were cloned");

        let qs = RefCell::new(VecDeque::from(s));
        let orig = EdwardsPoint::multiscalar_mul(shared(&qs, &clones), p);
        assert_eq!(orig, stated, "n = {n}: original API");
    }
}

#[test]
fn ristretto_optional_multiscalar_mul_verus_shared_queue() {
    for n in SIZES {
        let (s, p) = (scalars(n), ristretto_points(n));
        let stated = ristretto_sum(&s, &p);
        let opt: Vec<Option<RistrettoPoint>> = p.into_iter().map(Some).collect();

        let clones = Cell::new(0);
        let qs = RefCell::new(VecDeque::from(s.clone()));
        let qp = RefCell::new(VecDeque::from(opt.clone()));
        let r = RistrettoPoint::optional_multiscalar_mul_verus(
            shared(&qs, &clones),
            shared(&qp, &clones),
        );
        assert_eq!(r, Some(stated), "n = {n}");
        assert_eq!(clones.get(), 0, "n = {n}: inputs were cloned");

        let qs = RefCell::new(VecDeque::from(s));
        let orig = RistrettoPoint::optional_multiscalar_mul(shared(&qs, &clones), opt);
        assert_eq!(orig, Some(stated), "n = {n}: original API");
    }
}

#[test]
fn ristretto_multiscalar_mul_verus_shared_queue() {
    for n in SIZES {
        let (s, p) = (scalars(n), ristretto_points(n));
        let stated = ristretto_sum(&s, &p);

        let clones = Cell::new(0);
        let qs = RefCell::new(VecDeque::from(s.clone()));
        let qp = RefCell::new(VecDeque::from(p.clone()));
        let r = RistrettoPoint::multiscalar_mul_verus(shared(&qs, &clones), shared(&qp, &clones));
        assert_eq!(r, stated, "n = {n}");
        assert_eq!(clones.get(), 0, "n = {n}: inputs were cloned");

        let qs = RefCell::new(VecDeque::from(s));
        let orig = RistrettoPoint::multiscalar_mul(shared(&qs, &clones), p);
        assert_eq!(orig, stated, "n = {n}: original API");
    }
}

/// The positions of the `None` point in the tests below: first and last.
fn none_positions(n: usize) -> [usize; 2] {
    [0, n - 1]
}

#[test]
fn edwards_optional_multiscalar_mul_verus_shared_queue_none() {
    for n in [2, 190] {
        for k in none_positions(n) {
            let mut opt: Vec<Option<EdwardsPoint>> =
                edwards_points(n).into_iter().map(Some).collect();
            opt[k] = None;

            let clones = Cell::new(0);
            let qs = RefCell::new(VecDeque::from(scalars(n)));
            let qp = RefCell::new(VecDeque::from(opt));
            let r = EdwardsPoint::optional_multiscalar_mul_verus(
                shared(&qs, &clones),
                shared(&qp, &clones),
            );
            assert_eq!(r, None, "n = {n}, None at {k}");
            assert_eq!(clones.get(), 0, "n = {n}, None at {k}: inputs were cloned");
        }
    }
}

#[test]
fn ristretto_optional_multiscalar_mul_verus_shared_queue_none() {
    for n in [2, 190] {
        for k in none_positions(n) {
            let mut opt: Vec<Option<RistrettoPoint>> =
                ristretto_points(n).into_iter().map(Some).collect();
            opt[k] = None;

            let clones = Cell::new(0);
            let qs = RefCell::new(VecDeque::from(scalars(n)));
            let qp = RefCell::new(VecDeque::from(opt));
            let r = RistrettoPoint::optional_multiscalar_mul_verus(
                shared(&qs, &clones),
                shared(&qp, &clones),
            );
            assert_eq!(r, None, "n = {n}, None at {k}");
            assert_eq!(clones.get(), 0, "n = {n}, None at {k}: inputs were cloned");
        }
    }
}
