//! Tests for verifying Verus-compatible implementations match original implementations.
//!
//! These tests compare the _verus versions of multiscalar multiplication functions
//! against their original implementations to ensure functional equivalence.
#[cfg(test)]
mod tests {
    use crate::constants;
    use crate::edwards::EdwardsPoint;
    use crate::ristretto::RistrettoPoint;
    use crate::scalar::Scalar;
    use crate::traits::{MultiscalarMul, VartimeMultiscalarMul};
    use alloc::vec;
    use alloc::vec::Vec;

    use super::super::pippenger::Pippenger;
    use super::super::straus::Straus;

    /// Pippenger needs no bound on the scalars: with bit 255 set it still multiplies by the
    /// integer value. 2^256 - 1 is odd, so it fixes the order-2 point (0, -1); against the
    /// basepoint it acts as its reduction. Sizes 200, 600 and 900 select windows 6, 7 and 8.
    #[test]
    fn test_pippenger_scalar_with_bit_255_set() {
        let s = Scalar { bytes: [0xff; 32] };
        let t = constants::EIGHT_TORSION[4];
        let b = constants::ED25519_BASEPOINT_POINT;
        let b_expected = b * Scalar::from_bytes_mod_order(s.bytes);
        for size in [200usize, 600, 900] {
            let mut scalars = vec![Scalar::ZERO; size];
            scalars[0] = s;
            for (p, expected) in [(t, t), (b, b_expected)] {
                let points = vec![Some(p); size];
                let verus = Pippenger::optional_multiscalar_mul_verus(&scalars, &points);
                let original =
                    Pippenger::optional_multiscalar_mul(scalars.iter(), points.iter().copied());
                assert_eq!(verus, Some(expected), "size={}", size);
                assert_eq!(original, Some(expected), "size={}", size);
            }
        }
    }

    /// Borrowing a point changes the scalar that the other iterator yields.
    #[test]
    fn multiscalar_with_shared_iterator_state() {
        use core::{borrow::Borrow, cell::Cell, iter::once};

        struct Point<'a>(&'a Cell<bool>, EdwardsPoint);

        impl Borrow<EdwardsPoint> for Point<'_> {
            fn borrow(&self) -> &EdwardsPoint {
                self.0.set(true);
                &self.1
            }
        }

        let flag = Cell::new(false);
        let base = constants::ED25519_BASEPOINT_POINT;
        let scalars = once(()).map(|_| {
            if flag.get() {
                Scalar::ONE
            } else {
                Scalar::ZERO
            }
        });
        let points = once(Point(&flag, base));
        assert_eq!(EdwardsPoint::multiscalar_mul(scalars, points), base);
    }

    #[test]
    fn multiscalar_respects_overridden_by_ref() {
        struct SkipFirst<T>(alloc::vec::IntoIter<T>);

        impl<T> Iterator for SkipFirst<T> {
            type Item = T;

            fn next(&mut self) -> Option<T> {
                self.0.next()
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                self.0.size_hint()
            }

            fn by_ref(&mut self) -> &mut Self {
                self.next();
                self
            }
        }

        let base = constants::ED25519_BASEPOINT_POINT;
        let scalars = SkipFirst(alloc::vec![Scalar::ONE, Scalar::from(2u8)].into_iter());
        let points = SkipFirst(alloc::vec![base, base].into_iter());
        assert_eq!(EdwardsPoint::multiscalar_mul(scalars, points), base + base);

        // Ristretto checks the length through Map::by_ref(), preserving both input points.
        let base = constants::RISTRETTO_BASEPOINT_POINT;
        let points = SkipFirst(vec![base, base + base].into_iter());
        let scalars = [Scalar::ONE, Scalar::ONE];
        assert_eq!(
            RistrettoPoint::multiscalar_mul(scalars, points),
            base + base + base
        );
    }

    #[test]
    fn test_pippenger_original_vs_verus() {
        // Test sizes covering all window width cases:
        // w=6 for size < 500, w=7 for 500 <= size < 800, w=8 for size >= 800
        let test_sizes = [
            1, 2, 3, 4, 8, 16, 32, 64, 128, 256, 499, 500, 501, 799, 800, 801, 1000,
        ];

        let num_rounds = 20; // Random rounds per size
        let mut total_comparisons = 0;

        for size in test_sizes {
            for round in 0..num_rounds {
                // Generate pseudo-random scalars and points using deterministic seeds
                // Different seed for each (size, round) combination
                let seed_base = (size as u64) * 1000 + (round as u64);

                let points: Vec<_> = (0..size)
                    .map(|i| {
                        let seed = Scalar::from(seed_base + (i as u64) * 7 + 1);
                        constants::ED25519_BASEPOINT_POINT * seed
                    })
                    .collect();

                let scalars: Vec<_> = (0..size)
                    .map(|i| {
                        let a = Scalar::from(seed_base * 3 + (i as u64) * 13 + 5);
                        let b = Scalar::from((i as u64) + 1);
                        a * b // Mix to get varied scalars
                    })
                    .collect();

                // Original implementation
                let original = Pippenger::optional_multiscalar_mul(
                    scalars.iter(),
                    points.iter().map(|p| Some(*p)),
                );

                // Verus implementation
                let opt_points: Vec<_> = points.iter().map(|p| Some(*p)).collect();
                let verus = Pippenger::optional_multiscalar_mul_verus(&scalars, &opt_points);

                assert!(
                    original.is_some(),
                    "Original returned None at size={}, round={}",
                    size,
                    round
                );
                assert!(
                    verus.is_some(),
                    "Verus returned None at size={}, round={}",
                    size,
                    round
                );

                assert_eq!(
                    original.unwrap().compress(),
                    verus.unwrap().compress(),
                    "Mismatch at size={}, round={}",
                    size,
                    round
                );

                total_comparisons += 1;
            }
        }

        println!(
            "Pippenger original vs verus: {} comparisons passed!",
            total_comparisons
        );
    }

    #[test]
    fn test_straus_optional_original_vs_verus() {
        // Test various sizes
        let test_sizes = [1, 2, 3, 4, 8, 16, 32, 64, 100, 150];

        let num_rounds = 20; // Random rounds per size
        let mut total_comparisons = 0;

        for size in test_sizes {
            for round in 0..num_rounds {
                // Generate pseudo-random scalars and points using deterministic seeds
                let seed_base = (size as u64) * 1000 + (round as u64);

                let points: Vec<_> = (0..size)
                    .map(|i| {
                        let seed = Scalar::from(seed_base + (i as u64) * 7 + 1);
                        constants::ED25519_BASEPOINT_POINT * seed
                    })
                    .collect();

                let scalars: Vec<_> = (0..size)
                    .map(|i| {
                        let a = Scalar::from(seed_base * 3 + (i as u64) * 13 + 5);
                        let b = Scalar::from((i as u64) + 1);
                        a * b
                    })
                    .collect();

                // Original implementation
                let original = Straus::optional_multiscalar_mul(
                    scalars.iter(),
                    points.iter().map(|p| Some(*p)),
                );

                // Verus implementation
                let opt_points: Vec<_> = points.iter().map(|p| Some(*p)).collect();
                let verus = Straus::optional_multiscalar_mul_verus(&scalars, &opt_points);

                assert!(
                    original.is_some(),
                    "Original returned None at size={}, round={}",
                    size,
                    round
                );
                assert!(
                    verus.is_some(),
                    "Verus returned None at size={}, round={}",
                    size,
                    round
                );

                assert_eq!(
                    original.unwrap().compress(),
                    verus.unwrap().compress(),
                    "Mismatch at size={}, round={}",
                    size,
                    round
                );

                total_comparisons += 1;
            }
        }

        println!(
            "Straus optional original vs verus: {} comparisons passed!",
            total_comparisons
        );
    }

    #[test]
    fn test_straus_multiscalar_original_vs_verus() {
        // Test various sizes (constant-time multiscalar_mul)
        let test_sizes = [1, 2, 3, 4, 8, 16, 32, 64, 100, 150];

        let num_rounds = 20; // Random rounds per size
        let mut total_comparisons = 0;

        for size in test_sizes {
            for round in 0..num_rounds {
                // Generate pseudo-random scalars and points using deterministic seeds
                let seed_base = (size as u64) * 1000 + (round as u64);

                let points: Vec<_> = (0..size)
                    .map(|i| {
                        let seed = Scalar::from(seed_base + (i as u64) * 7 + 1);
                        constants::ED25519_BASEPOINT_POINT * seed
                    })
                    .collect();

                let scalars: Vec<_> = (0..size)
                    .map(|i| {
                        let a = Scalar::from(seed_base * 3 + (i as u64) * 13 + 5);
                        let b = Scalar::from((i as u64) + 1);
                        a * b
                    })
                    .collect();

                // Original implementation (via trait)
                let original = Straus::multiscalar_mul(scalars.iter(), points.iter());

                // Verus implementation
                let verus = Straus::multiscalar_mul_verus(&scalars, &points);

                assert_eq!(
                    original.compress(),
                    verus.compress(),
                    "Mismatch at size={}, round={}",
                    size,
                    round
                );

                total_comparisons += 1;
            }
        }

        println!(
            "Straus multiscalar_mul original vs verus: {} comparisons passed!",
            total_comparisons
        );
    }

    #[test]
    fn test_edwards_optional_dispatcher_original_vs_verus() {
        // Test sizes on both sides of the dispatch threshold (190)
        // size < 190: uses Straus
        // size >= 190: uses Pippenger
        let test_sizes = [1, 10, 50, 100, 150, 189, 190, 191, 200, 300];

        let num_rounds = 10;
        let mut total_comparisons = 0;

        for size in test_sizes {
            for round in 0..num_rounds {
                let seed_base = (size as u64) * 1000 + (round as u64);

                let points: Vec<_> = (0..size)
                    .map(|i| {
                        let seed = Scalar::from(seed_base + (i as u64) * 7 + 1);
                        constants::ED25519_BASEPOINT_POINT * seed
                    })
                    .collect();

                let scalars: Vec<_> = (0..size)
                    .map(|i| {
                        let a = Scalar::from(seed_base * 3 + (i as u64) * 13 + 5);
                        let b = Scalar::from((i as u64) + 1);
                        a * b
                    })
                    .collect();

                // Original EdwardsPoint dispatcher
                let original = EdwardsPoint::optional_multiscalar_mul(
                    scalars.iter(),
                    points.iter().map(|p| Some(*p)),
                );

                // Verus EdwardsPoint dispatcher
                let verus = EdwardsPoint::optional_multiscalar_mul_verus(
                    scalars.iter().cloned(),
                    points.iter().map(|p| Some(*p)),
                );

                // Verified slice version
                let opt_points: Vec<_> = points.iter().map(|p| Some(*p)).collect();
                let slices = EdwardsPoint::optional_multiscalar_mul_slices(&scalars, &opt_points);
                assert_eq!(
                    original.map(|p| p.compress()),
                    slices.map(|p| p.compress()),
                    "Slice mismatch at size={}, round={}",
                    size,
                    round
                );

                assert!(
                    original.is_some(),
                    "Original returned None at size={}, round={}",
                    size,
                    round
                );
                assert!(
                    verus.is_some(),
                    "Verus returned None at size={}, round={}",
                    size,
                    round
                );

                assert_eq!(
                    original.unwrap().compress(),
                    verus.unwrap().compress(),
                    "Mismatch at size={}, round={}",
                    size,
                    round
                );

                total_comparisons += 1;
            }
        }

        println!(
            "Edwards optional dispatcher original vs verus: {} comparisons passed!",
            total_comparisons
        );
    }

    #[test]
    fn test_edwards_multiscalar_dispatcher_original_vs_verus() {
        // Test sizes (constant-time version only dispatches to Straus)
        let test_sizes = [1, 10, 50, 100, 150, 189];

        let num_rounds = 10;
        let mut total_comparisons = 0;

        for size in test_sizes {
            for round in 0..num_rounds {
                let seed_base = (size as u64) * 1000 + (round as u64);

                let points: Vec<_> = (0..size)
                    .map(|i| {
                        let seed = Scalar::from(seed_base + (i as u64) * 7 + 1);
                        constants::ED25519_BASEPOINT_POINT * seed
                    })
                    .collect();

                let scalars: Vec<_> = (0..size)
                    .map(|i| {
                        let a = Scalar::from(seed_base * 3 + (i as u64) * 13 + 5);
                        let b = Scalar::from((i as u64) + 1);
                        a * b
                    })
                    .collect();

                // Original EdwardsPoint dispatcher (via trait)
                let original = EdwardsPoint::multiscalar_mul(scalars.iter(), points.iter());

                // Verus EdwardsPoint dispatcher
                let verus = EdwardsPoint::multiscalar_mul_verus(scalars.iter(), points.iter());

                // Verified slice version
                let slices = EdwardsPoint::multiscalar_mul_slices(&scalars, &points);
                assert_eq!(
                    original.compress(),
                    slices.compress(),
                    "Slice mismatch at size={}, round={}",
                    size,
                    round
                );

                assert_eq!(
                    original.compress(),
                    verus.compress(),
                    "Mismatch at size={}, round={}",
                    size,
                    round
                );

                total_comparisons += 1;
            }
        }

        println!(
            "Edwards multiscalar_mul dispatcher original vs verus: {} comparisons passed!",
            total_comparisons
        );
    }
}
