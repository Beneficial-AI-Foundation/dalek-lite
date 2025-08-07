// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2019 Oleg Andreev
// See LICENSE for licensing information.
//
// Authors:
// - Oleg Andreev <oleganza@gmail.com>

//! Implementation of a variant of Pippenger's algorithm.

#![allow(non_snake_case)]

use alloc::vec::Vec;

use core::borrow::Borrow;
use core::cmp::Ordering;

use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::VartimeMultiscalarMul;

#[cfg(feature = "verus")]
use vstd::prelude::*;

#[cfg(feature = "verus")]
verus! {
    spec fn digit_bounds_valid(digit: i16, w: usize) -> bool {
        // Digits are in range [-2^w/2, 2^w/2], except the last digit may equal 2^w/2
        let max_magnitude = (1i16 << (w - 1));
        -max_magnitude <= digit && digit <= max_magnitude
    }

    spec fn bucket_index_safe(digit: i16, buckets_count: usize) -> bool {
        if digit > 0 {
            let b = (digit - 1) as usize;
            b < buckets_count
        } else if digit < 0 {
            let b = (-digit - 1) as usize;
            b < buckets_count
        } else {
            true // digit == 0, no bucket access
        }
    }

    spec fn window_width_valid(w: usize) -> bool {
        // Window width must be in valid range to prevent overflow
        4 <= w && w <= 8
    }

    spec fn bucket_count_consistent(w: usize, buckets_count: usize) -> bool {
        // buckets_count = (1 << w) / 2, which is 2^(w-1)
        // This ensures bucket indexing stays within bounds
        buckets_count == (1usize << (w - 1))
    }
}

/// Implements a version of Pippenger's algorithm.
///
/// The algorithm works as follows:
///
/// Let `n` be a number of point-scalar pairs.
/// Let `w` be a window of bits (6..8, chosen based on `n`, see cost factor).
///
/// 1. Prepare `2^(w-1) - 1` buckets with indices `[1..2^(w-1))` initialized with identity points.
///    Bucket 0 is not needed as it would contain points multiplied by 0.
/// 2. Convert scalars to a radix-`2^w` representation with signed digits in `[-2^w/2, 2^w/2]`.
///    Note: only the last digit may equal `2^w/2`.
/// 3. Starting with the last window, for each point `i=[0..n)` add it to a bucket indexed by
///    the point's scalar's value in the window.
/// 4. Once all points in a window are sorted into buckets, add buckets by multiplying each
///    by their index. Efficient way of doing it is to start with the last bucket and compute two sums:
///    intermediate sum from the last to the first, and the full sum made of all intermediate sums.
/// 5. Shift the resulting sum of buckets by `w` bits by using `w` doublings.
/// 6. Add to the return value.
/// 7. Repeat the loop.
///
/// Approximate cost w/o wNAF optimizations (A = addition, D = doubling):
///
/// ```ascii
/// cost = (n*A + 2*(2^w/2)*A + w*D + A)*256/w
///          |          |       |     |   |
///          |          |       |     |   looping over 256/w windows
///          |          |       |     adding to the result
///    sorting points   |       shifting the sum by w bits (to the next window, starting from last window)
///    one by one       |
///    into buckets     adding/subtracting all buckets
///                     multiplied by their indexes
///                     using a sum of intermediate sums
/// ```
///
/// For large `n`, dominant factor is (n*256/w) additions.
/// However, if `w` is too big and `n` is not too big, then `(2^w/2)*A` could dominate.
/// Therefore, the optimal choice of `w` grows slowly as `n` grows.
///
/// This algorithm is adapted from section 4 of <https://eprint.iacr.org/2012/549.pdf>.
pub struct Pippenger;

impl VartimeMultiscalarMul for Pippenger {
    type Point = EdwardsPoint;

    fn optional_multiscalar_mul<I, J>(scalars: I, points: J) -> Option<EdwardsPoint>
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator<Item = Option<EdwardsPoint>>,
    {
        #[cfg(feature = "verus")]
        requires([
            // The algorithm is designed for these window widths to prevent overflow
            // Window width determines bucket count and digit extraction bounds
            window_width_valid(6), // w=6 for size < 500
            window_width_valid(7), // w=7 for size < 800  
            window_width_valid(8), // w=8 for size >= 800
        ]);
        use crate::traits::Identity;

        let mut scalars = scalars.into_iter();
        let size = scalars.by_ref().size_hint().0;

        // Digit width in bits. As digit width grows,
        // number of point additions goes down, but amount of
        // buckets and bucket additions grows exponentially.
        let w = if size < 500 {
            6
        } else if size < 800 {
            7
        } else {
            8
        };

        let max_digit: usize = 1 << w;
        let digits_count: usize = Scalar::to_radix_2w_size_hint(w);
        let buckets_count: usize = max_digit / 2; // digits are signed+centered hence 2^w/2, excluding 0-th bucket

        #[cfg(feature = "verus")]
        assert([
            // Verify window width is in valid range (4 <= w <= 8)
            window_width_valid(w),
            // Verify bucket count consistency: buckets_count = 2^(w-1) 
            bucket_count_consistent(w, buckets_count),
            // Verify max_digit calculation doesn't overflow
            max_digit == (1usize << w),
            // Verify buckets_count = max_digit / 2
            buckets_count == max_digit / 2,
            // Verify digits_count is reasonable (should be <= 64 for scalar)
            digits_count <= 64,
        ]);

        // Collect optimized scalars and points in buffers for repeated access
        // (scanning the whole set per digit position).
        let scalars = scalars.map(|s| s.borrow().as_radix_2w(w));

        let points = points
            .into_iter()
            .map(|p| p.map(|P| P.as_projective_niels()));

        let scalars_points = scalars
            .zip(points)
            .map(|(s, maybe_p)| maybe_p.map(|p| (s, p)))
            .collect::<Option<Vec<_>>>()?;

        // Prepare 2^w/2 buckets.
        // buckets[i] corresponds to a multiplication factor (i+1).
        let mut buckets: Vec<_> = (0..buckets_count)
            .map(|_| EdwardsPoint::identity())
            .collect();

        let mut columns = (0..digits_count).rev().map(|digit_index| {
            // Clear the buckets when processing another digit.
            for bucket in &mut buckets {
                #[cfg(feature = "verus")]
                assert([
                    buckets.len() == buckets_count,  // Bucket array size consistency
                ]);
                
                *bucket = EdwardsPoint::identity();
            }

            // Iterate over pairs of (point, scalar)
            // and add/sub the point to the corresponding bucket.
            // Note: if we add support for precomputed lookup tables,
            // we'll be adding/subtracting point premultiplied by `digits[i]` to buckets[0].
            for (digits, pt) in scalars_points.iter() {
                #[cfg(feature = "verus")]
                assert([
                    buckets.len() == buckets_count,  // Bucket array size for safe indexing
                    buckets_count == (1usize << (w - 1)),  // Bucket count matches window width
                    digits.len() == digits_count,  // Each scalar has correct digit count
                    digit_index < digits.len(),  // Safe digits[digit_index] access
                ]);
                
                // Check digit bounds for this specific iteration
                #[cfg(feature = "verus")]
                assert(digit_index < digits_count);
                // Widen digit so that we don't run into edge cases when w=8.
                let digit = digits[digit_index] as i16;
                
                #[cfg(feature = "verus")]
                assert([
                    // Verify digit is in valid range for the window width
                    digit_bounds_valid(digit, w),
                    // Verify bucket indexing will be safe for this digit
                    bucket_index_safe(digit, buckets_count),
                ]);
                
                match digit.cmp(&0) {
                    Ordering::Greater => {
                        let b = (digit - 1) as usize;
                        #[cfg(feature = "verus")]
                        assert(b < buckets_count); // Verify bucket access is safe
                        buckets[b] = (&buckets[b] + pt).as_extended();
                    }
                    Ordering::Less => {
                        let b = (-digit - 1) as usize;
                        #[cfg(feature = "verus")]
                        assert(b < buckets_count); // Verify bucket access is safe
                        buckets[b] = (&buckets[b] - pt).as_extended();
                    }
                    Ordering::Equal => {}
                }
            }

            // Add the buckets applying the multiplication factor to each bucket.
            // The most efficient way to do that is to have a single sum with two running sums:
            // an intermediate sum from last bucket to the first, and a sum of intermediate sums.
            //
            // For example, to add buckets 1*A, 2*B, 3*C we need to add these points:
            //   C
            //   C B
            //   C B A   Sum = C + (C+B) + (C+B+A)
            #[cfg(feature = "verus")]
            assert([
                // Verify buckets_count > 0 so accessing buckets_count - 1 is safe
                buckets_count > 0,
                // Verify buckets_count - 1 is within buckets array bounds
                buckets_count - 1 < buckets.len(),
                // Verify buckets array has the expected size
                buckets.len() == buckets_count,
            ]);
            
            let mut buckets_intermediate_sum = buckets[buckets_count - 1];
            let mut buckets_sum = buckets[buckets_count - 1];
            for i in (0..(buckets_count - 1)).rev() {
                #[cfg(feature = "verus")]
                assert([
                    i < buckets_count - 1,  // Loop index bounds for safe buckets[i] access
                    buckets.len() == buckets_count,  // Bucket array size consistency
                    buckets_count > 0,  // Ensures buckets_count - 1 is valid
                    i < buckets.len(), // Verify array access is safe
                ]);
                
                buckets_intermediate_sum += buckets[i];
                buckets_sum += buckets_intermediate_sum;
            }

            buckets_sum
        });

        // Take the high column as an initial value to avoid wasting time doubling the identity element in `fold()`.
        let hi_column = columns.next().expect("should have more than zero digits");

        #[cfg(feature = "verus")]
        assert([
            // Verify w can be safely cast to u32 for mul_by_pow_2
            w <= u32::MAX as usize,
            // Verify w is in the expected range to prevent overflow in mul_by_pow_2
            w <= 8, // Maximum window width supported
        ]);

        Some(columns.fold(hi_column, |total, p| total.mul_by_pow_2(w as u32) + p))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::constants;

    #[test]
    fn test_vartime_pippenger() {
        // Reuse points across different tests
        let mut n = 512;
        let x = Scalar::from(2128506u64).invert();
        let y = Scalar::from(4443282u64).invert();
        let points: Vec<_> = (0..n)
            .map(|i| constants::ED25519_BASEPOINT_POINT * Scalar::from(1 + i as u64))
            .collect();
        let scalars: Vec<_> = (0..n)
            .map(|i| x + (Scalar::from(i as u64) * y)) // fast way to make ~random but deterministic scalars
            .collect();

        let premultiplied: Vec<EdwardsPoint> = scalars
            .iter()
            .zip(points.iter())
            .map(|(sc, pt)| sc * pt)
            .collect();

        while n > 0 {
            let scalars = &scalars[0..n].to_vec();
            let points = &points[0..n].to_vec();
            let control: EdwardsPoint = premultiplied[0..n].iter().sum();

            let subject = Pippenger::vartime_multiscalar_mul(scalars.clone(), points.clone());

            assert_eq!(subject.compress(), control.compress());

            n /= 2;
        }
    }
}
