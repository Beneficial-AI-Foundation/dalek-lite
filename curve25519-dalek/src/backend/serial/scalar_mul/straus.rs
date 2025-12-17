// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2021 isis lovecruft
// Copyright (c) 2016-2019 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>
//! Implementation of the interleaved window method, also known as Straus' method.
#![allow(non_snake_case)]

use alloc::vec::Vec;

use core::borrow::Borrow;
use core::cmp::Ordering;

use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::MultiscalarMul;
use crate::traits::VartimeMultiscalarMul;

#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_mul_specs::*;
use vstd::prelude::*;

/// Perform multiscalar multiplication by the interleaved window
/// method, also known as Straus' method (since it was apparently
/// [first published][solution] by Straus in 1964, as a solution to [a
/// problem][problem] posted in the American Mathematical Monthly in
/// 1963).
///
/// It is easy enough to reinvent, and has been repeatedly.  The basic
/// idea is that when computing
/// \\[
/// Q = s_1 P_1 + \cdots + s_n P_n
/// \\]
/// by means of additions and doublings, the doublings can be shared
/// across the \\( P_i \\\).
///
/// We implement two versions, a constant-time algorithm using fixed
/// windows and a variable-time algorithm using sliding windows.  They
/// are slight variations on the same idea, and are described in more
/// detail in the respective implementations.
///
/// [solution]: https://www.jstor.org/stable/2310929
/// [problem]: https://www.jstor.org/stable/2312273

use crate::backend::serial::curve_models::ProjectiveNielsPoint;
use crate::window::LookupTable;
use crate::window::NafLookupTable5;

verus! {

// External-body helpers for iterator operations not supported by Verus

/// Collect points into lookup tables for Straus algorithm
#[verifier::external_body]
fn collect_lookup_tables<I, J>(points: J) -> (result: Vec<LookupTable<ProjectiveNielsPoint>>)
where
    J: IntoIterator,
    J::Item: Borrow<EdwardsPoint>,

    ensures
        // Length of result matches number of input points
        result@.len() == spec_points_len::<J>(points) as int,
        // Each lookup table corresponds to its input point
        forall|i: int|
            0 <= i < result@.len() ==> spec_lookup_table_point(&#[trigger] result@[i])
                == spec_points_from_into_iter::<J>(points)[i],
{
    points
        .into_iter()
        .map(|point| LookupTable::<ProjectiveNielsPoint>::from(point.borrow()))
        .collect()
}

/// Collect scalars into radix-16 digit arrays
#[verifier::external_body]
fn collect_scalar_digits<I>(scalars: I) -> (result: Vec<[i8; 64]>)
where
    I: IntoIterator,
    I::Item: Borrow<Scalar>,

    ensures
        // Length of result matches number of input scalars
        result@.len() == spec_scalars_len::<I>(scalars) as int,
        // Each digit array corresponds to its input scalar
        forall|i: int|
            0 <= i < result@.len() ==> spec_radix16_digits_to_scalar(&#[trigger] result@[i])
                == spec_scalars_from_into_iter::<I>(scalars)[i],
{
    scalars
        .into_iter()
        .map(|s| s.borrow().as_radix_16())
        .collect()
}

/// Collect scalars into NAF form
#[verifier::external_body]
fn collect_nafs<I>(scalars: I) -> (result: Vec<[i8; 256]>)
where
    I: IntoIterator,
    I::Item: Borrow<Scalar>,

    ensures
        // Length of result matches number of input scalars
        result@.len() == spec_scalars_len::<I>(scalars) as int,
        // Each NAF array corresponds to its input scalar
        forall|i: int|
            0 <= i < result@.len() ==> spec_naf_digits_to_scalar(&#[trigger] result@[i])
                == spec_scalars_from_into_iter::<I>(scalars)[i],
{
    scalars
        .into_iter()
        .map(|c| c.borrow().non_adjacent_form(5))
        .collect()
}

/// Collect optional points into NAF lookup tables
#[verifier::external_body]
fn collect_naf_lookup_tables<J>(points: J) -> (result: Option<Vec<NafLookupTable5<ProjectiveNielsPoint>>>)
where
    J: IntoIterator<Item = Option<EdwardsPoint>>,

    ensures
        // Result is Some iff spec_optional_points returns Some
        match (result, spec_optional_points_from_into_iter::<J>(points)) {
            (Some(tables), Some(pts)) => {
                // Length matches
                &&& tables@.len() == pts.len()
                // Each lookup table corresponds to its input point
                &&& forall|i: int|
                    0 <= i < tables@.len() ==> spec_naf_lookup_table_point(&#[trigger] tables@[i])
                        == pts[i]
            },
            (None, None) => true,
            _ => false,
        },
{
    points
        .into_iter()
        .map(|P_opt| P_opt.map(|P| NafLookupTable5::<ProjectiveNielsPoint>::from(&P)))
        .collect::<Option<Vec<_>>>()
}

/// Zeroize scalar digits for security
#[cfg(feature = "zeroize")]
#[verifier::external_body]
fn zeroize_scalar_digits(scalar_digits: &mut Vec<[i8; 64]>)
{
    zeroize::Zeroize::zeroize(scalar_digits);
}

pub struct Straus {}

impl MultiscalarMul for Straus {
    type Point = EdwardsPoint;

    /// Constant-time Straus using a fixed window of size \\(4\\).
    ///
    /// Our goal is to compute
    /// \\[
    /// Q = s_1 P_1 + \cdots + s_n P_n.
    /// \\]
    ///
    /// For each point \\( P_i \\), precompute a lookup table of
    /// \\[
    /// P_i, 2P_i, 3P_i, 4P_i, 5P_i, 6P_i, 7P_i, 8P_i.
    /// \\]
    ///
    /// For each scalar \\( s_i \\), compute its radix-\\(2^4\\)
    /// signed digits \\( s_{i,j} \\), i.e.,
    /// \\[
    ///    s_i = s_{i,0} + s_{i,1} 16^1 + ... + s_{i,63} 16^{63},
    /// \\]
    /// with \\( -8 \leq s_{i,j} < 8 \\).  Since \\( 0 \leq |s_{i,j}|
    /// \leq 8 \\), we can retrieve \\( s_{i,j} P_i \\) from the
    /// lookup table with a conditional negation: using signed
    /// digits halves the required table size.
    ///
    /// Then as in the single-base fixed window case, we have
    /// \\[
    /// \begin{aligned}
    /// s_i P_i &= P_i (s_{i,0} +     s_{i,1} 16^1 + \cdots +     s_{i,63} 16^{63})   \\\\
    /// s_i P_i &= P_i s_{i,0} + P_i s_{i,1} 16^1 + \cdots + P_i s_{i,63} 16^{63}     \\\\
    /// s_i P_i &= P_i s_{i,0} + 16(P_i s_{i,1} + 16( \cdots +16P_i s_{i,63})\cdots )
    /// \end{aligned}
    /// \\]
    /// so each \\( s_i P_i \\) can be computed by alternately adding
    /// a precomputed multiple \\( P_i s_{i,j} \\) of \\( P_i \\) and
    /// repeatedly doubling.
    ///
    /// Now consider the two-dimensional sum
    /// \\[
    /// \begin{aligned}
    /// s\_1 P\_1 &=& P\_1 s\_{1,0} &+& 16 (P\_1 s\_{1,1} &+& 16 ( \cdots &+& 16 P\_1 s\_{1,63}&) \cdots ) \\\\
    ///     +     & &      +        & &      +            & &             & &     +            &           \\\\
    /// s\_2 P\_2 &=& P\_2 s\_{2,0} &+& 16 (P\_2 s\_{2,1} &+& 16 ( \cdots &+& 16 P\_2 s\_{2,63}&) \cdots ) \\\\
    ///     +     & &      +        & &      +            & &             & &     +            &           \\\\
    /// \vdots    & &  \vdots       & &   \vdots          & &             & &  \vdots          &           \\\\
    ///     +     & &      +        & &      +            & &             & &     +            &           \\\\
    /// s\_n P\_n &=& P\_n s\_{n,0} &+& 16 (P\_n s\_{n,1} &+& 16 ( \cdots &+& 16 P\_n s\_{n,63}&) \cdots )
    /// \end{aligned}
    /// \\]
    /// The sum of the left-hand column is the result \\( Q \\); by
    /// computing the two-dimensional sum on the right column-wise,
    /// top-to-bottom, then right-to-left, we need to multiply by \\(
    /// 16\\) only once per column, sharing the doublings across all
    /// of the input points.
    fn multiscalar_mul<I, J>(scalars: I, points: J) -> (result: EdwardsPoint)
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator,
        J::Item: Borrow<EdwardsPoint>,

        ensures
            edwards_point_as_affine(result) == spec_multiscalar_mul(
                spec_scalars_from_into_iter::<I>(scalars),
                spec_points_from_into_iter::<J>(points),
            ),
    {
        use crate::traits::Identity;

        /* ORIGINAL CODE:
        let lookup_tables: Vec<_> = points
            .into_iter()
            .map(|point| LookupTable::<ProjectiveNielsPoint>::from(point.borrow()))
            .collect();
        */
        // Rewritten: use external_body helper for iterator operations
        let lookup_tables = collect_lookup_tables::<I, J>(points);

        // This puts the scalar digits into a heap-allocated Vec.
        // To ensure that these are erased, pass ownership of the Vec into a
        // Zeroizing wrapper.
        /* ORIGINAL CODE:
        let mut scalar_digits: Vec<_> = scalars
            .into_iter()
            .map(|s| s.borrow().as_radix_16())
            .collect();
        */
        // Rewritten: use external_body helper for iterator operations
        #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
        let mut scalar_digits = collect_scalar_digits(scalars);

        let mut Q = EdwardsPoint::identity();
        /* ORIGINAL CODE:
        for j in (0..64).rev() {
            Q = Q.mul_by_pow_2(4);
            let it = scalar_digits.iter().zip(lookup_tables.iter());
            for (s_i, lookup_table_i) in it {
                // R_i = s_{i,j} * P_i
                let R_i = lookup_table_i.select(s_i[j]);
                // Q = Q + R_i
                Q = (&Q + &R_i).as_extended();
            }
        }
        */
        // Rewritten for Verus compatibility (rev() and zip() not supported)
        let n = scalar_digits.len();
        let mut j: usize = 64;
        while j > 0 {
            j = j - 1;
            // TODO: need to prove preconditions for mul_by_pow_2 and arithmetic traits (Add)
            assume(false);
            Q = Q.mul_by_pow_2(4);
            for idx in 0..n {
                let s_i = &scalar_digits[idx];
                let lookup_table_i = &lookup_tables[idx];
                // R_i = s_{i,j} * P_i
                let R_i = lookup_table_i.select(s_i[j]);
                // Q = Q + R_i
                Q = (&Q + &R_i).as_extended();
            }
        }

        /* ORIGINAL CODE: zeroize::Zeroize::zeroize(&mut scalar_digits); */
        // Rewritten: use external_body helper
        #[cfg(feature = "zeroize")]
        zeroize_scalar_digits(&mut scalar_digits);

        Q
    }
}

} // verus!

verus! {

impl VartimeMultiscalarMul for Straus {
    type Point = EdwardsPoint;

    /// Variable-time Straus using a non-adjacent form of width \\(5\\).
    ///
    /// This is completely similar to the constant-time code, but we
    /// use a non-adjacent form for the scalar, and do not do table
    /// lookups in constant time.
    ///
    /// The non-adjacent form has signed, odd digits.  Using only odd
    /// digits halves the table size (since we only need odd
    /// multiples), or gives fewer additions for the same table size.
    fn optional_multiscalar_mul<I, J>(scalars: I, points: J) -> (result: Option<EdwardsPoint>)
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator<Item = Option<EdwardsPoint>>,

        ensures
            match (result, spec_optional_points_from_into_iter::<J>(points)) {
                (Some(r), Some(pts)) => edwards_point_as_affine(r) == spec_multiscalar_mul(
                    spec_scalars_from_into_iter::<I>(scalars),
                    pts,
                ),
                (None, None) => true,
                _ => false,
            },
    {
        use crate::backend::serial::curve_models::{
            CompletedPoint, ProjectivePoint,
        };
        use crate::traits::Identity;

        /* ORIGINAL CODE:
        let nafs: Vec<_> = scalars
            .into_iter()
            .map(|c| c.borrow().non_adjacent_form(5))
            .collect();
        */
        // Rewritten: use external_body helper for iterator operations
        let nafs = collect_nafs(scalars);

        /* ORIGINAL CODE:
        let lookup_tables = points
            .into_iter()
            .map(|P_opt| P_opt.map(|P| NafLookupTable5::<ProjectiveNielsPoint>::from(&P)))
            .collect::<Option<Vec<_>>>()?;
        */
        // Rewritten: use external_body helper for iterator operations
        let lookup_tables = collect_naf_lookup_tables(points)?;

        let mut r = ProjectivePoint::identity();

        /* ORIGINAL CODE:
        for i in (0..256).rev() {
            let mut t: CompletedPoint = r.double();

            for (naf, lookup_table) in nafs.iter().zip(lookup_tables.iter()) {
                match naf[i].cmp(&0) {
                    Ordering::Greater => {
                        t = &t.as_extended() + &lookup_table.select(naf[i] as usize)
                    }
                    Ordering::Less => t = &t.as_extended() - &lookup_table.select(-naf[i] as usize),
                    Ordering::Equal => {}
                }
            }

            r = t.as_projective();
        }
        */
        // Rewritten for Verus compatibility (rev() and zip() not supported)
        let num_points = nafs.len();
        let mut i: usize = 256;
        while i > 0 {
            i = i - 1;
            // TODO: need to prove preconditions for double and arithmetic traits (Add, Sub)
            assume(false);
            let mut t: CompletedPoint = r.double();

            for idx in 0..num_points {
                let naf = &nafs[idx];
                let lookup_table = &lookup_tables[idx];
                match naf[i].cmp(&0) {
                    Ordering::Greater => {
                        t = &t.as_extended() + &lookup_table.select(naf[i] as usize)
                    }
                    Ordering::Less => t = &t.as_extended() - &lookup_table.select(-naf[i] as usize),
                    Ordering::Equal => {}
                }
            }

            r = t.as_projective();
        }

        Some(r.as_extended())
    }
}

} // verus!
