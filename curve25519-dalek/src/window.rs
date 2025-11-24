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
//! Code for fixed- and sliding-window functionality
#![allow(non_snake_case)]

use core::fmt::Debug;

use cfg_if::cfg_if;

use subtle::Choice;
use subtle::ConditionallyNegatable;
use subtle::ConditionallySelectable;
use subtle::ConstantTimeEq;

use crate::traits::Identity;

use crate::backend::serial::curve_models::AffineNielsPoint;
use crate::backend::serial::curve_models::ProjectiveNielsPoint;
use crate::backend::serial::u64::subtle_assumes::{
    conditional_assign_generic, conditional_negate_field, ct_eq_u16, identity_generic,
};
use crate::edwards::EdwardsPoint;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

use vstd::prelude::*;

#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::edwards_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::field_specs::*;

verus! {

/// Specification trait for `From<T>` conversions, allowing preconditions
pub trait FromSpecImpl<T>: Sized {
    /// Whether this implementation provides a full specification
    spec fn obeys_from_spec() -> bool;

    /// Preconditions for the `from` conversion
    spec fn from_spec_req(src: T) -> bool;

    /// Specification for what the conversion produces
    spec fn from_spec(src: T) -> Self;
}

/// Spec: Check if a lookup table contains [P, 2P, 3P, ..., size*P] in ProjectiveNiels form
pub open spec fn is_valid_lookup_table_projective<const N: usize>(
    table: [ProjectiveNielsPoint; N],
    P: EdwardsPoint,
    size: nat,
) -> bool {
    &&& table.len() == size
    &&& forall|j: int|
        0 <= j < size ==> projective_niels_point_as_affine_edwards(#[trigger] table[j])
            == edwards_scalar_mul(edwards_point_as_affine(P), (j + 1) as nat)
}

/// Spec: Check if a lookup table contains [P, 2P, 3P, ..., size*P] in AffineNiels form
pub open spec fn is_valid_lookup_table_affine<const N: usize>(
    table: [AffineNielsPoint; N],
    P: EdwardsPoint,
    size: nat,
) -> bool {
    &&& table.len() == size
    &&& forall|j: int|
        0 <= j < size ==> affine_niels_point_as_affine_edwards(#[trigger] table[j])
            == edwards_scalar_mul(edwards_point_as_affine(P), (j + 1) as nat)
}

} // verus!
macro_rules! impl_lookup_table {
    (Name = $name:ident, Size = $size:expr, SizeNeg = $neg:expr, SizeRange = $range:expr, ConversionRange = $conv_range:expr) => {
        verus! {


        /// A lookup table of precomputed multiples of a point \\(P\\), used to
        /// compute \\( xP \\) for \\( -8 \leq x \leq 8 \\).
        ///
        /// The computation of \\( xP \\) is done in constant time by the `select` function.
        ///
        /// Since `LookupTable` does not implement `Index`, it's more difficult
        /// to accidentally use the table directly.  Unfortunately the table is
        /// only `pub(crate)` so that we can write hardcoded constants, so it's
        /// still technically possible.  It would be nice to prevent direct
        /// access to the table.
        ///
        /* VERIFICATION NOTE: Changed from `pub(crate)` to `pub` to allow Verus verification of
         the `from` function's ensures clause, which must be verifiable from outside this crate.
         */
        #[derive(Copy)]
        pub struct $name<T>(pub [T; $size]);


        /* VERIFICATION NOTE: Replaced generic impl with two concrete implementations
         to allow type-specific ensures clauses in the `select` function.

         ORIGINAL CODE:
         impl<T> $name<T>
         where
             T: Identity + ConditionallySelectable + ConditionallyNegatable,
         {
             pub fn select(&self, x: i8) -> (result: T)
                 ensures
                     (x > 0 ==> result == self.0[(x - 1) as int]),
                     // Generic T prevented type-specific specs for x == 0 and x < 0
             {...}
         }

         The `From` implementations were already concrete (one for AffineNielsPoint,
         one for ProjectiveNielsPoint), so they were unaffected by this change.
         */

        // Concrete implementation of select for AffineNielsPoint
        impl $name<AffineNielsPoint> {
            /// Given \\(-8 \leq x \leq 8\\), return \\(xP\\) in constant time.
            ///
            /// Where P is the base point that was used to create this lookup table.
            /// This table stores [P, 2P, 3P, ..., 8P] (for radix-16).
            pub fn select(&self, x: i8) -> (result: AffineNielsPoint)
                requires
                    $neg <= x,
                    x as i16 <= $size as i16,
                ensures
                    // Formal specification for all cases:
                    (x > 0 ==> result == self.0[(x - 1) as int]),
                    (x == 0 ==> result == identity_affine_niels()),
                    (x < 0 ==> result == negate_affine_niels(self.0[((-x) - 1) as int])),
            {
                // Debug assertions from original macro - ignored by Verus
                #[cfg(not(verus_keep_ghost))]
                {
                    debug_assert!(x >= $neg);
                    debug_assert!(x as i16 <= $size as i16);
                }

                assume(false);

                // Compute xabs = |x|
                let xmask = x as i16 >> 7;
                let xabs = (x as i16 + xmask) ^ xmask;

                // Set t = 0 * P = identity
                let mut t = AffineNielsPoint::identity();
                for j in $range {
                    // Copy `points[j-1] == j*P` onto `t` in constant time if `|x| == j`.
                    /* ORIGINAL CODE: let c = (xabs as u16).ct_eq(&(j as u16)); */
                    let c = ct_eq_u16(&(xabs as u16), &(j as u16));
                    /* ORIGINAL CODE: t.conditional_assign(&self.0[j - 1], c); */
                    conditional_assign_generic(&mut t, &self.0[j - 1], c);
                }
                // Now t == |x| * P.

                let neg_mask = Choice::from((xmask & 1) as u8);
                /* ORIGINAL CODE: t.conditional_negate(neg_mask); */
                conditional_negate_field(&mut t, neg_mask);
                // Now t == x * P.

                t
            }
        }

        // Concrete implementation of select for ProjectiveNielsPoint
        impl $name<ProjectiveNielsPoint> {
            /// Given \\(-8 \leq x \leq 8\\), return \\(xP\\) in constant time.
            ///
            /// Where P is the base point that was used to create this lookup table.
            /// This table stores [P, 2P, 3P, ..., 8P] (for radix-16).
            #[verifier::external_body]
            pub fn select(&self, x: i8) -> (result: ProjectiveNielsPoint)
                requires
                    $neg <= x,
                    x as i16 <= $size as i16,
                ensures
                    // Formal specification for all cases:
                    (x > 0 ==> result == self.0[(x - 1) as int]),
                    (x == 0 ==> result == identity_projective_niels()),
                    (x < 0 ==> result == negate_projective_niels(self.0[((-x) - 1) as int])),
            {
                // Debug assertions from original macro - ignored by Verus
                #[cfg(not(verus_keep_ghost))]
                {
                    debug_assert!(x >= $neg);
                    debug_assert!(x as i16 <= $size as i16);
                }

                assume(false);

                // Compute xabs = |x|
                let xmask = x as i16 >> 7;
                let xabs = (x as i16 + xmask) ^ xmask;

                // Set t = 0 * P = identity
                let mut t = ProjectiveNielsPoint::identity();
                for j in $range {
                    // Copy `points[j-1] == j*P` onto `t` in constant time if `|x| == j`.
                    /* ORIGINAL CODE: let c = (xabs as u16).ct_eq(&(j as u16)); */
                    let c = ct_eq_u16(&(xabs as u16), &(j as u16));
                    /* ORIGINAL CODE: t.conditional_assign(&self.0[j - 1], c); */
                    conditional_assign_generic(&mut t, &self.0[j - 1], c);
                }
                // Now t == |x| * P.

                let neg_mask = Choice::from((xmask & 1) as u8);
                /* ORIGINAL CODE: t.conditional_negate(neg_mask); */
                conditional_negate_field(&mut t, neg_mask);
                // Now t == x * P.

                t
            }
        }

        // Manual Clone implementation to avoid array clone issues in Verus
        impl<T: Copy> Clone for $name<T> {
            #[verifier::external_body]
            fn clone(&self) -> Self {
                *self
            }
        }

        impl<T: Copy + Default> Default for $name<T> {
            #[verifier::external_body]
            fn default() -> (result: $name<T>)
                ensures
                    // All table entries are set to the same default value
                    // (Cannot express T::default() in spec, but all entries are equal)
                    forall|i: int, j: int| 0 <= i < $size && 0 <= j < $size ==> result.0[i] == result.0[j],
            {
                $name([T::default(); $size])
            }
        }

        impl<T: Debug> Debug for $name<T> {
            #[verifier::external_body]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(f, "{:?}(", stringify!($name))?;

                for x in self.0.iter() {
                    write!(f, "{:?}", x)?;
                }

                write!(f, ")")
            }
        }

        /// Spec for From<&EdwardsPoint> conversion for ProjectiveNiels lookup table
        impl<'a> FromSpecImpl<&'a EdwardsPoint> for $name<ProjectiveNielsPoint> {
            open spec fn obeys_from_spec() -> bool {
                false
            }

            open spec fn from_spec_req(P: &'a EdwardsPoint) -> bool {
                // Preconditions needed for table construction
                limbs_bounded(&P.X, 54) && limbs_bounded(&P.Y, 54)
                    && limbs_bounded(&P.Z, 54) && limbs_bounded(&P.T, 54)
            }

            open spec fn from_spec(P: &'a EdwardsPoint) -> Self {
                arbitrary() // conditions specified in the ensures clause of the from function
            }
        }

        impl<'a> From<&'a EdwardsPoint> for $name<ProjectiveNielsPoint> {
            /// Create a lookup table from an EdwardsPoint
            /// Constructs [P, 2P, 3P, ..., Size*P]
            fn from(P: &'a EdwardsPoint) -> (result: Self)
                ensures
                    is_valid_lookup_table_projective(result.0, *P, $size as nat),
            {
                // Assume preconditions from FromSpecImpl::from_spec_req
                proof {
                    assume(limbs_bounded(&P.X, 54));
                    assume(limbs_bounded(&P.Y, 54));
                    assume(limbs_bounded(&P.Z, 54));
                    assume(limbs_bounded(&P.T, 54));
                }

                let mut points = [P.as_projective_niels(); $size];
                for j in $conv_range
                {
                    // ORIGINAL CODE:
                    // points[j + 1] = (P + &points[j]).as_extended().as_projective_niels();

                    // For Verus: unroll to assume preconditions for intermediate operations
                    proof {
                        // Preconditions for P (left-hand side of addition)
                        assume(sum_of_limbs_bounded(&P.Y, &P.X, u64::MAX));
                        assume(limbs_bounded(&P.X, 54));
                        assume(limbs_bounded(&P.Y, 54));
                        assume(limbs_bounded(&P.Z, 54));
                        assume(limbs_bounded(&P.T, 54));
                        // Preconditions for &points[j] (right-hand side - ProjectiveNielsPoint)
                        assume(limbs_bounded(&&points[j as int].Y_plus_X, 54));
                        assume(limbs_bounded(&&points[j as int].Y_minus_X, 54));
                        assume(limbs_bounded(&&points[j as int].Z, 54));
                        assume(limbs_bounded(&&points[j as int].T2d, 54));
                    }
                    let sum = P + &points[j];
                    proof {
                        // Preconditions for sum.as_extended()
                        assume(limbs_bounded(&sum.X, 54));
                        assume(limbs_bounded(&sum.Y, 54));
                        assume(limbs_bounded(&sum.Z, 54));
                        assume(limbs_bounded(&sum.T, 54));
                    }
                    let extended = sum.as_extended();
                    proof {
                        // Preconditions for extended.as_projective_niels()
                        assume(limbs_bounded(&extended.X, 54));
                        assume(limbs_bounded(&extended.Y, 54));
                        assume(limbs_bounded(&extended.Z, 54));
                        assume(limbs_bounded(&extended.T, 54));
                    }
                    points[j + 1] = extended.as_projective_niels();
                }
                let result = $name(points);
                proof {
                    assume(is_valid_lookup_table_projective(result.0, *P, $size as nat));
                }
                result
            }
        }

        /// Spec for From<&EdwardsPoint> conversion for AffineNiels lookup table
        impl<'a> FromSpecImpl<&'a EdwardsPoint> for $name<AffineNielsPoint> {
            open spec fn obeys_from_spec() -> bool {
                false
            }

            open spec fn from_spec_req(P: &'a EdwardsPoint) -> bool {
                // Preconditions needed for table construction
                limbs_bounded(&P.X, 54) && limbs_bounded(&P.Y, 54)
                    && limbs_bounded(&P.Z, 54) && limbs_bounded(&P.T, 54)
            }

            open spec fn from_spec(P: &'a EdwardsPoint) -> Self {
                arbitrary() // conditions specified in the ensures clause of the from function
            }
        }

        impl<'a> From<&'a EdwardsPoint> for $name<AffineNielsPoint> {
            /// Create a lookup table from an EdwardsPoint (affine version)
            /// Constructs [P, 2P, 3P, ..., Size*P]
            fn from(P: &'a EdwardsPoint) -> (result: Self)
                ensures
                    is_valid_lookup_table_affine(result.0, *P, $size as nat),
            {
                // Assume preconditions from FromSpecImpl::from_spec_req
                proof {
                    assume(limbs_bounded(&P.X, 54));
                    assume(limbs_bounded(&P.Y, 54));
                    assume(limbs_bounded(&P.Z, 54));
                    assume(limbs_bounded(&P.T, 54));
                }

                let mut points = [P.as_affine_niels(); $size];
                // XXX batch inversion would be good if perf mattered here
                for j in $conv_range
                {
                    // ORIGINAL CODE:
                    // points[j + 1] = (P + &points[j]).as_extended().as_affine_niels()

                    // For Verus: unroll to assume preconditions for intermediate operations
                    proof {
                        // Preconditions for P (left-hand side of addition)
                        assume(sum_of_limbs_bounded(&P.Y, &P.X, u64::MAX));
                        assume(sum_of_limbs_bounded(&P.Z, &P.Z, u64::MAX)); // for Z2 = &P.Z + &P.Z in add
                        assume(limbs_bounded(&P.X, 54));
                        assume(limbs_bounded(&P.Y, 54));
                        assume(limbs_bounded(&P.Z, 54));
                        assume(limbs_bounded(&P.T, 54));
                        // Preconditions for &points[j] (right-hand side - AffineNielsPoint)
                        assume(limbs_bounded(&&points[j as int].y_plus_x, 54));
                        assume(limbs_bounded(&&points[j as int].y_minus_x, 54));
                        assume(limbs_bounded(&&points[j as int].xy2d, 54));
                    }
                    let sum = P + &points[j];
                    proof {
                        // Preconditions for sum.as_extended()
                        assume(limbs_bounded(&sum.X, 54));
                        assume(limbs_bounded(&sum.Y, 54));
                        assume(limbs_bounded(&sum.Z, 54));
                        assume(limbs_bounded(&sum.T, 54));
                    }
                    let extended = sum.as_extended();
                    proof {
                        // Preconditions for extended.as_affine_niels()
                        assume(limbs_bounded(&extended.X, 54));
                        assume(limbs_bounded(&extended.Y, 54));
                        assume(limbs_bounded(&extended.Z, 54));
                        assume(limbs_bounded(&extended.T, 54));
                    }
                    points[j + 1] = extended.as_affine_niels()
                }
                let result = $name(points);
                proof {
                    assume(is_valid_lookup_table_affine(result.0, *P, $size as nat));
                }
                result
            }
        }
    } // verus!
        #[cfg(feature = "zeroize")]
        impl<T> Zeroize for $name<T>
        where
            T: Copy + Default + Zeroize,
        {
            fn zeroize(&mut self) {
                self.0.iter_mut().zeroize();
            }
        }
    };
} // End macro_rules! impl_lookup_table

// The first one has to be named "LookupTable" because it's used as a constructor for consts.
// This is radix-16
impl_lookup_table! {
    Name = LookupTable,
    Size = 8,
    SizeNeg = -8,
    SizeRange = 1..9,
    ConversionRange = 0..7
}

// The rest only get used to make basepoint tables
cfg_if! {
    if #[cfg(feature = "precomputed-tables")] {
        // radix-32
        impl_lookup_table! {
            Name = LookupTableRadix32,
            Size = 16,
            SizeNeg = -16,
            SizeRange = 1..17,
            ConversionRange = 0..15
        }
        // radix-64
        impl_lookup_table! {
            Name = LookupTableRadix64,
            Size = 32,
            SizeNeg = -32,
            SizeRange = 1..33,
            ConversionRange = 0..31
        }
        // radix-128
        impl_lookup_table! {
            Name = LookupTableRadix128,
            Size = 64,
            SizeNeg = -64,
            SizeRange = 1..65,
            ConversionRange = 0..63
        }
        // radix-256
        impl_lookup_table! {
            Name = LookupTableRadix256,
            Size = 128,
            SizeNeg = -128,
            SizeRange = 1..129,
            ConversionRange = 0..127
        }

        // For homogeneity we then alias it to "LookupTableRadix16".
        pub(crate) type LookupTableRadix16<T> = LookupTable<T>;
    }
}

/// Holds odd multiples 1A, 3A, ..., 15A of a point A.
#[derive(Copy, Clone)]
pub(crate) struct NafLookupTable5<T>(pub(crate) [T; 8]);

impl<T: Copy> NafLookupTable5<T> {
    /// Given public, odd \\( x \\) with \\( 0 < x < 2^4 \\), return \\(xA\\).
    pub fn select(&self, x: usize) -> T {
        debug_assert_eq!(x & 1, 1);
        debug_assert!(x < 16);

        self.0[x / 2]
    }
}

impl<T: Debug> Debug for NafLookupTable5<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "NafLookupTable5({:?})", self.0)
    }
}

impl<'a> From<&'a EdwardsPoint> for NafLookupTable5<ProjectiveNielsPoint> {
    fn from(A: &'a EdwardsPoint) -> Self {
        let mut Ai = [A.as_projective_niels(); 8];
        let A2 = A.double();
        for i in 0..7 {
            Ai[i + 1] = (&A2 + &Ai[i]).as_extended().as_projective_niels();
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
        NafLookupTable5(Ai)
    }
}

impl<'a> From<&'a EdwardsPoint> for NafLookupTable5<AffineNielsPoint> {
    fn from(A: &'a EdwardsPoint) -> Self {
        let mut Ai = [A.as_affine_niels(); 8];
        let A2 = A.double();
        for i in 0..7 {
            Ai[i + 1] = (&A2 + &Ai[i]).as_extended().as_affine_niels();
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
        NafLookupTable5(Ai)
    }
}

/// Holds stuff up to 8. The only time we use tables this big is for precomputed basepoint tables
/// and multiscalar multiplication (which requires alloc).
#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
#[derive(Copy, Clone)]
pub(crate) struct NafLookupTable8<T>(pub(crate) [T; 64]);

#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl<T: Copy> NafLookupTable8<T> {
    pub fn select(&self, x: usize) -> T {
        debug_assert_eq!(x & 1, 1);
        debug_assert!(x < 128);

        self.0[x / 2]
    }
}

#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl<T: Debug> Debug for NafLookupTable8<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        writeln!(f, "NafLookupTable8([")?;
        for i in 0..64 {
            writeln!(f, "\t{:?},", &self.0[i])?;
        }
        write!(f, "])")
    }
}

#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl<'a> From<&'a EdwardsPoint> for NafLookupTable8<ProjectiveNielsPoint> {
    fn from(A: &'a EdwardsPoint) -> Self {
        let mut Ai = [A.as_projective_niels(); 64];
        let A2 = A.double();
        for i in 0..63 {
            Ai[i + 1] = (&A2 + &Ai[i]).as_extended().as_projective_niels();
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A, ..., 127A]
        NafLookupTable8(Ai)
    }
}

#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl<'a> From<&'a EdwardsPoint> for NafLookupTable8<AffineNielsPoint> {
    fn from(A: &'a EdwardsPoint) -> Self {
        let mut Ai = [A.as_affine_niels(); 64];
        let A2 = A.double();
        for i in 0..63 {
            Ai[i + 1] = (&A2 + &Ai[i]).as_extended().as_affine_niels();
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A, ..., 127A]
        NafLookupTable8(Ai)
    }
}
