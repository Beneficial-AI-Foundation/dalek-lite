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
    conditional_assign_generic, conditional_negate_affine_niels, conditional_negate_generic,
    ct_eq_u16,
};
use crate::edwards::EdwardsPoint;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::backend::serial::u64::subtle_assumes::choice_is_true;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::{
    lemma_identity_affine_niels_valid, lemma_negate_affine_niels_preserves_validity,
};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::add_lemmas::lemma_sum_of_limbs_bounded_from_fe51_bounded;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::edwards_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::field_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::window_specs::*;
use vstd::prelude::*;

/* VERIFICATION NOTE: Removed unused impl_lookup_table! macro since LookupTable
(radix-16) was manually expanded. */

verus! {

/* VERIFICATION NOTE: Manually expanded impl_lookup_table! macro for radix-16 (LookupTable).
   Removed macro invocations for radix-32, 64, 128, 256 variants to focus verification
   on the primary radix-16 implementation used as a constructor for consts.

   Original macro invocation:
impl_lookup_table! {
    Name = LookupTable,
    Size = 8,
    SizeNeg = -8,
    SizeRange = 1..9,
    ConversionRange = 0..7
   }
*/
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
pub struct LookupTable<T>(pub [T; 8]);

/* VERIFICATION NOTE: Replaced generic impl with two concrete implementations
 to allow type-specific ensures clauses in the `select` function.

 ORIGINAL CODE:
 impl<T> LookupTable<T>
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
impl LookupTable<AffineNielsPoint> {
    /// Given \\(-8 \leq x \leq 8\\), return \\(xP\\) in constant time.
    ///
    /// Where P is the base point that was used to create this lookup table.
    /// This table stores [P, 2P, 3P, ..., 8P] (for radix-16).
    pub fn select(&self, x: i8) -> (result: AffineNielsPoint)
        requires
            -8 <= x,
            x <= 8,
            lookup_table_affine_limbs_bounded(self.0),
            // Per-entry validity is required because select returns table entries directly
            // (when x > 0) and must guarantee is_valid_affine_niels_point(result).
            // This cannot be derived from lookup_table_affine_limbs_bounded (which only
            // constrains limb magnitudes) or is_valid_lookup_table_affine (which constrains
            // (y+x, y-x) coordinates but not xy2d). Validity requires all three fields
            // to be consistent with some EdwardsPoint.
            // All callers construct tables via From<&EdwardsPoint>, whose as_affine_niels
            // ensures per-entry validity.
            forall|j: int| 0 <= j < 8 ==> is_valid_affine_niels_point(#[trigger] self.0[j]),
        ensures
    // Formal specification for all cases:

            (x > 0 ==> result == self.0[(x - 1) as int]),
            (x == 0 ==> result == identity_affine_niels()),
            (x < 0 ==> result == negate_affine_niels(self.0[((-x) - 1) as int])),
            // Limb bounds on result
            fe51_limbs_bounded(&result.y_plus_x, 54),
            fe51_limbs_bounded(&result.y_minus_x, 54),
            fe51_limbs_bounded(&result.xy2d, 54),
            // The result is a valid AffineNielsPoint
            is_valid_affine_niels_point(result),
    {
        // Debug assertions from original macro - ignored by Verus
        #[cfg(not(verus_keep_ghost))]
        {
            debug_assert!(x >= -8);
            debug_assert!(x <= 8);
        }

        // Compute xabs = |x|
        let xmask = x as i16 >> 7;
        proof {
            // xmask is 0 or -1, so x + xmask doesn't overflow i16
            assert((x as i16 >> 7u32) == 0i16 || (x as i16 >> 7u32) == -1i16) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
            ;
        }
        let xabs = (x as i16 + xmask) ^ xmask;

        proof {
            // WI3: Bit-vector facts about xmask, xabs
            // In Verus spec mode, i16 + i16 returns int (for overflow safety),
            // making `(x as i16 + xmask) ^ xmask` fail because int has no XOR.
            // Work around by binding the sum as i16 so XOR stays in bitvector land.
            let xsum: i16 = (x as i16 + xmask) as i16;
            assert(x >= 0i8 ==> xabs == x as i16) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
                    xmask == (x as i16 >> 7u32),
                    xsum == (x as i16 + xmask) as i16,
                    xabs == (xsum ^ xmask),
            ;
            assert(x < 0i8 ==> xabs == -(x as i16)) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
                    xmask == (x as i16 >> 7u32),
                    xsum == (x as i16 + xmask) as i16,
                    xabs == (xsum ^ xmask),
            ;
            assert(0 <= xabs && xabs <= 8);
            // xmask sign (used later for neg_mask)
            assert(x >= 0i8 ==> (x as i16 >> 7u32) == 0i16) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
            ;
            assert(x < 0i8 ==> (x as i16 >> 7u32) == -1i16) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
            ;
        }

        // Set t = 0 * P = identity
        let mut t = AffineNielsPoint::identity();
        proof {
            // Identity has trivially bounded limbs (all 0 or 1)
            assert(1u64 < (1u64 << 54u64)) by (bit_vector);
            assert(0u64 < (1u64 << 54u64)) by (bit_vector);
            assert(fe51_limbs_bounded(&t.y_plus_x, 54)) by {
                assert(t.y_plus_x.limbs[0] < (1u64 << 54u64));
                assert(t.y_plus_x.limbs[1] < (1u64 << 54u64));
                assert(t.y_plus_x.limbs[2] < (1u64 << 54u64));
                assert(t.y_plus_x.limbs[3] < (1u64 << 54u64));
                assert(t.y_plus_x.limbs[4] < (1u64 << 54u64));
            }
            assert(fe51_limbs_bounded(&t.y_minus_x, 54)) by {
                assert(t.y_minus_x.limbs[0] < (1u64 << 54u64));
                assert(t.y_minus_x.limbs[1] < (1u64 << 54u64));
                assert(t.y_minus_x.limbs[2] < (1u64 << 54u64));
                assert(t.y_minus_x.limbs[3] < (1u64 << 54u64));
                assert(t.y_minus_x.limbs[4] < (1u64 << 54u64));
            }
            assert(fe51_limbs_bounded(&t.xy2d, 54)) by {
                assert(t.xy2d.limbs[0] < (1u64 << 54u64));
                assert(t.xy2d.limbs[1] < (1u64 << 54u64));
                assert(t.xy2d.limbs[2] < (1u64 << 54u64));
                assert(t.xy2d.limbs[3] < (1u64 << 54u64));
                assert(t.xy2d.limbs[4] < (1u64 << 54u64));
            }
            lemma_identity_affine_niels_valid();
        }

        for j in 1..9
            invariant
                -8 <= x,
                x <= 8,
                0 <= xabs,
                xabs <= 8,
                // xabs correctly computed
                (x >= 0 ==> xabs == x as i16),
                (x < 0 ==> xabs == -(x as i16)),
                // CT scan state: t holds the right value based on progress
                (xabs > 0 && (xabs as int) < j) ==> t == self.0[(xabs - 1) as int],
                (xabs == 0 || (xabs as int) >= j) ==> t == identity_affine_niels(),
                // Limb bounds preserved
                fe51_limbs_bounded(&t.y_plus_x, 54),
                fe51_limbs_bounded(&t.y_minus_x, 54),
                fe51_limbs_bounded(&t.xy2d, 54),
                // Validity preserved
                is_valid_affine_niels_point(t),
                // Table state (from preconditions, carry through loop)
                lookup_table_affine_limbs_bounded(self.0),
                forall|k: int| 0 <= k < 8 ==> is_valid_affine_niels_point(#[trigger] self.0[k]),
        {
            // Copy `points[j-1] == j*P` onto `t` in constant time if `|x| == j`.
            /* ORIGINAL CODE: let c = (xabs as u16).ct_eq(&(j as u16)); */
            let c = ct_eq_u16(&(xabs as u16), &(j as u16));
            /* ORIGINAL CODE: t.conditional_assign(&self.0[j - 1], c); */
            conditional_assign_generic(&mut t, &self.0[j - 1], c);
            proof {
                // After conditional_assign: if xabs == j, then t == self.0[j-1];
                // otherwise t is unchanged.
                if choice_is_true(c) {
                    assert(xabs as u16 == j as u16);
                    assert(t == self.0[(j - 1) as int]);
                }
            }
        }
        // Now t == |x| * P.

        proof {
            // Post-loop: at j == 9, the loop invariant gives us:
            // If xabs > 0 && xabs < 9: t == self.0[(xabs-1)]
            // If xabs == 0: t == identity_affine_niels()
            // Since 0 <= xabs <= 8, the case xabs >= 9 is impossible.
            if x > 0 {
                assert(xabs == x as i16);
                assert(xabs > 0 && (xabs as i32) < 9);
                assert(t == self.0[(xabs - 1) as int]);
                assert(t == self.0[(x - 1) as int]);
            } else if x == 0i8 {
                assert(xabs == 0);
                assert(t == identity_affine_niels());
            } else {
                // x < 0
                assert(xabs == -(x as i16));
                assert(xabs > 0 && (xabs as i32) < 9);
                assert(t == self.0[(xabs - 1) as int]);
                assert(t == self.0[((-x) - 1) as int]);
            }
        }

        let ghost old_t = t;
        proof {
            // xmask & 1 is 0 or 1, safe to cast to u8
            assert((xmask & 1i16) == 0i16 || (xmask & 1i16) == 1i16) by (bit_vector)
                requires
                    xmask == 0i16 || xmask == -1i16,
            ;
        }
        let neg_mask = Choice::from((xmask & 1) as u8);
        proof {
            // WI3: neg_mask bit-vector facts
            assert(x < 0i8 ==> ((xmask & 1i16) as u8 == 1u8)) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
                    xmask == (x as i16 >> 7u32),
            ;
            assert(x >= 0i8 ==> ((xmask & 1i16) as u8 == 0u8)) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
                    xmask == (x as i16 >> 7u32),
            ;
        }
        /* ORIGINAL CODE: t.conditional_negate(neg_mask); */
        conditional_negate_affine_niels(&mut t, neg_mask);
        proof {
            if x >= 0 {
                // neg_mask is false, so t is unchanged
                assert(!choice_is_true(neg_mask));
                assert(t == old_t);
            } else {
                // x < 0: neg_mask is true
                assert(choice_is_true(neg_mask));
                assert(t == negate_affine_niels(old_t));
                assert(old_t == self.0[((-x) - 1) as int]);
                // Prove validity of negated point
                lemma_negate_affine_niels_preserves_validity(old_t);
            }
        }
        // Now t == x * P.

        t
    }
}

// Concrete implementation of select for ProjectiveNielsPoint
impl LookupTable<ProjectiveNielsPoint> {
    /// Given \\(-8 \leq x \leq 8\\), return \\(xP\\) in constant time.
    ///
    /// Where P is the base point that was used to create this lookup table.
    /// This table stores [P, 2P, 3P, ..., 8P] (for radix-16).
    // TODO: prove select correctness once ct primitives are verified.
    pub fn select(&self, x: i8) -> (result: ProjectiveNielsPoint)
        requires
            -8 <= x,
            x <= 8,
            // Table entries must have bounded limbs
            lookup_table_projective_limbs_bounded(self.0),
        ensures
    // Formal specification for all cases:

            (x > 0 ==> result == self.0[(x - 1) as int]),
            (x == 0 ==> result == identity_projective_niels()),
            (x < 0 ==> result == negate_projective_niels(self.0[((-x) - 1) as int])),
            // Limb bounds for the result (derived from table bounds)
            fe51_limbs_bounded(&result.Y_plus_X, 54),
            fe51_limbs_bounded(&result.Y_minus_X, 54),
            fe51_limbs_bounded(&result.Z, 54),
            fe51_limbs_bounded(&result.T2d, 54),
            // The result is a valid ProjectiveNielsPoint
            is_valid_projective_niels_point(result),
    {
        proof {
            assume(false);
        }
        /* ORIGINAL CODE: for generic type T, $name, $size, $neg, $range, and $conv_range.

            debug_assert!(x >= $neg);
            debug_assert!(x as i16 <= $size as i16); // XXX We have to convert to i16s here for the radix-256 case.. this is wrong.

            // Compute xabs = |x|
                let xmask = x as i16 >> 7;
                let xabs = (x as i16 + xmask) ^ xmask;

                // Set t = 0 * P = identity
                let mut t = T::identity();
                for j in $range {
                    // Copy `points[j-1] == j*P` onto `t` in constant time if `|x| == j`.
                    let c = (xabs as u16).ct_eq(&(j as u16));
                    t.conditional_assign(&self.0[j - 1], c);
                }
                // Now t == |x| * P.

                let neg_mask = Choice::from((xmask & 1) as u8);
                t.conditional_negate(neg_mask);
                // Now t == x * P.

                t
        In our instantiation we have T = ProjectiveNielsPoint, $name = LookupTable, $size = 8, $neg = -8, $range = 1..9, and $conv_range = 0..7.
         */
        #[cfg(not(verus_keep_ghost))]
        {
            debug_assert!(x >= -8);
            debug_assert!(x <= 8);
        }

        // Compute xabs = |x|
        let xmask = x as i16 >> 7;
        let xabs = (x as i16 + xmask) ^ xmask;

        // Set t = 0 * P = identity
        let mut t = ProjectiveNielsPoint::identity();
        for j in 1..9 {
            // Copy `points[j-1] == j*P` onto `t` in constant time if `|x| == j`.
            /* ORIGINAL CODE: let c = (xabs as u16).ct_eq(&(j as u16)); */
            let c = ct_eq_u16(&(xabs as u16), &(j as u16));
            /* ORIGINAL CODE: t.conditional_assign(&self.0[j - 1], c); */
            conditional_assign_generic(&mut t, &self.0[j - 1], c);
        }
        // Now t == |x| * P.

        let neg_mask = Choice::from((xmask & 1) as u8);
        /* ORIGINAL CODE: t.conditional_negate(neg_mask); */
        conditional_negate_generic(&mut t, neg_mask);
        // Now t == x * P.

        t
    }
}

// Manual Clone implementation to avoid array clone issues in Verus
impl<T: Copy> Clone for LookupTable<T> {
    #[verifier::external_body]
    fn clone(&self) -> Self {
        *self
    }
}

// Specialized Default implementation for AffineNielsPoint
impl Default for LookupTable<AffineNielsPoint> {
    fn default() -> (result: LookupTable<AffineNielsPoint>)
        ensures
    // All table entries are set to the identity point

            forall|i: int|
                0 <= i < 8 ==> result.0[i] == crate::specs::edwards_specs::identity_affine_niels(),
    {
        LookupTable([AffineNielsPoint::default();8])
    }
}

// Specialized Default implementation for ProjectiveNielsPoint
impl Default for LookupTable<ProjectiveNielsPoint> {
    fn default() -> (result: LookupTable<ProjectiveNielsPoint>)
        ensures
    // All table entries are set to the identity point

            forall|i: int|
                0 <= i < 8 ==> result.0[i]
                    == crate::specs::edwards_specs::identity_projective_niels(),
    {
        LookupTable([ProjectiveNielsPoint::default();8])
    }
}

/* ORIGINAL CODE: generic default implementation
impl<T: Copy + Default> Default for $name<T> {
    fn default() -> $name<T> {
        $name([T::default(); 8])
    }
*/

impl<T: Debug> Debug for LookupTable<T> {
    #[verifier::external_body]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}(", stringify!(LookupTable))?;

        for x in self.0.iter() {
            write!(f, "{:?}", x)?;
        }

        write!(f, ")")
    }
}

impl<'a> From<&'a EdwardsPoint> for LookupTable<ProjectiveNielsPoint> {
    /// Create a lookup table from an EdwardsPoint
    /// Constructs [P, 2P, 3P, ..., Size*P]
    fn from(P: &'a EdwardsPoint) -> (result: Self)
        ensures
            is_valid_lookup_table_projective(result.0, *P, 8 as nat),
            lookup_table_projective_limbs_bounded(result.0),
    {
        /* ORIGINAL CODE: for generic $name, $size, and conv_range.

         let mut points = [P.as_projective_niels(); $size];
                for j in $conv_range {
                    points[j + 1] = (P + &points[j]).as_extended().as_projective_niels();
                }
                $name(points)

        In our instantiation we have $name = LookupTable, $size = 8, and conv_range = 0..7.
        */
        proof {
            use_type_invariant(P);
            lemma_unfold_edwards(*P);
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&P.Y, &P.X, 52);
        }

        let mut points = [P.as_projective_niels();8];
        for j in 0..7 {
            // ORIGINAL CODE: points[j + 1] = (P + &points[j]).as_extended().as_projective_niels();
            // Variable assignment refactor: split into sum, extended to prove type invariant
            // properties at each intermediate step.
            proof {
                use_type_invariant(P);
                lemma_unfold_edwards(*P);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&P.Y, &P.X, 52);
                assume(fe51_limbs_bounded(&&points[j as int].Y_plus_X, 54));
                assume(fe51_limbs_bounded(&&points[j as int].Y_minus_X, 54));
                assume(fe51_limbs_bounded(&&points[j as int].Z, 54));
                assume(fe51_limbs_bounded(&&points[j as int].T2d, 54));
                assume(is_valid_projective_niels_point(points[j as int]));
            }
            let sum = P + &points[j];
            proof {
                assume(fe51_limbs_bounded(&sum.X, 54));
                assume(fe51_limbs_bounded(&sum.Y, 54));
                assume(fe51_limbs_bounded(&sum.Z, 54));
                assume(fe51_limbs_bounded(&sum.T, 54));
            }
            let extended = sum.as_extended();
            proof {
                use_type_invariant(extended);
                lemma_unfold_edwards(extended);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&extended.Y, &extended.X, 52);
            }
            points[j + 1] = extended.as_projective_niels();
        }
        let result = LookupTable(points);
        proof {
            assume(is_valid_lookup_table_projective(result.0, *P, 8 as nat));
            assume(lookup_table_projective_limbs_bounded(result.0));
        }
        result
    }
}

impl<'a> From<&'a EdwardsPoint> for LookupTable<AffineNielsPoint> {
    /// Create a lookup table from an EdwardsPoint (affine version)
    /// Constructs [P, 2P, 3P, ..., Size*P]
    fn from(P: &'a EdwardsPoint) -> (result: Self)
        ensures
            is_valid_lookup_table_affine(result.0, *P, 8 as nat),
            lookup_table_affine_limbs_bounded(result.0),
            forall|j: int| 0 <= j < 8 ==> is_valid_affine_niels_point(#[trigger] result.0[j]),
    {
        /* ORIGINAL CODE: for generic $name, $size, and conv_range.

         let mut points = [P.as_affine_niels(); $size];
                // XXX batch inversion would be good if perf mattered here
                for j in $conv_range {
                    points[j + 1] = (P + &points[j]).as_extended().as_affine_niels()
                }
                $name(points)

        In our instantiation we have $name = LookupTable, $size = 8, and conv_range = 0..7.
        */
        proof {
            use_type_invariant(P);
            lemma_unfold_edwards(*P);
        }

        let mut points = [P.as_affine_niels();8];
        for j in 0..7 {
            // ORIGINAL CODE: points[j + 1] = (P + &points[j]).as_extended().as_affine_niels();
            // Variable assignment refactor: split into sum, extended to prove type invariant
            // properties at each intermediate step.
            proof {
                use_type_invariant(P);
                lemma_unfold_edwards(*P);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&P.Z, &P.Z, 52);
                assume(fe51_limbs_bounded(&&points[j as int].y_plus_x, 54));
                assume(fe51_limbs_bounded(&&points[j as int].y_minus_x, 54));
                assume(fe51_limbs_bounded(&&points[j as int].xy2d, 54));
                assume(is_valid_affine_niels_point(points[j as int]));
            }
            let sum = P + &points[j];
            proof {
                assume(fe51_limbs_bounded(&sum.X, 54));
                assume(fe51_limbs_bounded(&sum.Y, 54));
                assume(fe51_limbs_bounded(&sum.Z, 54));
                assume(fe51_limbs_bounded(&sum.T, 54));
            }
            let extended = sum.as_extended();
            proof {
                use_type_invariant(extended);
                lemma_unfold_edwards(extended);
            }
            points[j + 1] = extended.as_affine_niels()
        }
        let result = LookupTable(points);
        proof {
            assume(is_valid_lookup_table_affine(result.0, *P, 8 as nat));
            assume(lookup_table_affine_limbs_bounded(result.0));
            // Per-entry validity: each entry was produced by as_affine_niels on a valid
            // EdwardsPoint, which ensures is_valid_affine_niels_point. This surfaces the
            // existing assumes at lines 398/408 (inside the loop) as a postcondition.
            assume(forall|j: int|
                0 <= j < 8 ==> is_valid_affine_niels_point(#[trigger] result.0[j]));
        }
        result
    }
}

} // verus!
#[cfg(feature = "zeroize")]
impl<T> Zeroize for LookupTable<T>
where
    T: Copy + Default + Zeroize,
{
    fn zeroize(&mut self) {
        self.0.iter_mut().zeroize();
    }
}

cfg_if! {
    if #[cfg(feature = "precomputed-tables")] {
        // For homogeneity with other radix sizes, alias to "LookupTableRadix16".
        pub(crate) type LookupTableRadix16<T> = LookupTable<T>;
    }
}

verus! {

/// Holds odd multiples 1A, 3A, ..., 15A of a point A.
/* VERIFICATION NOTE:
   - Changed from pub(crate) to pub to allow Verus verification
     of requires/ensures clauses that reference self.0.
   - Removed Clone from #[derive(Copy, Clone)] because Verus does not support
     autoderive Clone for arrays. Manual Clone impl provided outside verus! macro.

   ORIGINAL CODE:
   #[derive(Copy, Clone)]
   pub(crate) struct NafLookupTable5<T>(pub(crate) [T; 8]);
*/
#[derive(Copy)]
pub struct NafLookupTable5<T>(pub [T; 8]);

/* VERIFICATION NOTE: Replaced generic NafLookupTable5<T>::select with concrete implementations
   to allow type-specific specs.

   ORIGINAL CODE:
   impl<T: Copy> NafLookupTable5<T> {
       pub fn select(&self, x: usize) -> T {
           debug_assert_eq!(x & 1, 1);
           debug_assert!(x < 16);
           self.0[x / 2]
       }
   }
*/

/// Concrete select implementation for NafLookupTable5<ProjectiveNielsPoint>
impl NafLookupTable5<ProjectiveNielsPoint> {
    /// Given public, odd \\( x \\) with \\( 0 < x < 2^4 \\), return \\(xA\\).
    /// Table stores [1A, 3A, 5A, 7A, 9A, 11A, 13A, 15A], so table[x/2] = x*A.
    pub fn select(&self, x: usize) -> (result: ProjectiveNielsPoint)
        requires
            x & 1 == 1,  // x is odd
            x < 16,  // x in {1, 3, 5, 7, 9, 11, 13, 15}
            naf_lookup_table5_projective_limbs_bounded(self.0),
        ensures
            result == self.0[(x / 2) as int],
            fe51_limbs_bounded(&result.Y_plus_X, 54),
            fe51_limbs_bounded(&result.Y_minus_X, 54),
            fe51_limbs_bounded(&result.Z, 54),
            fe51_limbs_bounded(&result.T2d, 54),
            // The result is a valid ProjectiveNielsPoint
            is_valid_projective_niels_point(result),
    {
        #[cfg(not(verus_keep_ghost))]
        {
            debug_assert_eq!(x & 1, 1);
            debug_assert!(x < 16);
        }
        proof {
            assume(is_valid_projective_niels_point(self.0[(x / 2) as int]));
        }
        self.0[x / 2]
    }
}

/// Concrete select implementation for NafLookupTable5<AffineNielsPoint>
impl NafLookupTable5<AffineNielsPoint> {
    /// Given public, odd \\( x \\) with \\( 0 < x < 2^4 \\), return \\(xA\\).
    /// Table stores [1A, 3A, 5A, 7A, 9A, 11A, 13A, 15A], so table[x/2] = x*A.
    pub fn select(&self, x: usize) -> (result: AffineNielsPoint)
        requires
            x & 1 == 1,  // x is odd
            x < 16,  // x in {1, 3, 5, 7, 9, 11, 13, 15}
            naf_lookup_table5_affine_limbs_bounded(self.0),
        ensures
            result == self.0[(x / 2) as int],
            fe51_limbs_bounded(&result.y_plus_x, 54),
            fe51_limbs_bounded(&result.y_minus_x, 54),
            fe51_limbs_bounded(&result.xy2d, 54),
    {
        #[cfg(not(verus_keep_ghost))]
        {
            debug_assert_eq!(x & 1, 1);
            debug_assert!(x < 16);
        }
        self.0[x / 2]
    }
}

} // verus!
// Manual Clone impl since derive(Clone) is not supported inside verus macro for arrays
impl<T: Copy> Clone for NafLookupTable5<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: Debug> Debug for NafLookupTable5<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "NafLookupTable5({:?})", self.0)
    }
}

verus! {

impl<'a> From<&'a EdwardsPoint> for NafLookupTable5<ProjectiveNielsPoint> {
    /// Create a NAF lookup table from an EdwardsPoint
    /// Constructs [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A] (odd multiples)
    fn from(A: &'a EdwardsPoint) -> (result: Self)
        ensures
            is_valid_naf_lookup_table5_projective(result.0, *A),
            naf_lookup_table5_projective_limbs_bounded(result.0),
    {
        proof {
            use_type_invariant(A);
            lemma_unfold_edwards(*A);
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&A.Y, &A.X, 52);
        }

        let mut Ai = [A.as_projective_niels();8];
        let A2 = A.double();

        for i in 0..7 {
            // ORIGINAL CODE: Ai[i + 1] = (&A2 + &Ai[i]).as_extended().as_projective_niels();
            // Variable assignment refactor: split into sum, extended to prove type invariant
            // properties at each intermediate step.
            proof {
                use_type_invariant(A2);
                lemma_unfold_edwards(A2);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&A2.Y, &A2.X, 52);
                assume(fe51_limbs_bounded(&&Ai[i as int].Y_plus_X, 54));
                assume(fe51_limbs_bounded(&&Ai[i as int].Y_minus_X, 54));
                assume(fe51_limbs_bounded(&&Ai[i as int].Z, 54));
                assume(fe51_limbs_bounded(&&Ai[i as int].T2d, 54));
                assume(is_valid_projective_niels_point(Ai[i as int]));
            }
            let sum = &A2 + &Ai[i];
            proof {
                assume(fe51_limbs_bounded(&sum.X, 54));
                assume(fe51_limbs_bounded(&sum.Y, 54));
                assume(fe51_limbs_bounded(&sum.Z, 54));
                assume(fe51_limbs_bounded(&sum.T, 54));
            }
            let extended = sum.as_extended();
            proof {
                use_type_invariant(extended);
                lemma_unfold_edwards(extended);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&extended.Y, &extended.X, 52);
            }
            Ai[i + 1] = extended.as_projective_niels();
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
        let result = NafLookupTable5(Ai);
        proof {
            assume(is_valid_naf_lookup_table5_projective(result.0, *A));
            assume(naf_lookup_table5_projective_limbs_bounded(result.0));
        }
        result
    }
}

impl<'a> From<&'a EdwardsPoint> for NafLookupTable5<AffineNielsPoint> {
    /// Create a NAF lookup table from an EdwardsPoint
    /// Constructs [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A] (odd multiples)
    fn from(A: &'a EdwardsPoint) -> (result: Self)
        ensures
            is_valid_naf_lookup_table5_affine(result.0, *A),
            naf_lookup_table5_affine_limbs_bounded(result.0),
    {
        proof {
            use_type_invariant(A);
            lemma_unfold_edwards(*A);
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&A.Y, &A.X, 52);
        }

        let mut Ai = [A.as_affine_niels();8];
        let A2 = A.double();

        for i in 0..7 {
            // ORIGINAL CODE: Ai[i + 1] = (&A2 + &Ai[i]).as_extended().as_affine_niels();
            // Variable assignment refactor: split into sum, extended to prove type invariant
            // properties at each intermediate step.
            proof {
                use_type_invariant(A2);
                lemma_unfold_edwards(A2);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&A2.Y, &A2.X, 52);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&A2.Z, &A2.Z, 52);
                assume(fe51_limbs_bounded(&&Ai[i as int].y_plus_x, 54));
                assume(fe51_limbs_bounded(&&Ai[i as int].y_minus_x, 54));
                assume(fe51_limbs_bounded(&&Ai[i as int].xy2d, 54));
                assume(is_valid_affine_niels_point(Ai[i as int]));
            }
            let sum = &A2 + &Ai[i];
            proof {
                assume(fe51_limbs_bounded(&sum.X, 54));
                assume(fe51_limbs_bounded(&sum.Y, 54));
                assume(fe51_limbs_bounded(&sum.Z, 54));
                assume(fe51_limbs_bounded(&sum.T, 54));
            }
            let extended = sum.as_extended();
            proof {
                use_type_invariant(extended);
                lemma_unfold_edwards(extended);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&extended.Y, &extended.X, 52);
            }
            Ai[i + 1] = extended.as_affine_niels();
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
        let result = NafLookupTable5(Ai);
        proof {
            assume(is_valid_naf_lookup_table5_affine(result.0, *A));
            assume(naf_lookup_table5_affine_limbs_bounded(result.0));
        }
        result
    }
}

} // verus!
verus! {

/// Holds stuff up to 8. The only time we use tables this big is for precomputed basepoint tables
/// and multiscalar multiplication (which requires alloc).
/* VERIFICATION NOTE:
   - Changed from pub(crate) to pub to allow Verus verification
     of requires/ensures clauses that reference self.0.
   - Removed Clone from #[derive(Copy, Clone)] because Verus does not support
     autoderive Clone for arrays. Manual Clone impl provided outside verus! macro.

   ORIGINAL CODE:
   #[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
   #[derive(Copy, Clone)]
   pub(crate) struct NafLookupTable8<T>(pub(crate) [T; 64]);
*/
#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
#[derive(Copy)]
pub struct NafLookupTable8<T>(pub [T; 64]);

/* VERIFICATION NOTE: Replaced generic NafLookupTable8<T>::select with concrete implementations
   to allow type-specific specs.

   ORIGINAL CODE:
   impl<T: Copy> NafLookupTable8<T> {
       pub fn select(&self, x: usize) -> T {
           debug_assert_eq!(x & 1, 1);
           debug_assert!(x < 128);
           self.0[x / 2]
       }
   }
*/

/// Concrete select implementation for NafLookupTable8<ProjectiveNielsPoint>
#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl NafLookupTable8<ProjectiveNielsPoint> {
    /// Given public, odd \\( x \\) with \\( 0 < x < 2^7 \\), return \\(xA\\).
    /// Table stores [1A, 3A, 5A, ..., 127A], so table[x/2] = x*A.
    pub fn select(&self, x: usize) -> (result: ProjectiveNielsPoint)
        requires
            x & 1 == 1,  // x is odd
            x < 128,  // x in {1, 3, 5, ..., 127}
            naf_lookup_table8_projective_limbs_bounded(self.0),
        ensures
            result == self.0[(x / 2) as int],
            fe51_limbs_bounded(&result.Y_plus_X, 54),
            fe51_limbs_bounded(&result.Y_minus_X, 54),
            fe51_limbs_bounded(&result.Z, 54),
            fe51_limbs_bounded(&result.T2d, 54),
    {
        #[cfg(not(verus_keep_ghost))]
        {
            debug_assert_eq!(x & 1, 1);
            debug_assert!(x < 128);
        }
        self.0[x / 2]
    }
}

/// Concrete select implementation for NafLookupTable8<AffineNielsPoint>
#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl NafLookupTable8<AffineNielsPoint> {
    /// Given public, odd \\( x \\) with \\( 0 < x < 2^7 \\), return \\(xA\\).
    /// Table stores [1A, 3A, 5A, ..., 127A], so table[x/2] = x*A.
    pub fn select(&self, x: usize) -> (result: AffineNielsPoint)
        requires
            x & 1 == 1,  // x is odd
            x < 128,  // x in {1, 3, 5, ..., 127}
            naf_lookup_table8_affine_limbs_bounded(self.0),
        ensures
            result == self.0[(x / 2) as int],
            fe51_limbs_bounded(&result.y_plus_x, 54),
            fe51_limbs_bounded(&result.y_minus_x, 54),
            fe51_limbs_bounded(&result.xy2d, 54),
    {
        #[cfg(not(verus_keep_ghost))]
        {
            debug_assert_eq!(x & 1, 1);
            debug_assert!(x < 128);
        }
        self.0[x / 2]
    }
}

} // verus!
// Manual Clone impl since derive(Clone) is not supported inside verus macro for arrays
#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl<T: Copy> Clone for NafLookupTable8<T> {
    fn clone(&self) -> Self {
        *self
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

verus! {

#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl<'a> From<&'a EdwardsPoint> for NafLookupTable8<ProjectiveNielsPoint> {
    /// Create a NAF lookup table from an EdwardsPoint
    /// Constructs [A, 3A, 5A, 7A, ..., 127A] (odd multiples)
    fn from(A: &'a EdwardsPoint) -> (result: Self)
        ensures
            is_valid_naf_lookup_table8_projective(result.0, *A),
            naf_lookup_table8_projective_limbs_bounded(result.0),
    {
        proof {
            use_type_invariant(A);
            lemma_unfold_edwards(*A);
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&A.Y, &A.X, 52);
        }

        let mut Ai = [A.as_projective_niels();64];
        let A2 = A.double();

        for i in 0..63 {
            // ORIGINAL CODE: Ai[i + 1] = (&A2 + &Ai[i]).as_extended().as_projective_niels();
            // Variable assignment refactor: split into sum, extended to prove type invariant
            // properties at each intermediate step.
            proof {
                use_type_invariant(A2);
                lemma_unfold_edwards(A2);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&A2.Y, &A2.X, 52);
                assume(fe51_limbs_bounded(&&Ai[i as int].Y_plus_X, 54));
                assume(fe51_limbs_bounded(&&Ai[i as int].Y_minus_X, 54));
                assume(fe51_limbs_bounded(&&Ai[i as int].Z, 54));
                assume(fe51_limbs_bounded(&&Ai[i as int].T2d, 54));
                assume(is_valid_projective_niels_point(Ai[i as int]));
            }
            let sum = &A2 + &Ai[i];
            proof {
                assume(fe51_limbs_bounded(&sum.X, 54));
                assume(fe51_limbs_bounded(&sum.Y, 54));
                assume(fe51_limbs_bounded(&sum.Z, 54));
                assume(fe51_limbs_bounded(&sum.T, 54));
            }
            let extended = sum.as_extended();
            proof {
                use_type_invariant(extended);
                lemma_unfold_edwards(extended);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&extended.Y, &extended.X, 52);
            }
            Ai[i + 1] = extended.as_projective_niels();
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A, ..., 127A]
        let result = NafLookupTable8(Ai);
        proof {
            assume(is_valid_naf_lookup_table8_projective(result.0, *A));
            assume(naf_lookup_table8_projective_limbs_bounded(result.0));
        }
        result
    }
}

#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl<'a> From<&'a EdwardsPoint> for NafLookupTable8<AffineNielsPoint> {
    /// Create a NAF lookup table from an EdwardsPoint
    /// Constructs [A, 3A, 5A, 7A, ..., 127A] (odd multiples)
    fn from(A: &'a EdwardsPoint) -> (result: Self)
        ensures
            is_valid_naf_lookup_table8_affine(result.0, *A),
            naf_lookup_table8_affine_limbs_bounded(result.0),
    {
        proof {
            use_type_invariant(A);
            lemma_unfold_edwards(*A);
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&A.Y, &A.X, 52);
        }

        let mut Ai = [A.as_affine_niels();64];
        let A2 = A.double();

        for i in 0..63 {
            // ORIGINAL CODE: Ai[i + 1] = (&A2 + &Ai[i]).as_extended().as_affine_niels();
            // Variable assignment refactor: split into sum, extended to prove type invariant
            // properties at each intermediate step.
            proof {
                use_type_invariant(A2);
                lemma_unfold_edwards(A2);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&A2.Y, &A2.X, 52);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&A2.Z, &A2.Z, 52);
                assume(fe51_limbs_bounded(&&Ai[i as int].y_plus_x, 54));
                assume(fe51_limbs_bounded(&&Ai[i as int].y_minus_x, 54));
                assume(fe51_limbs_bounded(&&Ai[i as int].xy2d, 54));
                assume(is_valid_affine_niels_point(Ai[i as int]));
            }
            let sum = &A2 + &Ai[i];
            proof {
                assume(fe51_limbs_bounded(&sum.X, 54));
                assume(fe51_limbs_bounded(&sum.Y, 54));
                assume(fe51_limbs_bounded(&sum.Z, 54));
                assume(fe51_limbs_bounded(&sum.T, 54));
            }
            let extended = sum.as_extended();
            proof {
                use_type_invariant(extended);
                lemma_unfold_edwards(extended);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&extended.Y, &extended.X, 52);
            }
            Ai[i + 1] = extended.as_affine_niels();
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A, ..., 127A]
        let result = NafLookupTable8(Ai);
        proof {
            assume(is_valid_naf_lookup_table8_affine(result.0, *A));
            assume(naf_lookup_table8_affine_limbs_bounded(result.0));
        }
        result
    }
}

} // verus!
