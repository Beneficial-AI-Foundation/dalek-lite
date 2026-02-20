#![allow(non_snake_case)]

use crate::backend::serial::curve_models::ProjectiveNielsPoint;
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::Identity;
use crate::window::LookupTable;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::mul_base_lemmas::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::window_specs::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// Perform constant-time, variable-base scalar multiplication.
/// Computes scalar * point on the Ed25519 curve.
#[rustfmt::skip]  // keep alignment of explanatory comments
pub(crate) fn mul(point: &EdwardsPoint, scalar: &Scalar) -> (result: EdwardsPoint)
    requires
        scalar.bytes[31] <= 127,
        is_well_formed_edwards_point(*point),
    ensures
        is_well_formed_edwards_point(result),
        edwards_point_as_affine(result) == edwards_scalar_mul(
            edwards_point_as_affine(*point),
            scalar_as_nat(scalar),
        ),
{
    // Construct a lookup table of [P,2P,3P,4P,5P,6P,7P,8P]
    let lookup_table = LookupTable::<ProjectiveNielsPoint>::from(point);
    // Setting s = scalar, compute
    //
    //    s = s_0 + s_1*16^1 + ... + s_63*16^63,
    //
    // with `-8 ≤ s_i < 8` for `0 ≤ i < 63` and `-8 ≤ s_63 ≤ 8`.
    // This decomposition requires s < 2^255, which is guaranteed by Scalar invariant #1.
    let scalar_digits = scalar.as_radix_16();
    // Compute s*P as
    //
    //    s*P = P*(s_0 +   s_1*16^1 +   s_2*16^2 + ... +   s_63*16^63)
    //    s*P =  P*s_0 + P*s_1*16^1 + P*s_2*16^2 + ... + P*s_63*16^63
    //    s*P = P*s_0 + 16*(P*s_1 + 16*(P*s_2 + 16*( ... + P*s_63)...))
    //
    // We sum right-to-left.

    // Unwrap first loop iteration to save computing 16*identity
    let mut tmp2;
    let mut tmp3 = EdwardsPoint::identity();
    proof {
        assert(is_well_formed_edwards_point(tmp3));
        assert(radix_16_all_bounded(&scalar_digits));
        assert(radix_16_digit_bounded(scalar_digits[63]));
    }
    /* ORIGINAL CODE:
    let mut tmp1 = &tmp3 + &lookup_table.select(scalar_digits[63]);
    */
    let selected = lookup_table.select(scalar_digits[63]);
    proof {
        assert(is_valid_projective_niels_point(selected));
    }
    let mut tmp1 = &tmp3 + &selected;

    // Now tmp1 = s_63*P in P1xP1 coords
    // Prove initialization: invariant holds at j=0
    proof {
        let P_affine = edwards_point_as_affine(*point);

        // Identity has affine coords (0, 1)
        lemma_identity_affine_coords(tmp3);
        assert(edwards_point_as_affine(tmp3) == (0nat, 1nat));

        // Select gives signed scalar multiplication
        lemma_select_projective_is_signed_scalar_mul(
            lookup_table.0,
            scalar_digits[63],
            selected,
            *point,
        );
        let selected_affine = projective_niels_point_as_affine_edwards(selected);
        assert(selected_affine == edwards_scalar_mul_signed(P_affine, scalar_digits[63] as int));

        // P_affine coords are < p() (field_mul returns val % p)
        p_gt_2();
        assert(P_affine.0 < p()) by {
            lemma_mod_bound(
                (fe51_as_canonical_nat(&point.X) * field_inv(
                    fe51_as_canonical_nat(&point.Z),
                )) as int,
                p() as int,
            );
        }
        assert(P_affine.1 < p()) by {
            lemma_mod_bound(
                (fe51_as_canonical_nat(&point.Y) * field_inv(
                    fe51_as_canonical_nat(&point.Z),
                )) as int,
                p() as int,
            );
        }

        // Selected affine coords are canonical (< p)
        assert(selected_affine.0 < p() && selected_affine.1 < p()) by {
            lemma_edwards_scalar_mul_signed_canonical(P_affine, scalar_digits[63] as int);
        }

        // identity + selected = (selected.0 % p, selected.1 % p) = selected
        assert(completed_point_as_affine_edwards(tmp1) == selected_affine) by {
            lemma_edwards_add_identity_left(selected_affine.0, selected_affine.1);
            lemma_small_mod(selected_affine.0, p());
            lemma_small_mod(selected_affine.1, p());
        }

        // reconstruct_radix_2w for the 1-element subrange [s_63]
        let s = scalar_digits@.subrange(63int, 64int);
        assert(s.len() == 1);
        assert(s[0] == scalar_digits[63]);
        assert(s.skip(1).len() == 0);
        assert(reconstruct_radix_2w(s.skip(1), 4) == 0int);
        // reconstruct_radix_2w([s_63], 4) = s_63 + 16 * 0 = s_63
        lemma2_to64();
        assert(pow2(4) == 16);
    }

    /* ORIGINAL CODE:
    for i in (0..63).rev() {
    */
    for j in 0usize..63
        invariant
            radix_16_all_bounded(&scalar_digits),
            lookup_table_projective_limbs_bounded(lookup_table.0),
            is_valid_completed_point(tmp1),
            fe51_limbs_bounded(&tmp1.X, 54),
            fe51_limbs_bounded(&tmp1.Y, 54),
            fe51_limbs_bounded(&tmp1.Z, 54),
            fe51_limbs_bounded(&tmp1.T, 54),
            // Table validity (from LookupTable::from postcondition)
            is_valid_lookup_table_projective(lookup_table.0, *point, 8),
            // Radix-16 reconstruction equality (from as_radix_16 postcondition)
            reconstruct_radix_16(scalar_digits@) == scalar_as_nat(scalar) as int,
            // Functional correctness: Horner partial evaluation
            completed_point_as_affine_edwards(tmp1) == edwards_scalar_mul_signed(
                edwards_point_as_affine(*point),
                reconstruct_radix_2w(scalar_digits@.subrange(63 - j as int, 64), 4),
            ),
    {
        let i = 62 - j;  // i goes from 62 down to 0

        // Capture old affine for tracking through 4 doublings
        let ghost old_affine = completed_point_as_affine_edwards(tmp1);
        let ghost P_affine = edwards_point_as_affine(*point);
        let ghost partial_j = reconstruct_radix_2w(scalar_digits@.subrange(63 - j as int, 64), 4);

        // 4 doublings: multiply the accumulator by 16
        tmp2 = tmp1.as_projective();  // tmp2 =    (prev) in P2 coords
        tmp1 = tmp2.double();  // tmp1 =  2*(prev) in P1xP1 coords
        let ghost a1 = completed_point_as_affine_edwards(tmp1);

        tmp2 = tmp1.as_projective();  // tmp2 =  2*(prev) in P2 coords
        tmp1 = tmp2.double();  // tmp1 =  4*(prev) in P1xP1 coords
        let ghost a2 = completed_point_as_affine_edwards(tmp1);

        tmp2 = tmp1.as_projective();  // tmp2 =  4*(prev) in P2 coords
        tmp1 = tmp2.double();  // tmp1 =  8*(prev) in P1xP1 coords
        let ghost a3 = completed_point_as_affine_edwards(tmp1);

        tmp2 = tmp1.as_projective();  // tmp2 =  8*(prev) in P2 coords
        tmp1 = tmp2.double();  // tmp1 = 16*(prev) in P1xP1 coords
        let ghost a4 = completed_point_as_affine_edwards(tmp1);

        tmp3 = tmp1.as_extended();  // tmp3 = 16*(prev) in P3 coords

        /* ORIGINAL CODE:
        tmp1 = &tmp3 + &lookup_table.select(scalar_digits[i]);
        */
        proof {
            assert(radix_16_digit_bounded(scalar_digits[i as int]));
        }
        let selected = lookup_table.select(scalar_digits[i]);
        proof {
            assert(is_valid_projective_niels_point(selected));
        }
        tmp1 = &tmp3 + &selected;
        // Now tmp1 = s_i*P + 16*(prev) in P1xP1 coords

        proof {
            // -- Step 1: 4 doublings = multiplication by 16 --
            assert(a1 == edwards_double(old_affine.0, old_affine.1));
            assert(a2 == edwards_double(a1.0, a1.1));
            assert(a3 == edwards_double(a2.0, a2.1));
            assert(a4 == edwards_double(a3.0, a3.1));
            lemma_four_doublings_is_mul_16(old_affine, a1, a2, a3, a4);
            lemma2_to64();

            // as_extended preserves affine
            assert(edwards_point_as_affine(tmp3) == a4);

            // -- Step 2: Composition: [16]([partial]*P) = [partial*16]*P --
            assert(old_affine == edwards_scalar_mul_signed(P_affine, partial_j));
            lemma_edwards_scalar_mul_signed_composition(P_affine, partial_j, 16);
            assert(a4 == edwards_scalar_mul_signed(P_affine, partial_j * 16));

            // -- Step 3: Select gives signed scalar mul --
            lemma_select_projective_is_signed_scalar_mul(
                lookup_table.0,
                scalar_digits[i as int],
                selected,
                *point,
            );
            let selected_affine = projective_niels_point_as_affine_edwards(selected);
            assert(selected_affine == edwards_scalar_mul_signed(
                P_affine,
                scalar_digits[i as int] as int,
            ));

            // -- Step 4: Add combines the two terms --
            // completed_point_as_affine_edwards(tmp1) ==
            //   edwards_add(a4, selected_affine) ==
            //   edwards_add([partial*16]*P, [s_i]*P) ==
            //   [partial*16 + s_i]*P
            axiom_edwards_scalar_mul_signed_additive(
                P_affine,
                partial_j * 16,
                scalar_digits[i as int] as int,
            );

            // -- Step 5: Connect to reconstruct_radix_2w recurrence --
            let i_int = i as int;
            let s = scalar_digits@.subrange(i_int, 64);
            assert(s.len() > 0);
            assert(s[0] == scalar_digits@[i_int]);
            assert(s.skip(1) =~= scalar_digits@.subrange(i_int + 1, 64));
            // Unfold reconstruct_radix_2w one step
            assert(reconstruct_radix_2w(s, 4) == (scalar_digits@[i_int] as int) + pow2(4)
                * reconstruct_radix_2w(scalar_digits@.subrange(i_int + 1, 64), 4));
            assert(pow2(4) == 16);
            // i_int + 1 == 63 - j, so subrange(i_int+1, 64) == subrange(63-j, 64)
            assert(i_int + 1 == 63 - j as int);
            // The new partial = s[i] + 16 * partial_j = partial_j * 16 + s[i]
            assert(reconstruct_radix_2w(s, 4) == partial_j * 16 + scalar_digits[i as int] as int)
                by {
                assert((scalar_digits@[i_int] as int) + 16 * partial_j == partial_j * 16 + (
                scalar_digits@[i_int] as int)) by {
                    lemma_mul_is_commutative(16, partial_j as int);
                }
            }
            // s == scalar_digits@.subrange(63 - (j+1), 64)
            assert(63 - (j + 1) as int == i_int);
        }
    }

    // Post-loop: connect to edwards_scalar_mul(P, scalar_as_nat(scalar))
    let result = tmp1.as_extended();
    proof {
        let P_affine = edwards_point_as_affine(*point);

        // After loop (j=63): invariant gives us the full reconstruction
        assert(scalar_digits@.subrange(0int, 64int) =~= scalar_digits@);
        assert(reconstruct_radix_2w(scalar_digits@, 4) == reconstruct_radix_16(scalar_digits@));
        assert(reconstruct_radix_16(scalar_digits@) == scalar_as_nat(scalar) as int);

        // Since scalar_as_nat >= 0, signed == unsigned
        assert(scalar_as_nat(scalar) as int >= 0);
        reveal(edwards_scalar_mul_signed);
        assert(edwards_scalar_mul_signed(P_affine, scalar_as_nat(scalar) as int)
            == edwards_scalar_mul(P_affine, scalar_as_nat(scalar)));

        // as_extended preserves affine
        assert(edwards_point_as_affine(result) == completed_point_as_affine_edwards(tmp1));
    }
    result
}

} // verus!
