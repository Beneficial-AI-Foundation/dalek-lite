//! Helper functions for use with Lizard
#![allow(non_snake_case)]

use subtle::Choice;
use subtle::ConstantTimeEq;

use super::lizard_constants;
use crate::constants;

use crate::field::FieldElement;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::backend::serial::u64::subtle_assumes::choice_is_true;
#[allow(unused_imports)]
use crate::backend::serial::u64::subtle_assumes::{
    choice_not, choice_or, conditional_assign_generic, conditional_negate_field_element,
    negate_field_element,
};

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::lemma_small_mod;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::lizard_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::ristretto_specs::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::add_lemmas::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::as_bytes_lemmas::lemma_ct_eq_iff_canonical_nat;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::batch_invert_lemmas::lemma_is_zero_iff_canonical_nat_zero;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::constants_lemmas::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::lemma_square_matches_field_square;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::sqrt_m1_lemmas::lemma_sqrt_m1_limbs_bounded;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::sqrt_ratio_lemmas::{
    lemma_canonical_nat_lt_p, lemma_invsqrt_unique, lemma_is_negative_bridge,
    lemma_sqrt_ratio_mutual_exclusion,
};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::lizard_lemmas::*;

verus! {

/// Represents a point (s,t) on the Jacobi quartic associated
/// to the Edwards curve.
#[derive(Copy, Clone)]
#[allow(missing_docs)]
pub struct JacobiPoint {
    pub S: FieldElement,
    pub T: FieldElement,
}

/// Exec-to-spec bridge for `elligator_inv`.
#[verifier::spinoff_prover]
proof fn lemma_elligator_inv_spec_anchor(
    gs: nat,
    gt: nat,
    ret_val: bool,
    out_nat: nat,
    s_is_zero: bool,
    t_equals_one: bool,
    sq_val: bool,
    a_nat: nat,
    s2_nat: nat,
    s4_nat: nat,
    a2_nat: nat,
    inv_sq_y_nat: nat,
    y_nat: nat,
    s_is_neg: bool,
    pms2_nat: nat,
    x_before_negate_nat: nat,
)
    requires
        gs < p(),
        gt < p(),
        inv_sq_y_nat < p(),
        y_nat < p(),
        s_is_zero == (gs == 0),
        t_equals_one == (gt == 1),
        // Branch 1
        (s_is_zero && t_equals_one) ==> (ret_val && out_nat == sqrt_id()),
        (s_is_zero && !t_equals_one) ==> (ret_val && out_nat == 0),
        // Decomposed exec intermediates (each mirrors one operation's ensures)
        a_nat == field_mul(field_add(gt, 1), dp1_over_dm1()),
        s2_nat == field_square(gs),
        s4_nat == field_square(s2_nat),
        a2_nat == field_square(a_nat),
        inv_sq_y_nat == field_mul(field_sub(s4_nat, a2_nat), sqrt_m1()),
        y_nat % 2 == 0,
        // Success: invsqrt found a square root
        sq_val ==> (is_sqrt_ratio(1, inv_sq_y_nat, y_nat) && inv_sq_y_nat != 0),
        (!s_is_zero && sq_val) ==> ret_val,
        (!s_is_zero && sq_val) ==> s_is_neg == is_negative(gs),
        (!s_is_zero && sq_val) ==> pms2_nat == (if s_is_neg {
            field_neg(s2_nat)
        } else {
            s2_nat
        }),
        (!s_is_zero && sq_val) ==> x_before_negate_nat == field_mul(
            field_add(a_nat, pms2_nat),
            y_nat,
        ),
        (!s_is_zero && sq_val) ==> out_nat == field_abs(x_before_negate_nat),
        // Failure
        (!s_is_zero && !sq_val) ==> !ret_val,
        (!s_is_zero && !sq_val && inv_sq_y_nat != 0) ==> is_sqrt_ratio_times_i(
            1,
            inv_sq_y_nat,
            y_nat,
        ),
        (!s_is_zero && !sq_val && inv_sq_y_nat != 0) ==> !is_sqrt_ratio(1, inv_sq_y_nat, y_nat),
    ensures
        ret_val == spec_elligator_inv(gs, gt).0,
        ret_val ==> out_nat == spec_elligator_inv(gs, gt).1,
{
    reveal(spec_elligator_inv);
    lemma_small_mod(gs, p());
    lemma_small_mod(gt, p());
    lemma_small_mod(inv_sq_y_nat, p());
    lemma_small_mod(y_nat, p());
    if !s_is_zero && sq_val {
        lemma_invsqrt_unique(inv_sq_y_nat, y_nat);
    }
    if !s_is_zero && !sq_val && inv_sq_y_nat != 0 {
        lemma_invsqrt_unique(inv_sq_y_nat, y_nat);
    }
}

impl JacobiPoint {
    /// Elligator2 is defined in two steps: first a field element is converted
    /// to a point (s,t) on the Jacobi quartic associated to the Edwards curve.
    /// Then this point is mapped to a point on the Edwards curve.
    /// This function computes a field element that is mapped to a given (s,t)
    /// with Elligator2 if it exists.
    pub(crate) fn elligator_inv(&self) -> (result: (Choice, FieldElement))
        requires
            fe51_limbs_bounded(&self.S, 52),
            fe51_limbs_bounded(&self.T, 52),
        ensures
            fe51_limbs_bounded(&result.1, 52),
            // Spec anchor: the success flag matches spec_elligator_inv
            crate::backend::serial::u64::subtle_assumes::choice_is_true(result.0)
                == spec_elligator_inv(
                fe51_as_canonical_nat(&self.S),
                fe51_as_canonical_nat(&self.T),
            ).0,
            // When successful, the output value matches spec_elligator_inv
            crate::backend::serial::u64::subtle_assumes::choice_is_true(result.0)
                ==> fe51_as_canonical_nat(&result.1) == spec_elligator_inv(
                fe51_as_canonical_nat(&self.S),
                fe51_as_canonical_nat(&self.T),
            ).1,
    {
        proof {
            lemma_fe51_limbs_bounded_weaken(&self.S, 52, 54);
            lemma_fe51_limbs_bounded_weaken(&self.T, 52, 54);
            lemma_one_limbs_bounded_51();
            lemma_fe51_limbs_bounded_weaken(&FieldElement::ONE, 51, 52);
            lemma_zero_limbs_bounded();
            lemma_sqrt_id_limbs_bounded_52();
            lemma_dp1_over_dm1_limbs_bounded_51();
            lemma_fe51_limbs_bounded_weaken(&lizard_constants::DP1_OVER_DM1, 51, 54);
            lemma_sqrt_m1_limbs_bounded();
            lemma_fe51_limbs_bounded_weaken(&constants::SQRT_M1, 51, 54);
        }
        let mut out = FieldElement::ZERO;

        // Special case: s = 0.  If s is zero, either t = 1 or t = -1.
        // If t=1, then sqrt(i*d) is the preimage.  Otherwise it's 0.
        let s_is_zero = self.S.is_zero();
        let t_equals_one = self.T.ct_eq(&FieldElement::ONE);
        let ghost pre_out_1 = out;
        /* ORIGINAL CODE: out.conditional_assign(&lizard_constants::SQRT_ID, t_equals_one); */
        conditional_assign_generic(&mut out, &lizard_constants::SQRT_ID, t_equals_one);
        proof {
            if choice_is_true(t_equals_one) {
                assert(out == lizard_constants::SQRT_ID);
            } else {
                assert(out == pre_out_1);
            }
        }
        let mut ret = s_is_zero;
        let mut done = s_is_zero;

        // a := (t+1) (d+1)/(d-1)
        /* ORIGINAL CODE: let a = &(&self.T + &FieldElement::ONE) * &lizard_constants::DP1_OVER_DM1; */
        proof {
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&self.T, &FieldElement::ONE, 52);
        }
        let t_plus_1 = &self.T + &FieldElement::ONE;
        proof {
            lemma_fe51_limbs_bounded_weaken(&t_plus_1, 53, 54);
        }
        let a = &t_plus_1 * &lizard_constants::DP1_OVER_DM1;
        let a2 = a.square();

        // y := 1/sqrt(i (s^4 - a^2)).
        let s2 = self.S.square();
        let s4 = s2.square();
        let invSqY = &(&s4 - &a2) * &constants::SQRT_M1;

        // There is no preimage if the square root of i*(s^4-a^2) does not exist.
        let (sq, y) = invSqY.invsqrt();
        /* ORIGINAL CODE: ret |= sq; done |= !sq; */
        ret = choice_or(ret, sq);
        done = choice_or(done, choice_not(sq));

        // x := (a + sign(s)*s^2) y
        let mut pms2 = s2;
        /* ORIGINAL CODE: pms2.conditional_negate(self.S.is_negative()); */
        let s_is_neg = self.S.is_negative();
        conditional_negate_field_element(&mut pms2, s_is_neg);
        proof {
            if !choice_is_true(s_is_neg) {
                assert(pms2 == s2);
            }
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&a, &pms2, 52);
        }
        /* ORIGINAL CODE: let mut x = &(&a + &pms2) * &y; */
        let a_plus_pms2 = &a + &pms2;
        proof {
            lemma_fe51_limbs_bounded_weaken(&a_plus_pms2, 53, 54);
            lemma_fe51_limbs_bounded_weaken(&y, 52, 54);
        }
        let mut x = &a_plus_pms2 * &y;
        let x_is_negative = x.is_negative();
        let ghost x_before_negate = x;
        /* ORIGINAL CODE: x.conditional_negate(x_is_negative); */
        conditional_negate_field_element(&mut x, x_is_negative);
        let ghost pre_out_2 = out;
        let not_done = choice_not(done);
        /* ORIGINAL CODE: out.conditional_assign(&x, !done); */
        conditional_assign_generic(&mut out, &x, not_done);
        proof {
            if choice_is_true(not_done) {
                assert(out == x);
            } else {
                assert(out == pre_out_2);
            }

            let gs = fe51_as_canonical_nat(&self.S);
            let gt = fe51_as_canonical_nat(&self.T);

            // Bridge predicates
            lemma_is_zero_iff_canonical_nat_zero(self.S);
            lemma_ct_eq_iff_canonical_nat(&self.T, &FieldElement::ONE);
            lemma_one_field_element_value();
            lemma_canonical_nat_lt_p(&self.S);
            lemma_canonical_nat_lt_p(&self.T);
            lemma_canonical_nat_lt_p(&invSqY);
            lemma_canonical_nat_lt_p(&y);

            if gs == 0 && gt != 1 {
                lemma_zero_field_element_value();
            }
            if gs != 0 && choice_is_true(sq) {
                lemma_is_negative_bridge(&self.S, gs);
                lemma_is_negative_bridge(&x_before_negate, fe51_as_canonical_nat(&x_before_negate));
            }
            if gs != 0 && !choice_is_true(sq) {
                lemma_zero_field_element_value();
                if fe51_as_canonical_nat(&invSqY) != 0 {
                    lemma_small_mod(fe51_as_canonical_nat(&invSqY), p());
                    lemma_small_mod(1nat, p());
                    lemma_sqrt_ratio_mutual_exclusion(
                        1,
                        fe51_as_canonical_nat(&invSqY),
                        fe51_as_canonical_nat(&y),
                    );
                }
            }
            // Bridge square() to field_square

            assert(fe51_as_canonical_nat(&s2) == field_square(gs)) by {
                lemma_square_matches_field_square(fe51_as_nat(&self.S), fe51_as_nat(&s2));
            };
            assert(fe51_as_canonical_nat(&s4) == field_square(fe51_as_canonical_nat(&s2))) by {
                lemma_square_matches_field_square(fe51_as_nat(&s2), fe51_as_nat(&s4));
            };
            assert(fe51_as_canonical_nat(&a2) == field_square(fe51_as_canonical_nat(&a))) by {
                lemma_square_matches_field_square(fe51_as_nat(&a), fe51_as_nat(&a2));
            };
            assert(fe51_as_canonical_nat(&a) == field_mul(field_add(gt, 1), dp1_over_dm1()));

            lemma_elligator_inv_spec_anchor(
                gs,
                gt,
                choice_is_true(ret),
                fe51_as_canonical_nat(&out),
                choice_is_true(s_is_zero),
                choice_is_true(t_equals_one),
                choice_is_true(sq),
                fe51_as_canonical_nat(&a),
                fe51_as_canonical_nat(&s2),
                fe51_as_canonical_nat(&s4),
                fe51_as_canonical_nat(&a2),
                fe51_as_canonical_nat(&invSqY),
                fe51_as_canonical_nat(&y),
                choice_is_true(s_is_neg),
                fe51_as_canonical_nat(&pms2),
                fe51_as_canonical_nat(&x_before_negate),
            );
        }

        (ret, out)
    }

    /// Compute the dual of this Jacobi quartic point: (-S, -T).
    pub(crate) fn dual(&self) -> (result: JacobiPoint)
        requires
            fe51_limbs_bounded(&self.S, 54),
            fe51_limbs_bounded(&self.T, 54),
        ensures
            fe51_limbs_bounded(&result.S, 52),
            fe51_limbs_bounded(&result.T, 52),
            // result = (-S, -T)
            fe51_as_canonical_nat(&result.S) == field_neg(fe51_as_canonical_nat(&self.S)),
            fe51_as_canonical_nat(&result.T) == field_neg(fe51_as_canonical_nat(&self.T)),
    {
        /* ORIGINAL CODE: JacobiPoint { S: -(&self.S), T: -(&self.T) } */
        // Using negate_field_element wrapper to avoid Verus internal error
        JacobiPoint { S: negate_field_element(&self.S), T: negate_field_element(&self.T) }
    }
}

} // verus!
