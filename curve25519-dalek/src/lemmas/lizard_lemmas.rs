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
use crate::specs::lizard_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::ristretto_specs::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::sqrt_m1_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::number_theory_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
pub use crate::lemmas::common_lemmas::bit_lemmas::{
    lemma_mask_bound_implies_bit_clean, lemma_mask_or_bound, lemma_or_bit, lemma_or_bit_all,
    mask_bit,
};

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::core_specs::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::primality_specs::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
pub use crate::lemmas::edwards_lemmas::torsion_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
pub use crate::lemmas::ristretto_lemmas::coset_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::sqrt_ratio_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::from_bytes_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::as_bytes_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::core_assumes::axiom_sha256_output_length;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::core_assumes::{seq_to_array_32, spec_sha256};

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::to_nat_lemmas::*;

#[allow(unused_imports)]
use crate::field::FieldElement;
#[allow(unused_imports)]
use crate::lizard::lizard_constants;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// Lizard constant limb-bound lemmas
// =============================================================================
pub proof fn lemma_sqrt_id_limbs_bounded_52()
    ensures
        fe51_limbs_bounded(&lizard_constants::SQRT_ID, 52),
{
    assert(2298852427963285u64 < (1u64 << 52)) by (bit_vector);
    assert(3837146560810661u64 < (1u64 << 52)) by (bit_vector);
    assert(4413131899466403u64 < (1u64 << 52)) by (bit_vector);
    assert(3883177008057528u64 < (1u64 << 52)) by (bit_vector);
    assert(2352084440532925u64 < (1u64 << 52)) by (bit_vector);
}

pub proof fn lemma_dp1_over_dm1_limbs_bounded_51()
    ensures
        fe51_limbs_bounded(&lizard_constants::DP1_OVER_DM1, 51),
{
    assert(2159851467815724u64 < (1u64 << 51)) by (bit_vector);
    assert(1752228607624431u64 < (1u64 << 51)) by (bit_vector);
    assert(1825604053920671u64 < (1u64 << 51)) by (bit_vector);
    assert(1212587319275468u64 < (1u64 << 51)) by (bit_vector);
    assert(253422448836237u64 < (1u64 << 51)) by (bit_vector);
}

pub proof fn lemma_mdouble_invsqrt_a_minus_d_bounded_51()
    ensures
        fe51_limbs_bounded(&lizard_constants::MDOUBLE_INVSQRT_A_MINUS_D, 51),
{
    assert(1693982333959686u64 < (1u64 << 51)) by (bit_vector);
    assert(608509411481997u64 < (1u64 << 51)) by (bit_vector);
    assert(2235573344831311u64 < (1u64 << 51)) by (bit_vector);
    assert(947681270984193u64 < (1u64 << 51)) by (bit_vector);
    assert(266558006233600u64 < (1u64 << 51)) by (bit_vector);
}

pub proof fn lemma_minvsqrt_one_plus_d_bounded_51()
    ensures
        fe51_limbs_bounded(&lizard_constants::MINVSQRT_ONE_PLUS_D, 51),
{
    assert(321571956990465u64 < (1u64 << 51)) by (bit_vector);
    assert(1251814006996634u64 < (1u64 << 51)) by (bit_vector);
    assert(2226845496292387u64 < (1u64 << 51)) by (bit_vector);
    assert(189049560751797u64 < (1u64 << 51)) by (bit_vector);
    assert(2074948709371214u64 < (1u64 << 51)) by (bit_vector);
}

pub proof fn lemma_midouble_invsqrt_a_minus_d_bounded_51()
    ensures
        fe51_limbs_bounded(&lizard_constants::MIDOUBLE_INVSQRT_A_MINUS_D, 51),
{
    assert(1608655899704280u64 < (1u64 << 51)) by (bit_vector);
    assert(1999971613377227u64 < (1u64 << 51)) by (bit_vector);
    assert(49908634785720u64 < (1u64 << 51)) by (bit_vector);
    assert(1873700692181652u64 < (1u64 << 51)) by (bit_vector);
    assert(353702208628067u64 < (1u64 << 51)) by (bit_vector);
}

pub proof fn lemma_zero_limbs_bounded()
    ensures
        fe51_limbs_bounded(&FieldElement::ZERO, 52),
{
    assert(forall|i: int| 0 <= i < 5 ==> FieldElement::ZERO.limbs[i] == 0u64);
    assert(0u64 < (1u64 << 52)) by (bit_vector);
}

// =============================================================================
// Exec–spec bridge lemmas (moved from lizard_ristretto.rs for co-location
// with their axiom dependencies)
// =============================================================================
/// h = sha256(msg) with bytes 8..24 overwritten and bits cleared ⟹ h = spec_lizard_fe_bytes(msg).
#[verifier::spinoff_prover]
pub proof fn lemma_h_equals_spec_lizard_fe_bytes(h: [u8; 32], msg: Seq<u8>)
    requires
        msg.len() == 16,
        h[0int] == (spec_sha256(msg)[0int] & 254u8),
        forall|i: int| 1 <= i < 8 ==> h[i] == spec_sha256(msg)[i],
        forall|i: int| 0 <= i < 16 ==> h[(8 + i) as int] == msg[i],
        forall|i: int| 24 <= i < 31 ==> h[i] == spec_sha256(msg)[i],
        h[31int] == (spec_sha256(msg)[31int] & 63u8),
    ensures
        h == spec_lizard_fe_bytes(msg),
{
    axiom_sha256_output_length(msg);
}

/// buf2 = spec_lizard_fe_bytes(msg) ⟹ msg is a valid Lizard coset preimage.
#[verifier::spinoff_prover]
pub proof fn lemma_decode_candidate_preimage(
    fe_j: &FieldElement,
    buf2: &[u8; 32],
    msg_spec: Seq<u8>,
    coset: [(nat, nat); 4],
)
    requires
        msg_spec.len() == 16,
        as_bytes_post(fe_j, buf2),
        *buf2 == spec_lizard_fe_bytes(msg_spec),
        ({
            let ej = spec_elligator_ristretto_flavor(fe51_as_canonical_nat(fe_j));
            ej == coset[0] || ej == coset[1] || ej == coset[2] || ej == coset[3]
        }),
    ensures
        is_lizard_preimage_coset(msg_spec, coset),
{
    assert(is_lizard_preimage_coset(msg_spec, coset)) by {
        lemma_from_u8_32_as_nat(buf2);
        lemma_as_nat_32_mod_255(buf2);
        lemma_from_bytes_as_bytes_roundtrip(fe_j, buf2, &spec_fe51_from_bytes(buf2));
    };
}

/// Each JQ point maps to some coset member (disjunction over four indices).
///
/// Axiom dependencies:
/// - `axiom_jacobi_quartic_birational_pair01` (non-edge: JQ[0]→coset[0], JQ[1]→coset[2])
/// - `axiom_jacobi_quartic_torsion_pair23` (non-edge: JQ[2]→coset[1], JQ[3]→coset[3])
/// - `lemma_jacobi_quartic_edge_values` (edge: X=0 or Y=0 branch)
#[verifier::spinoff_prover]
pub proof fn lemma_coset_bridge(
    point: crate::edwards::EdwardsPoint,
    s0: nat,
    t0: nat,
    s1: nat,
    t1: nat,
    s2: nat,
    t2: nat,
    s3: nat,
    t3: nat,
)
    requires
        is_well_formed_edwards_point(point),
        spec_to_jacobi_quartic_ristretto(point) == [(s0, t0), (s1, t1), (s2, t2), (s3, t3)],
    ensures
        ({
            let (x, y) = edwards_point_as_affine(point);
            let coset = ristretto_coset_affine(x, y);
            ({
                let ji = jacobi_to_edwards_affine(s0, t0);
                ji == coset[0] || ji == coset[1] || ji == coset[2] || ji == coset[3]
            }) && ({
                let ji = jacobi_to_edwards_affine(s1, t1);
                ji == coset[0] || ji == coset[1] || ji == coset[2] || ji == coset[3]
            }) && ({
                let ji = jacobi_to_edwards_affine(s2, t2);
                ji == coset[0] || ji == coset[1] || ji == coset[2] || ji == coset[3]
            }) && ({
                let ji = jacobi_to_edwards_affine(s3, t3);
                ji == coset[0] || ji == coset[1] || ji == coset[2] || ji == coset[3]
            })
        }),
{
    axiom_jacobi_quartic_birational_pair01(point);
    axiom_jacobi_quartic_torsion_pair23(point);
    lemma_jacobi_quartic_edge_values(point);
}

/// gamma_nat = nat_invsqrt(gamma_arg_nat) from exec-level invsqrt postconditions.
#[verifier::spinoff_prover]
pub proof fn lemma_invsqrt_bridge(
    gamma_arg_nat: nat,
    gamma_nat: nat,
    gamma_sq_val: bool,
    one_canonical: nat,
)
    requires
        gamma_arg_nat < p(),
        gamma_nat < p(),
        gamma_nat % 2 == 0,
        one_canonical == 1,
        gamma_sq_val ==> is_sqrt_ratio(one_canonical, gamma_arg_nat, gamma_nat),
        (!gamma_sq_val && gamma_arg_nat != 0) ==> is_sqrt_ratio_times_i(
            one_canonical,
            gamma_arg_nat,
            gamma_nat,
        ),
        gamma_arg_nat == 0 ==> gamma_nat == 0,
    ensures
        gamma_nat == nat_invsqrt(gamma_arg_nat),
{
    if gamma_arg_nat % p() != 0 {
        assert(!is_negative(gamma_nat)) by {
            lemma_small_mod(gamma_nat, p());
        };
        if gamma_sq_val {
            assert(is_sqrt_ratio(1, gamma_arg_nat, gamma_nat));
        } else {
            assert(gamma_arg_nat != 0) by {
                lemma_small_mod(gamma_arg_nat, p());
            };
            assert(is_sqrt_ratio_times_i(1, gamma_arg_nat, gamma_nat));
        }
        lemma_invsqrt_unique(gamma_arg_nat, gamma_nat);
    } else {
        assert(gamma_arg_nat == 0) by {
            lemma_small_mod(gamma_arg_nat, p());
        };
    }
}

// =============================================================================
// spec_lizard_fe_bytes injectivity (fully proved)
// =============================================================================
/// `spec_lizard_fe_bytes` is injective on 16-byte messages: bytes 8..23 of
/// the output carry the message payload verbatim (the Seq::new closure
/// sets `s[i] = data[i−8]` for `8 ≤ i < 24`, and the updates at
/// indices 0 and 31 leave that range untouched).
///
/// This removes the "SHA-256 structural consistency" trust assumption
/// from the old monolithic decode exhaustive axiom: injectivity
/// follows from the definition of `spec_lizard_fe_bytes`, not from any
/// hash collision-resistance property.  (The proof does use
/// `axiom_sha256_output_length` to establish that the SHA-256 output
/// is 32 bytes, which is needed for the index arithmetic.)
#[verifier::spinoff_prover]
pub proof fn lemma_spec_lizard_fe_bytes_injective(m1: Seq<u8>, m2: Seq<u8>)
    requires
        m1.len() == 16,
        m2.len() == 16,
        spec_lizard_fe_bytes(m1) == spec_lizard_fe_bytes(m2),
    ensures
        m1 =~= m2,
{
    axiom_sha256_output_length(m1);
    axiom_sha256_output_length(m2);
}

// =============================================================================
// Coset membership predicate (opaque to prevent quantifier explosion in loops)
// =============================================================================
/// Opaque predicate: the Elligator forward map of `fe_val` lands on some coset member.
/// Kept opaque in loop invariants to avoid quantifier explosion from
/// `spec_elligator_ristretto_flavor` expansion.
#[verifier::opaque]
pub open spec fn is_slot_in_coset(fe_val: nat, coset: [(nat, nat); 4]) -> bool {
    let ej = spec_elligator_ristretto_flavor(fe_val);
    ej == coset[0] || ej == coset[1] || ej == coset[2] || ej == coset[3]
}

/// Prove that an even slot maps to the coset (scoped reveal + axiom).
pub proof fn lemma_even_is_slot_in_coset(fe_val: nat, s: nat, t: nat, coset: [(nat, nat); 4])
    requires
        spec_elligator_inv(s, t).0,
        spec_elligator_inv(s, t).1 == fe_val,
        ({
            let ji = jacobi_to_edwards_affine(s, t);
            ji == coset[0] || ji == coset[1] || ji == coset[2] || ji == coset[3]
        }),
    ensures
        is_slot_in_coset(fe_val, coset),
{
    reveal(is_slot_in_coset);
    assert(spec_elligator_ristretto_flavor(fe_val) == jacobi_to_edwards_affine(s, t)) by {
        lemma_elligator_inv_algebraic(s, t);
    };
}

/// Prove that an odd (dual) slot maps to the coset (scoped reveal + axiom).
pub proof fn lemma_odd_is_slot_in_coset(
    fe_val: nat,
    ns: nat,
    nt: nat,
    s: nat,
    t: nat,
    coset: [(nat, nat); 4],
)
    requires
        spec_elligator_inv(ns, nt).0,
        spec_elligator_inv(ns, nt).1 == fe_val,
        ns == field_neg(s),
        nt == field_neg(t),
        ({
            let ji = jacobi_to_edwards_affine(s, t);
            ji == coset[0] || ji == coset[1] || ji == coset[2] || ji == coset[3]
        }),
    ensures
        is_slot_in_coset(fe_val, coset),
{
    reveal(is_slot_in_coset);
    assert(spec_elligator_ristretto_flavor(fe_val) == jacobi_to_edwards_affine(ns, nt)) by {
        lemma_elligator_inv_algebraic(ns, nt);
    };
    lemma_jacobi_dual_same_edwards(s, t);
}

/// (−s, −t) and (s, t) map to the same Edwards affine point.
///
/// y depends only on s²; (−s)² = s², so y is unchanged.
/// x = 2s/(t·c); with s→−s, t→−t the negations cancel.
pub proof fn lemma_jacobi_dual_same_edwards(s: nat, t: nat)
    ensures
        jacobi_to_edwards_affine(field_neg(s), field_neg(t)) == jacobi_to_edwards_affine(s, t),
{
    let ns = field_neg(s);
    let nt = field_neg(t);
    let c = spec_sqrt_ad_minus_one();
    let two_s = field_mul(2, s);
    let tc = field_mul(t, c);

    // (−s)² = s²
    assert(field_square(ns) == field_square(s)) by {
        lemma_neg_square_eq(s);
        lemma_square_mod_noop(s);
    };

    // 2·(−s) = −(2·s)
    assert(field_mul(2, ns) == field_neg(two_s)) by {
        lemma_field_mul_neg(2, s);
    };

    // (−t)·c = −(t·c)
    assert(field_mul(nt, c) == field_neg(tc)) by {
        lemma_field_neg_mul_left(t, c);
    };

    // inv(−(t·c)) = −inv(t·c)
    assert(field_inv(field_mul(nt, c)) == field_neg(field_inv(tc))) by {
        lemma_field_inv_neg(tc);
    };

    // (−a)·(−b) = −(a·(−b)) = −(−(a·b)) = a·b
    assert(field_mul(field_neg(two_s), field_neg(field_inv(tc))) == field_neg(
        field_mul(two_s, field_neg(field_inv(tc))),
    )) by {
        lemma_field_neg_mul_left(two_s, field_neg(field_inv(tc)));
    };
    assert(field_mul(two_s, field_neg(field_inv(tc))) == field_neg(field_mul(two_s, field_inv(tc))))
        by {
        lemma_field_mul_neg(two_s, field_inv(tc));
    };
    assert(field_neg(field_neg(field_mul(two_s, field_inv(tc)))) == field_mul(two_s, field_inv(tc))
        % p()) by {
        lemma_field_neg_neg(field_mul(two_s, field_inv(tc)));
    };
    assert(field_mul(two_s, field_inv(tc)) < p()) by {
        p_gt_2();
        lemma_mod_bound((two_s * field_inv(tc)) as int, p() as int);
    };
    lemma_small_mod(field_mul(two_s, field_inv(tc)), p());

    // Both coordinates match, so the affine points are equal.
    assert(jacobi_to_edwards_affine(ns, nt) == jacobi_to_edwards_affine(s, t));
}

/// Constant identity: mc · √(ad−1) = 2·√(−1)  in F_p  (p = 2²⁵⁵ − 19).
///
/// where:
///   mc       = `midouble_invsqrt_a_minus_d()`
///   √(ad−1)  = √(−d−1)      (`spec_sqrt_ad_minus_one()`,  a = −1 for Ed25519)
///   √(−1)   = `sqrt_m1()`
///
/// Left as axiom because the 510-bit limb arithmetic exceeds Z3's capacity.
///
/// Runtime validation: `test_axiom_mc_times_sqrt_ad_m1` in lizard_ristretto.rs.
pub proof fn axiom_mc_times_sqrt_ad_m1()
    ensures
        field_mul(midouble_invsqrt_a_minus_d(), spec_sqrt_ad_minus_one()) == field_mul(
            2,
            sqrt_m1(),
        ),
{
    admit();
}

// =============================================================================
// Jacobi → Edwards edge-case lemmas (fully proved)
// =============================================================================
/// S = 0 ⟹ jacobi_to_edwards_affine(0, t) = (0, 1).
///
/// y = (1 − 0²)/(1 + 0²) = 1,  x = 2·0/(t·c) = 0.
pub proof fn lemma_jacobi_to_edwards_affine_s_zero(t: nat)
    ensures
        jacobi_to_edwards_affine(0, t) == (0nat, 1nat),
{
    p_gt_2();
    assert(field_square(0nat) == 0) by {
        lemma_small_mod(0nat, p());
    };
    assert(field_sub(1nat, 0nat) == 1) by {
        lemma_small_mod(1nat, p());
        lemma_mod_add_multiples_vanish(1int, p() as int);
    };
    assert(field_add(1nat, 0nat) == 1) by {
        lemma_small_mod(1nat, p());
    };
    assert(field_inv(1nat) == 1) by {
        lemma_field_inv_one();
    };
    assert(field_mul(1nat, 1nat) == 1) by {
        lemma_field_mul_one_right(1nat);
        lemma_small_mod(1nat, p());
    };
    assert(field_mul(2, 0nat) == 0) by {
        lemma_field_mul_zero_right(2, 0nat);
    };
    let denom = field_inv(field_mul(t, spec_sqrt_ad_minus_one()));
    assert(field_mul(0nat, denom) == 0) by {
        lemma_field_mul_zero_left(0nat, denom);
        lemma_small_mod(0nat, p());
    };
}

/// s² = 1 ⟹ y-coordinate of jacobi_to_edwards_affine is 0.
///
/// y = (1 − 1)/(1 + 1) = 0/2 = 0.
pub proof fn lemma_jacobi_to_edwards_affine_y_zero_when_s_sq_one(s: nat, t: nat)
    requires
        field_square(s) == 1,
    ensures
        jacobi_to_edwards_affine(s, t).1 == 0,
{
    p_gt_2();
    assert(field_sub(1, field_square(s)) == 0) by {
        lemma_field_sub_self(1nat);
    };
    assert(0nat % p() == 0) by {
        lemma_small_mod(0nat, p());
    };
    assert(field_mul(field_sub(1, field_square(s)), field_inv(field_add(1, field_square(s)))) == 0)
        by {
        lemma_field_mul_zero_left(
            field_sub(1, field_square(s)),
            field_inv(field_add(1, field_square(s))),
        );
    };
}

/// Axiom (birational pair 0,1 → coset 0,2): For a non-degenerate
/// Birational pair (0, 2): for P = (X:Y:Z:T) on E with x,y ≠ 0, the dual
/// isogeny θ̂: E → J lifts P to two Jacobi quartic points JQ[0], JQ[1]
/// (from the (Z−Y, Z+Y) basis), and the forward isogeny θ: J → E recovers:
///
///   θ(JQ[0]) = P              (= coset[0])
///   θ(JQ[1]) = P + T₄         (= coset[2])
///
/// where T₄ = (0, −1) is the 4-torsion point (x ↦ −x, y ↦ −y),
/// θ(s,t) = `jacobi_to_edwards_affine(s, t)`, and
/// coset = { P, P+T₂, P+T₄, P+T₆ } = `ristretto_coset_affine(x, y)`.
///
/// Reference: Hamburg (2015) "Decaf" §4 (J[2] coset), §4.1 (isogeny);
///   ristretto.group/details/isogenies.html (θ = η∘ψ, θ̂ = dual).
///
/// **Gap:** the indexed mapping JQ[0]→coset[0], JQ[1]→coset[2] follows
///   from composing θ̂ with θ but is not stated directly in any reference.
///
/// Runtime validation: `test_axiom_birational_pair01` in lizard_ristretto.rs.
pub proof fn axiom_jacobi_quartic_birational_pair01(point: crate::edwards::EdwardsPoint)
    requires
        is_well_formed_edwards_point(point),
    ensures
        ({
            let (x, y) = edwards_point_as_affine(point);
            let coset = ristretto_coset_affine(x, y);
            let jcs = spec_to_jacobi_quartic_ristretto(point);
            x != 0 && y != 0 ==> (jacobi_to_edwards_affine(jcs[0].0, jcs[0].1) == coset[0]
                && jacobi_to_edwards_affine(jcs[1].0, jcs[1].1) == coset[2])
        }),
{
    admit();
}

/// Torsion pair (1, 3): for P = (X:Y:Z:T) on E with x,y ≠ 0, applying
/// the 4-torsion "torque" (X,Y,Z) ↦ (Y,X,iZ) before the dual isogeny
/// yields JQ[2], JQ[3], and the forward isogeny θ recovers:
///
///   θ(JQ[2]) = P + T₂         (= coset[1])
///   θ(JQ[3]) = P + T₆         (= coset[3])
///
/// where T₂ = (0, 1) (identity for Edwards addition), T₆ = T₂ + T₄,
/// and the torque effectively adds Q₄ = (i, 0) to bridge E/E[4] to E/E[2].
///
/// Reference: Hamburg (2015) "Decaf" §4, §7 (cofactor-8 coset
///   representatives); ristretto.group/details/isogeny_encoding.html
///   (torquing procedure); ristretto.group/formulas/encoding.html.
///
/// **Gap:** the indexed mapping JQ[2]→coset[1], JQ[3]→coset[3] follows
///   from the torque + isogeny composition but is not stated directly.
///
/// Runtime validation: `test_axiom_torsion_pair23` in lizard_ristretto.rs.
pub proof fn axiom_jacobi_quartic_torsion_pair23(point: crate::edwards::EdwardsPoint)
    requires
        is_well_formed_edwards_point(point),
    ensures
        ({
            let (x, y) = edwards_point_as_affine(point);
            let coset = ristretto_coset_affine(x, y);
            let jcs = spec_to_jacobi_quartic_ristretto(point);
            x != 0 && y != 0 ==> (jacobi_to_edwards_affine(jcs[2].0, jcs[2].1) == coset[1]
                && jacobi_to_edwards_affine(jcs[3].0, jcs[3].1) == coset[3])
        }),
{
    admit();
}

/// In the edge case (xn == 0 || yn == 0), spec_to_jacobi_quartic_ristretto
/// produces specific constant JQ values: (0,1), (0,1), (1,mc), (neg(1),mc).
#[verifier::spinoff_prover]
pub proof fn lemma_jq_edge_case_values(point: crate::edwards::EdwardsPoint)
    requires
        is_well_formed_edwards_point(point),
    ensures
        ({
            let (xn, yn, zn, _tn) = edwards_point_as_nat(point);
            let jcs = spec_to_jacobi_quartic_ristretto(point);
            let mc = midouble_invsqrt_a_minus_d();
            (xn == 0 || yn == 0) ==> (jcs[0] == (0nat, 1nat) && jcs[1] == (0nat, 1nat) && jcs[2]
                == (1nat, mc) && jcs[3] == (field_neg(1), mc))
        }),
{
    let (xn, yn, zn, _tn) = edwards_point_as_nat(point);
    if !(xn == 0 || yn == 0) {
        return ;
    }
    reveal(spec_to_jacobi_quartic_ristretto);
    let jcs = spec_to_jacobi_quartic_ristretto(point);
    p_gt_2();
    lemma_small_mod(0nat, p());

    // The x_or_y_zero flag in spec_to_jacobi_quartic_ristretto is true
    // so t0=1, t1=1, t2=mc, t3=mc, s2=1, s3=neg(1)

    // For s0: s0 = field_mul(s_over_x, xn)
    // When xn == 0: field_mul(anything, 0) = 0
    // When yn == 0: y2 = field_square(0) = 0, den1 = field_mul(gamma, 0) = 0,
    //   s_over_x = field_mul(0, z_min_y) = 0, s0 = field_mul(0, xn) = 0
    let y2 = field_square(yn);
    if xn == 0 {
        let s_over_x = field_mul(
            field_mul(
                nat_invsqrt(
                    field_mul(
                        field_mul(field_square(y2), field_square(xn)),
                        field_sub(field_square(zn), y2),
                    ),
                ),
                y2,
            ),
            field_sub(zn, yn),
        );
        assert(field_mul(s_over_x, 0nat) == 0) by {
            lemma_field_mul_zero_right(s_over_x, 0nat);
        };
        let sp_over_xp = field_mul(
            field_mul(
                nat_invsqrt(
                    field_mul(
                        field_mul(field_square(y2), field_square(xn)),
                        field_sub(field_square(zn), y2),
                    ),
                ),
                y2,
            ),
            field_add(zn, yn),
        );
        assert(field_mul(field_neg(sp_over_xp), 0nat) == 0) by {
            lemma_field_mul_zero_right(field_neg(sp_over_xp), 0nat);
        };
    } else {
        // yn == 0, so y2 = field_square(0) = 0
        assert(y2 == 0) by {
            lemma_small_mod(0nat, p());
        };
        let y4 = field_square(y2);
        assert(y4 == 0) by {
            lemma_small_mod(0nat, p());
        };
        let gamma = nat_invsqrt(
            field_mul(field_mul(y4, field_square(xn)), field_sub(field_square(zn), y2)),
        );
        assert(field_mul(y4, field_square(xn)) == 0) by {
            lemma_field_mul_zero_left(y4, field_square(xn));
        };
        let den1 = field_mul(gamma, y2);
        assert(den1 == 0) by {
            lemma_field_mul_zero_right(gamma, 0nat);
        };
        let s_over_x = field_mul(den1, field_sub(zn, yn));
        assert(s_over_x == 0) by {
            lemma_field_mul_zero_left(den1, field_sub(zn, yn));
        };
        assert(field_mul(s_over_x, xn) == 0) by {
            lemma_field_mul_zero_left(s_over_x, xn);
        };
        let sp_over_xp = field_mul(den1, field_add(zn, yn));
        assert(sp_over_xp == 0) by {
            lemma_field_mul_zero_left(den1, field_add(zn, yn));
        };
        assert(field_mul(field_neg(sp_over_xp), xn) == 0) by {
            assert(field_neg(0nat) == 0) by {
                vstd::arithmetic::div_mod::lemma_mod_self_0(p() as int);
            };
            lemma_field_mul_zero_left(field_neg(sp_over_xp), xn);
        };
    }
}

/// jacobi_to_edwards_affine(1, mc) == (neg(sqrt_m1()), 0) and
/// jacobi_to_edwards_affine(neg(1), mc) == (sqrt_m1(), 0).
#[verifier::spinoff_prover]
pub proof fn lemma_jq_four_torsion_images()
    ensures
        jacobi_to_edwards_affine(1, midouble_invsqrt_a_minus_d()) == (field_neg(sqrt_m1()), 0nat),
        jacobi_to_edwards_affine(field_neg(1), midouble_invsqrt_a_minus_d()) == (sqrt_m1(), 0nat),
{
    p_gt_2();
    lemma_small_mod(1nat, p());
    lemma_small_mod(0nat, p());
    let mc = midouble_invsqrt_a_minus_d();
    let sqrt_ad_m1 = spec_sqrt_ad_minus_one();
    let i = sqrt_m1();

    // --- y-coordinates are 0 (since s² = 1 for both) ---
    lemma_one_and_neg_one_square_to_one();
    lemma_jacobi_to_edwards_affine_y_zero_when_s_sq_one(1, mc);
    lemma_jacobi_to_edwards_affine_y_zero_when_s_sq_one(field_neg(1), mc);

    // --- Shared: inv(i) = neg(i) ---
    lemma_sqrt_m1_nonzero();
    lemma_field_mul_neg(i, i);
    assert(field_mul(i, field_neg(i)) == field_neg(field_mul(i, i)));
    axiom_sqrt_m1_squared();
    lemma_small_mod((p() - 1) as nat, p());
    assert(field_neg(1nat) == (p() - 1) as nat);
    assert(field_square(i) == (i * i) % p());
    assert(field_square(i) == field_neg(1nat));
    lemma_field_neg_neg(1nat);
    lemma_small_mod(1nat, p());
    assert(field_neg(field_neg(1nat)) == 1nat);
    assert(field_mul(i, field_neg(i)) == 1);
    assert(field_neg(i) < p()) by {
        lemma_mod_bound((p() - i % p()) as int, p() as int);
    };
    lemma_small_mod(i, p());
    field_inv_unique(i, field_neg(i));

    // --- x-coordinate of JQ[2] = (1, mc) ---
    // x = 2·1 / (mc · sqrt_ad_m1) = 2 / (2i) = inv(i) = neg(i)
    assert(2nat < p()) by {
        pow255_gt_19();
    };
    assert(field_mul(2nat, 1nat) == 2nat) by {
        lemma_field_mul_one_right(2nat);
        lemma_small_mod(2nat, p());
    };
    axiom_mc_times_sqrt_ad_m1();
    let two_i = field_mul(2, i);
    lemma_small_mod(2nat, p());
    lemma_a_times_inv_ab_is_inv_b(2, i);

    // --- x-coordinate of JQ[3] = (neg(1), mc) ---
    // x = 2·neg(1) / (mc · sqrt_ad_m1) = neg(2) / (2i) = neg(inv(i)) = neg(neg(i)) = i
    lemma_field_mul_neg(2nat, 1nat);
    let inv_two_i = field_inv(two_i);
    lemma_field_neg_mul_left(2nat, inv_two_i);
    lemma_field_neg_neg(i);
    lemma_mod_bound((2nat * inv_two_i) as int, p() as int);
    lemma_small_mod(field_mul(2nat, inv_two_i), p());
}

/// Edge case: When x = 0 or y = 0, the replacement values
/// (s0=0, s1=0, s2=1, s3=−1, t0=1, t1=1, t2=−2i/√(−d−1), t3=−2i/√(−d−1))
/// still produce Jacobi quartic points that each map to *some* coset member
/// (possibly repeated).
///
/// The edge case arises at the identity (0,1,1,0) and the
/// 2-torsion point (0,−1,1,0). The formulas degenerate (gamma
/// becomes 0), so constant replacement values are used.
///
/// Proved modulo two narrow bridge axioms about concrete constant values:
/// - `axiom_four_torsion_affine`: affine coordinates of E[4] elements
/// - `axiom_mc_times_sqrt_ad_m1`: mc · √(ad−1) = 2·√(−1)
///
/// Reference: Hamburg (2015) "Decaf", §4 — handling of
///   exceptional/degenerate points in the encoding.
///
/// Runtime validation: `test_axiom_edge_values` below.
#[verifier::spinoff_prover]
pub proof fn lemma_jacobi_quartic_edge_values(point: crate::edwards::EdwardsPoint)
    requires
        is_well_formed_edwards_point(point),
    ensures
        ({
            let (x, y) = edwards_point_as_affine(point);
            let coset = ristretto_coset_affine(x, y);
            let jcs = spec_to_jacobi_quartic_ristretto(point);
            (x == 0 || y == 0) ==> forall|i: int|
                #![trigger coset[i]]
                0 <= i < 4 ==> ({
                    let ji = jacobi_to_edwards_affine(jcs[i].0, jcs[i].1);
                    ji == coset[0] || ji == coset[1] || ji == coset[2] || ji == coset[3]
                })
        }),
{
    let (x, y) = edwards_point_as_affine(point);
    if !(x == 0 || y == 0) {
        return ;
    }
    p_gt_2();
    let (xn, yn, zn, _tn) = edwards_point_as_nat(point);
    let z_inv = field_inv(zn);

    // zn != 0 from well-formedness
    assert(zn % p() != 0) by {
        lemma_canonical_nat_lt_p(&edwards_z(point));
        lemma_small_mod(zn, p());
    };
    assert(xn < p()) by {
        lemma_canonical_nat_lt_p(&edwards_x(point));
    };
    assert(yn < p()) by {
        lemma_canonical_nat_lt_p(&edwards_y(point));
    };

    // Derive xn == 0 || yn == 0 from affine x == 0 || y == 0
    if x == 0 {
        lemma_affine_zero_implies_proj_zero(xn, zn);
    }
    if y == 0 {
        lemma_affine_zero_implies_proj_zero(yn, zn);
    }
    assert(xn == 0 || yn == 0);

    // Get concrete JQ edge values
    lemma_jq_edge_case_values(point);

    // x, y are field_mul results so they are < p()
    assert(x < p()) by {
        lemma_mod_bound((xn * z_inv) as int, p() as int);
    };
    assert(y < p()) by {
        lemma_mod_bound((yn * z_inv) as int, p() as int);
    };

    // Establish on-curve for the edge-coset preconditions
    assert(is_on_edwards_curve(x, y)) by {
        lemma_projective_implies_affine_on_curve(xn, yn, zn);
    };
    if x == 0 {
        lemma_on_curve_x_zero_implies_y_pm_one(x, y);
    }
    if y == 0 {
        lemma_on_curve_y_zero_implies_x_sq_neg_one(x, y);
    }
    // Coset contains the 4 torsion points

    lemma_edge_coset_contains_e4(x, y);
    let coset = ristretto_coset_affine(x, y);

    // JQ birational images
    let jcs = spec_to_jacobi_quartic_ristretto(point);
    let mc = midouble_invsqrt_a_minus_d();
    let id = (0nat, 1nat);
    let i_pt = (sqrt_m1(), 0nat);
    let neg_i_pt = (field_neg(sqrt_m1()), 0nat);

    // JQ[0] = JQ[1] = (0, 1) → (0, 1)
    lemma_jacobi_to_edwards_affine_s_zero(1);
    assert(jacobi_to_edwards_affine(0nat, 1nat) == id);

    // JQ[2] = (1, mc) → (neg(sqrt_m1()), 0) and JQ[3] = (neg(1), mc) → (sqrt_m1(), 0)
    lemma_jq_four_torsion_images();
    assert(jacobi_to_edwards_affine(1nat, mc) == neg_i_pt);
    assert(jacobi_to_edwards_affine(field_neg(1), mc) == i_pt);

    // Each JQ image is a coset member
    assert forall|i: int| #![trigger coset[i]] 0 <= i < 4 implies ({
        let ji = jacobi_to_edwards_affine(jcs[i].0, jcs[i].1);
        ji == coset[0] || ji == coset[1] || ji == coset[2] || ji == coset[3]
    }) by {
        if i == 0 || i == 1 {
            assert(jcs[i] == (0nat, 1nat));
        } else if i == 2 {
            assert(jcs[i] == (1nat, mc));
        } else {
            assert(jcs[i] == (field_neg(1), mc));
        }
    };
}

/// Elligator inversion round-trip: when `spec_elligator_inv` reports success,
/// applying the forward Elligator map to the returned field element yields
/// `jacobi_to_edwards_affine(s, t)`.
///
/// Proved structurally by branch analysis on `spec_elligator_inv`:
/// - s ≡ 0: forward map on 0 or √(id) produces (0, 1) = θ(0, t)
/// - s ≢ 0, non-square: vacuously true (inverse reports failure)
/// - s ≢ 0, square: forward Elligator recovers the Jacobi→Edwards image
///   (delegated to `axiom_elligator_inv_square_case`)
///
/// Reference: Hamburg (2015) "Decaf" (https://eprint.iacr.org/2015/673),
///   Appendix C (inverse), §6 (forward), §4.1 (birational θ).
///   Ristretto reparameterization: ristretto.group/details/elligator.html.
///
/// Runtime validation: `test_axiom_elligator_inv_roundtrip` (100+ random
///   Jacobi quartic points + corner cases)
pub proof fn lemma_elligator_inv_algebraic(s: nat, t: nat)
    ensures
        spec_elligator_inv(s, t).0 ==> spec_elligator_ristretto_flavor(spec_elligator_inv(s, t).1)
            == jacobi_to_edwards_affine(s, t),
{
    reveal(spec_elligator_inv);
    if field_canonical(s) == 0 {
        // s ≡ 0 mod p ⟹ jacobi_to_edwards_affine(s, t) = (0, 1)
        assert(jacobi_to_edwards_affine(s, t) == (0nat, 1nat)) by {
            lemma_jacobi_to_edwards_affine_s_canonical_zero(s, t);
        };
        if field_canonical(t) == 1 {
            // Branch 1: returns (true, √(id))
            assert(spec_elligator_ristretto_flavor(sqrt_id()) == (0nat, 1nat)) by {
                axiom_elligator_forward_sqrt_id();
            };
        } else {
            // Branch 2: returns (true, 0)
            assert(spec_elligator_ristretto_flavor(0) == (0nat, 1nat)) by {
                axiom_elligator_forward_zero();
            };
        }
    } else {
        let a = field_mul(field_add(t, 1), dp1_over_dm1());
        let s2 = field_square(s);
        let s4 = field_square(s2);
        let inv_sq_y = field_mul(field_sub(s4, field_square(a)), sqrt_m1());
        let y = nat_invsqrt(inv_sq_y);
        let sq = field_canonical(inv_sq_y) != 0 && is_sqrt_ratio(1, inv_sq_y, y);
        if !sq {
            // Branch 3: inverse reports failure — vacuously true
        } else {
            // Branch 4: s ≢ 0, square case — the algebraic round-trip identity
            let pms2 = if is_negative(s) {
                field_neg(s2)
            } else {
                s2
            };
            let x = field_mul(field_add(a, pms2), y);
            let r0 = field_abs(x);
            assert(spec_elligator_ristretto_flavor(r0) == jacobi_to_edwards_affine(s, t)) by {
                axiom_elligator_inv_square_case(s, t, a, s2, s4, inv_sq_y, y, pms2, x, r0);
            };
        }
    }
}

/// Generalization of `lemma_jacobi_to_edwards_affine_s_zero`: when s ≡ 0 mod p
/// (not necessarily s = 0), θ(s, t) = (0, 1).
///
/// All field operations are mod p, so field_square(s) = 0 when s ≡ 0.
proof fn lemma_jacobi_to_edwards_affine_s_canonical_zero(s: nat, t: nat)
    requires
        field_canonical(s) == 0,
    ensures
        jacobi_to_edwards_affine(s, t) == (0nat, 1nat),
{
    p_gt_2();
    // s ≡ 0 mod p ⟹ s² ≡ 0 mod p
    assert(field_square(s) == 0) by {
        assert(s % p() == 0);
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(s as int / p() as int, p() as int);
        assert((s * s) % p() == 0) by {
            lemma_field_mul_zero_left(s, s);
        };
    };
    // Now identical to s=0 case
    lemma_jacobi_to_edwards_affine_s_zero(t);
    // Bridge: jacobi_to_edwards_affine(s, t) uses field_square(s) which is 0
    // Since all field ops depend only on s mod p, the result is the same as for s=0
    assert(field_mul(2, s) == 0) by {
        lemma_field_mul_zero_right(2, s);
    };
    let denom = field_inv(field_mul(t, spec_sqrt_ad_minus_one()));
    assert(field_mul(field_mul(2, s), denom) == 0) by {
        lemma_field_mul_zero_left(field_mul(2, s), denom);
        lemma_small_mod(0nat, p());
    };
    assert(field_sub(1nat, 0nat) == 1) by {
        lemma_small_mod(1nat, p());
        lemma_mod_add_multiples_vanish(1int, p() as int);
    };
    assert(field_add(1nat, 0nat) == 1) by {
        lemma_small_mod(1nat, p());
    };
    assert(field_inv(1nat) == 1) by {
        lemma_field_inv_one();
    };
    assert(field_mul(1nat, 1nat) == 1) by {
        lemma_field_mul_one_right(1nat);
        lemma_small_mod(1nat, p());
    };
}

/// Forward Elligator map on r₀ = 0 produces the identity point (0, 1).
///
/// When r₀ = 0: r = i·0² = 0, s_prime_raw = s_if_square·0 = 0,
/// s_prime = 0. In either branch (was_square or not), the s value
/// that enters the completed point computation produces s² = 0,
/// giving Y = 1, T = 1, and X = 2·s·D (which involves s=0 in
/// the !was_square branch).
///
/// The key observation: regardless of was_square, the completed point's
/// affine x-coordinate is 0 and y-coordinate is 1, because in both
/// branches the final s value satisfies s² = 0 or the X numerator is 0.
///
/// This is a constant-level identity about the Elligator map on a specific
/// input. Runtime validated by `test_axiom_elligator_inv_roundtrip`.
proof fn axiom_elligator_forward_zero()
    ensures
        spec_elligator_ristretto_flavor(0) == (0nat, 1nat),
{
    admit();
}

/// Constant identity: the forward Elligator map on √(id) produces (0, 1).
///
/// √(id)² = id, so r = i·(id) = -d, giving D = (-1+d²)(0) = 0 ⟹ X = 0.
///
/// Not provable by Z3 because √(id) is a 255-bit constant whose square
/// must equal i·d mod p. Verified at runtime by `test_axiom_elligator_inv_roundtrip`.
proof fn axiom_elligator_forward_sqrt_id()
    ensures
        spec_elligator_ristretto_flavor(sqrt_id()) == (0nat, 1nat),
{
    admit();
}

/// Axiom (square-case round-trip): When s ≢ 0 and the inverse square root
/// exists, the forward Elligator map on |x| recovers jacobi_to_edwards_affine(s, t).
///
/// This is the algebraic core of the Elligator inversion round-trip.
/// The forward map Elligator(|x|) produces intermediates (s', N_t', D') such that
/// s' = S and D'·T = S·N_t', where S, T are the Jacobi quartic coordinates.
///
/// Reference: Westerbaan/Hamburg, go-ristretto (2019); Hamburg (2015) "Decaf"
///   Appendix C. The identity connects the Ristretto-parameterized inverse
///   (spec_elligator_inv) to the forward map (spec_elligator_ristretto_flavor)
///   through the birational map θ (jacobi_to_edwards_affine).
///
/// Runtime validation: `test_axiom_elligator_inv_roundtrip` in lizard_ristretto.rs.
proof fn axiom_elligator_inv_square_case(
    s: nat,
    t: nat,
    a: nat,
    s2: nat,
    s4: nat,
    inv_sq_y: nat,
    y: nat,
    pms2: nat,
    x: nat,
    r0: nat,
)
    requires
        field_canonical(s) != 0,
        a == field_mul(field_add(t, 1), dp1_over_dm1()),
        s2 == field_square(s),
        s4 == field_square(s2),
        inv_sq_y == field_mul(field_sub(s4, field_square(a)), sqrt_m1()),
        y == nat_invsqrt(inv_sq_y),
        field_canonical(inv_sq_y) != 0,
        is_sqrt_ratio(1, inv_sq_y, y),
        pms2 == (if is_negative(s) {
            field_neg(s2)
        } else {
            s2
        }),
        x == field_mul(field_add(a, pms2), y),
        r0 == field_abs(x),
    ensures
        spec_elligator_ristretto_flavor(r0) == jacobi_to_edwards_affine(s, t),
{
    admit();
}

/// Axiom (Elligator fiber completeness): Every field element `r` whose
/// forward Elligator image lies in the Ristretto coset of `point`
/// appears among the 8 spec-level candidates produced by Jacobi quartic
/// inversion + dual (see `spec_lizard_decode_candidates`).
///
/// The 8 candidates arise from: 4 coset members (J[2] coset) × 2 signs
/// (dual negation (s,t) ↔ (−s,−t) on the Jacobi quartic).
///
/// This is a derived property composing:
/// - `spec_to_jacobi_quartic_ristretto` covering all 4 coset members
///   (axiom_jacobi_quartic_birational_pair01, axiom_jacobi_quartic_torsion_pair23,
///   lemma_jacobi_quartic_edge_values)
/// - `spec_elligator_inv` + dual covering both Elligator preimage signs
///   per Jacobi quartic point (Decaf Appendix C sign analysis)
/// - The Ristretto Elligator map factoring through exactly one Jacobi
///   quartic point per coset member
///
/// Background references:
/// - Hamburg (2015) "Decaf" (https://eprint.iacr.org/2015/673),
///   §4 (J[2] coset covers all representatives), §6 (Elligator is at
///   most 4:1 after J[2] quotient in the cofactor-4 setting),
///   Appendix C (inverse formula + sign analysis).
/// - https://ristretto.group/details/isogeny_encoding.html
///   (cofactor-8 extension: torquing doubles the coset from E[2] to
///   E[4], yielding 4 coset members instead of Decaf's 2).
///
/// **Gap:** §6 establishes 4:1 for cofactor-4 Decaf; the 8-candidate
///   completeness for cofactor-8 Ristretto (4 coset × 2 dual signs)
///   is not directly stated in any paper. It follows from combining
///   the coset coverage axioms above with the Elligator inverse sign
///   ambiguity, but the full composition has not been published.
///   Provable by formal proof (e.g., Lean 4 / Mathlib) given the
///   component proofs for axioms 3–5.
///
/// Runtime validation: `test_elligator_inv` in lizard_ristretto.rs
///   (100 random points × 4 coset members × forward/inverse round-trip).
pub proof fn axiom_elligator_fiber_complete(point: crate::edwards::EdwardsPoint, r: nat)
    requires
        is_well_formed_edwards_point(point),
        r < p(),
    ensures
        ({
            let (x, y) = edwards_point_as_affine(point);
            let coset = ristretto_coset_affine(x, y);
            let ej = spec_elligator_ristretto_flavor(r);
            let candidates = spec_lizard_decode_candidates(point);
            (ej == coset[0] || ej == coset[1] || ej == coset[2] || ej == coset[3]) ==> exists|
                j: int,
            |
                #![trigger candidates[j]]
                0 <= j < 8 && candidates[j].0 && candidates[j].1 == r
        }),
{
    admit();
}

// =============================================================================
// JQ spec → candidate identity (fully proved)
// =============================================================================
/// Given `spec_to_jacobi_quartic_ristretto(point)`, each slot of
/// `spec_lizard_decode_candidates(point)` is the corresponding
/// `spec_elligator_inv` applied to the JQ pair (even slots) or its
/// negation (odd slots).
///
/// This is a definitional unfolding of `spec_lizard_decode_candidates`;
/// the spinoff isolates the unfolding from the caller's solver context.
#[verifier::spinoff_prover]
pub proof fn lemma_candidate_from_jq_spec(point: crate::edwards::EdwardsPoint)
    ensures
        ({
            let spec_jcs = spec_to_jacobi_quartic_ristretto(point);
            let c = spec_lizard_decode_candidates(point);
            &&& c[0] == spec_elligator_inv(spec_jcs[0].0, spec_jcs[0].1)
            &&& c[1] == spec_elligator_inv(field_neg(spec_jcs[0].0), field_neg(spec_jcs[0].1))
            &&& c[2] == spec_elligator_inv(spec_jcs[1].0, spec_jcs[1].1)
            &&& c[3] == spec_elligator_inv(field_neg(spec_jcs[1].0), field_neg(spec_jcs[1].1))
            &&& c[4] == spec_elligator_inv(spec_jcs[2].0, spec_jcs[2].1)
            &&& c[5] == spec_elligator_inv(field_neg(spec_jcs[2].0), field_neg(spec_jcs[2].1))
            &&& c[6] == spec_elligator_inv(spec_jcs[3].0, spec_jcs[3].1)
            &&& c[7] == spec_elligator_inv(field_neg(spec_jcs[3].0), field_neg(spec_jcs[3].1))
        }),
{
}

// =============================================================================
// Canonicity of spec_lizard_fe_bytes (fully proved)
// =============================================================================
/// `u8_32_as_nat(spec_lizard_fe_bytes(m)) < p()`.
///
/// Byte 31 is masked with `& 63`, so the value is at most
/// 63·2²⁴⁸ + (2²⁴⁸ − 1) = 2²⁵⁴ − 1 < p = 2²⁵⁵ − 19.
///
/// Critical for the SHA round-trip: `from_bytes(spec_lizard_fe_bytes(m))`
/// is the identity (no mod-p reduction).
///
/// ## Proof sketch
///
/// `spec_lizard_fe_bytes` masks byte 31 with `& 63u8`, giving `bytes[31] <= 63`.
///
/// ```text
///   u8_32_as_nat(bytes)
///     = Σ_{i=0}^{30} bytes[i] · 256^i  +  bytes[31] · 256^31
///     ≤ (256^31 − 1)                    +  63 · 256^31
///     = 64 · 256^31 − 1
///     = 2^254 − 1
///     < 2^255 − 19
///     = p
/// ```
///
/// Runtime validation: `test_lizard_decode_roundtrip_exhaustive` encodes 200+
/// random messages, confirming `from_bytes(spec_lizard_fe_bytes(m))` round-trips.
pub proof fn lemma_spec_lizard_fe_bytes_canonical(m: Seq<u8>)
    requires
        m.len() == 16,
    ensures
        u8_32_as_nat(&spec_lizard_fe_bytes(m)) < p(),
{
    let bytes = spec_lizard_fe_bytes(m);

    // Step 1: bytes[31] <= 63 (from the & 63 mask in spec_lizard_fe_bytes)
    axiom_sha256_output_length(m);
    let digest = spec_sha256(m);
    let s0 = Seq::new(
        32,
        |i: int|
            if 8 <= i < 24 {
                m[i - 8]
            } else {
                digest[i]
            },
    );
    let s1 = s0.update(0, s0[0] & 254u8);
    let s2 = s1.update(31, s1[31] & 63u8);

    // The & 63u8 mask bounds byte 31 to at most 63
    let b31_before: u8 = s1[31];
    let b31_after: u8 = b31_before & 63u8;
    assert(b31_after <= 63) by (bit_vector)
        requires
            b31_after == (b31_before & 63u8),
    ;
    assert(s2[31] == b31_after);
    assert(bytes == seq_to_array_32(s2));
    assert(bytes[31] == s2[31]);
    assert(bytes[31] <= 63);

    // Step 2: Decompose u8_32_as_nat into prefix(31) + bytes[31] * pow2(248)
    lemma_u8_32_as_nat_equals_rec(&bytes);
    lemma_decomposition_prefix_rec(&bytes, 31);
    let prefix31 = bytes_as_nat_prefix(bytes@, 31);
    assert(u8_32_as_nat(&bytes) == u8_32_as_nat_rec(&bytes, 0));
    assert(u8_32_as_nat_rec(&bytes, 0) == prefix31 + u8_32_as_nat_rec(&bytes, 31));
    assert(u8_32_as_nat_rec(&bytes, 31) == (bytes[31] as nat) * pow2(248) + u8_32_as_nat_rec(
        &bytes,
        32,
    ));
    assert(u8_32_as_nat_rec(&bytes, 32) == 0);
    assert(u8_32_as_nat(&bytes) == prefix31 + (bytes[31] as nat) * pow2(248));

    // Step 3: prefix(31) < pow2(248)
    lemma_bytes_as_nat_prefix_bounded(bytes@, 31);

    // Step 4: pow2(254) < p()
    // We use bytes[31] <= 63 and prefix31 < pow2(248) to bound the total.
    // 63 * pow2(248) + pow2(248) = 64 * pow2(248) = pow2(254)
    assert(pow2(6) == 64) by {
        lemma2_to64();
    }
    assert(pow2(254) == 64 * pow2(248)) by {
        assert(6 + 248 == 254nat);
        lemma_pow2_adds(6, 248);
    }
    assert(u8_32_as_nat(&bytes) < pow2(254)) by (nonlinear_arith)
        requires
            prefix31 < pow2(248),
            bytes[31] as nat <= 63,
            u8_32_as_nat(&bytes) == prefix31 + (bytes[31] as nat) * pow2(248),
            pow2(254) == 64 * pow2(248),
    ;

    // Step 5: pow2(254) <= p()  (since p = 2^255 - 19 > 2^254)
    pow255_gt_19();
    assert(pow2(1) == 2) by {
        lemma2_to64();
    }
    assert(pow2(255) == pow2(254) * pow2(1)) by {
        lemma_pow2_adds(254, 1);
    }
    assert(p() == pow2(255) - 19);
}

// =============================================================================
// Decode exhaustiveness (point-indexed, no free n_found)
// =============================================================================
/// Decode exhaustiveness: `spec_sha_consistent_count(point)` determines
/// whether a unique Lizard preimage exists.
///
/// No free `n_found` parameter — the count is a deterministic function of
/// the point via `spec_sha_consistent_count`. This eliminates the soundness
/// gap where an incorrect `n_found` could produce inconsistent conclusions.
///
/// ## Logical dependence on sub-properties
///
/// **(a) `lemma_spec_lizard_fe_bytes_injective`** (proved):
///   `spec_lizard_fe_bytes(m₁) == spec_lizard_fe_bytes(m₂) ⟹ m₁ == m₂`.
///
/// **(b) `axiom_elligator_fiber_complete`** (admitted): every r with
///   Elligator(r) ∈ coset(P) appears among the 8 candidates.
///
/// **(c) exec-spec candidate correspondence** (proved): exec `(mask, fes)`
///   matches `spec_lizard_decode_candidates(point)`. Now a direct postcondition
///   of `elligator_ristretto_flavor_inverse` (via `lemma_candidate_from_jq_spec`
///   and the strengthened `to_jacobi_quartic_ristretto` ensures).
///
/// **(d) `lemma_spec_lizard_fe_bytes_canonical`** (proved): canonical encoding.
///
/// **(e) `lemma_canonical_bytes_equal`** (proved): u8_32_as_nat injective.
///
/// count == 1: passed_data is a preimage. Any other preimage m₂ would
///   have r(m₂) among the 8 candidates (by (b) + (c)), and the SHA check
///   would pass by (d) + (e), giving count ≥ 2 — contradiction.
///
/// count == 0: if a preimage existed, (b) + (c) would place it among
///   candidates, and SHA consistency would give count ≥ 1 — contradiction.
///
/// count ≥ 2: two SHA-consistent candidates yield two coset preimages.
///   By (a), these messages differ, so uniqueness fails.
///
/// Runtime validation: `test_lizard_decode_roundtrip_exhaustive` in
///   lizard_ristretto.rs (200+ random round-trips).
pub proof fn axiom_decode_from_point(
    point: crate::edwards::EdwardsPoint,
    passed_data: Option<Seq<u8>>,
)
    requires
        is_well_formed_edwards_point(point),
        spec_sha_consistent_count(point) >= 1 <==> passed_data.is_Some(),
        passed_data.is_Some() ==> ({
            let (x, y) = edwards_point_as_affine(point);
            passed_data.unwrap().len() == 16 && is_lizard_preimage_coset(
                passed_data.unwrap(),
                ristretto_coset_affine(x, y),
            )
        }),
    ensures
        ({
            let (x, y) = edwards_point_as_affine(point);
            let c = spec_sha_consistent_count(point);
            (c == 1 ==> lizard_ristretto_has_unique_preimage(x, y)) && (c != 1
                ==> !lizard_ristretto_has_unique_preimage(x, y))
        }),
{
    admit();
}

/// Per-slot bridge: exec `ok` matches `candidates[j].0 && spec_candidate_sha_consistent(cj.1)`.
///
/// Extracts the heavy proof obligation from the decode loop body into a
/// spinoff prover to avoid rlimit pressure on the loop.
#[verifier::spinoff_prover]
pub proof fn lemma_exec_ok_matches_spec_slot(
    mask_bit_set: bool,
    sha_match: bool,
    buf2: &[u8; 32],
    msg: Seq<u8>,
    h: [u8; 32],
    fe_j: &FieldElement,
    cj: (bool, nat),
)
    requires
        msg.len() == 16,
        forall|i: int| 0 <= i < 16 ==> msg[i] == buf2[(8 + i) as int],
        h == spec_lizard_fe_bytes(msg),
        sha_match == (h == *buf2),
        u8_32_as_nat(buf2) == fe51_as_canonical_nat(fe_j),
        mask_bit_set <==> cj.0,
        cj.0 ==> fe51_as_canonical_nat(fe_j) == cj.1,
    ensures
        (mask_bit_set && sha_match) == (cj.0 && spec_candidate_sha_consistent(cj.1)),
{
    if cj.0 {
        assert(u8_32_as_nat(buf2) == cj.1);

        // cj.1 < p() < pow2(256)
        assert(cj.1 < p()) by {
            p_gt_2();
            vstd::arithmetic::div_mod::lemma_mod_bound(fe51_as_nat(fe_j) as int, p() as int);
        };
        assert(cj.1 < pow2(256)) by {
            pow255_gt_19();
            lemma_pow2_strictly_increases(255, 256);
        };
        vstd::arithmetic::div_mod::lemma_small_mod(cj.1, pow2(256));

        // u8_32_from_nat(cj.1) == buf2 by injectivity
        let chosen = u8_32_from_nat(cj.1);
        crate::lemmas::common_lemmas::to_nat_lemmas::lemma_canonical_bytes_equal(buf2, &chosen);
        assert(*buf2 =~= chosen);

        // Connect exec msg to spec msg from spec_candidate_sha_consistent
        // spec_candidate_sha_consistent(r): let b = u8_32_from_nat(r); let m = Seq::new(16, |i| b[(8+i)]); b == spec_lizard_fe_bytes(m)
        // We have: chosen == *buf2, and msg[i] == buf2[(8+i)] for i in 0..16
        let spec_msg = Seq::new(16, |i: int| chosen[(8 + i) as int]);
        assert(msg =~= spec_msg) by {
            assert(msg.len() == 16);
            assert(spec_msg.len() == 16);
            assert forall|i: int| 0 <= i < 16 implies msg[i] == spec_msg[i] by {
                assert(msg[i] == buf2[(8 + i) as int]);
                assert(buf2[(8 + i) as int] == chosen[(8 + i) as int]);
            };
        };
        assert(spec_candidate_sha_consistent(cj.1) == (chosen == spec_lizard_fe_bytes(spec_msg)));
        assert(spec_candidate_sha_consistent(cj.1) == (*buf2 == spec_lizard_fe_bytes(msg)));
    }
}

/// `partial_sha_consistent_count(candidates, 8) == spec_sha_consistent_count(point)`.
///
/// Unrolls the recursive `partial_sha_consistent_count` 8 steps and shows
/// the result equals the explicit 8-term sum in `spec_sha_consistent_count`.
/// Used after the decode loop to conclude `n_found == spec_sha_consistent_count(point)`.
#[verifier::spinoff_prover]
pub proof fn lemma_partial_count_full(point: crate::edwards::EdwardsPoint)
    requires
        is_well_formed_edwards_point(point),
    ensures
        partial_sha_consistent_count(spec_lizard_decode_candidates(point), 8)
            == spec_sha_consistent_count(point),
{
    let c = spec_lizard_decode_candidates(point);
    reveal_with_fuel(partial_sha_consistent_count, 9);

    assert(partial_sha_consistent_count(c, 0) == 0nat);

    assert(partial_sha_consistent_count(c, 1) == 0nat + if c[0].0 && spec_candidate_sha_consistent(
        c[0].1,
    ) {
        1nat
    } else {
        0nat
    });

    assert(partial_sha_consistent_count(c, 2) == partial_sha_consistent_count(c, 1) + if c[1].0
        && spec_candidate_sha_consistent(c[1].1) {
        1nat
    } else {
        0nat
    });

    assert(partial_sha_consistent_count(c, 3) == partial_sha_consistent_count(c, 2) + if c[2].0
        && spec_candidate_sha_consistent(c[2].1) {
        1nat
    } else {
        0nat
    });

    assert(partial_sha_consistent_count(c, 4) == partial_sha_consistent_count(c, 3) + if c[3].0
        && spec_candidate_sha_consistent(c[3].1) {
        1nat
    } else {
        0nat
    });

    assert(partial_sha_consistent_count(c, 5) == partial_sha_consistent_count(c, 4) + if c[4].0
        && spec_candidate_sha_consistent(c[4].1) {
        1nat
    } else {
        0nat
    });

    assert(partial_sha_consistent_count(c, 6) == partial_sha_consistent_count(c, 5) + if c[5].0
        && spec_candidate_sha_consistent(c[5].1) {
        1nat
    } else {
        0nat
    });

    assert(partial_sha_consistent_count(c, 7) == partial_sha_consistent_count(c, 6) + if c[6].0
        && spec_candidate_sha_consistent(c[6].1) {
        1nat
    } else {
        0nat
    });

    assert(partial_sha_consistent_count(c, 8) == partial_sha_consistent_count(c, 7) + if c[7].0
        && spec_candidate_sha_consistent(c[7].1) {
        1nat
    } else {
        0nat
    });
}

} // verus!
