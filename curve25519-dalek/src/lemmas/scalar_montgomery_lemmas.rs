use crate::backend::serial::u64::scalar::Scalar52;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar52_specs::group_order;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar52_specs::limbs_bounded;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar52_specs::scalar52_to_nat;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar52_specs::spec_mul_internal;
use vstd::prelude::*;

verus! {

/// Lemma: A 9-limb array with first 5 limbs matching self and last 4 being 0
/// can be viewed as the product of self and 1
pub proof fn lemma_from_montgomery_is_product_with_one(self_scalar: &Scalar52, limbs: &[u128; 9])
    requires
        limbs_bounded(self_scalar),
        forall|j: int| #![auto] 0 <= j < 5 ==> limbs[j] == self_scalar.limbs[j] as u128,
        forall|j: int| #![auto] 5 <= j < 9 ==> limbs[j] == 0,
    ensures
        (exists|bounded1: &Scalar52, bounded2: &Scalar52|
            limbs_bounded(bounded1) && limbs_bounded(bounded2) && spec_mul_internal(
                bounded1,
                bounded2,
            ) == limbs),
        // Stronger postcondition: one of them is canonical (< group_order)
        (exists|bounded: &Scalar52, canonical: &Scalar52|
            limbs_bounded(bounded) && limbs_bounded(canonical) && scalar52_to_nat(&canonical)
                < group_order() && spec_mul_internal(bounded, canonical) == limbs),
{
    let one = Scalar52 { limbs: [1, 0, 0, 0, 0] };
    assert(1 < (1u64 << 52)) by (bit_vector);
    let product = spec_mul_internal(self_scalar, &one);
    assert(product[0] == (self_scalar.limbs[0] as u128) * 1);
    assert(product[1] == (self_scalar.limbs[0] as u128) * 0 + (self_scalar.limbs[1] as u128) * 1);
    assert(product[2] == ((self_scalar.limbs[0] as u128) * (0) + (self_scalar.limbs[1] as u128) * (
    0) + (self_scalar.limbs[2] as u128) * (1)) as u128);
    assert(product[3] == ((self_scalar.limbs[0] as u128) * (0) + (self_scalar.limbs[1] as u128) * (
    0) + (self_scalar.limbs[2] as u128) * (0) + (self_scalar.limbs[3] as u128) * (1)) as u128);
    assert(product[4] == ((self_scalar.limbs[0] as u128) * (0) + (self_scalar.limbs[1] as u128) * (
    0) + (self_scalar.limbs[2] as u128) * (0) + (self_scalar.limbs[3] as u128) * (0) + (
    self_scalar.limbs[4] as u128) * (1)) as u128);
    assert(product[8] == ((self_scalar.limbs[4] as u128) * (0)) as u128);
    assert(&product =~= limbs);
    // Establish that one is canonical: scalar52_to_nat([1,0,0,0,0]) = 1 < group_order()
    crate::lemmas::scalar_lemmas::lemma_one_bounded(one);
    crate::lemmas::scalar_lemmas::lemma_five_limbs_equals_to_nat(&one.limbs);
    assert(1 < group_order());
}

/// Lemma: If the second input to mul_internal is canonical, the product satisfies
/// the precondition for montgomery_reduce's canonicity postcondition.
///
/// This enables proving that montgomery_mul(a, b) produces a canonical result
/// when b is canonical (< group_order).
pub proof fn lemma_mul_internal_one_canonical(a: &Scalar52, b: &Scalar52)
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        scalar52_to_nat(b) < group_order(),
    ensures
        (exists|bounded: &Scalar52, canonical: &Scalar52|
            limbs_bounded(bounded) && limbs_bounded(canonical) && scalar52_to_nat(canonical)
                < group_order() && spec_mul_internal(bounded, canonical) == spec_mul_internal(
                a,
                b,
            )),
{
    // Provide explicit witness: bounded = a, canonical = b
    assert(limbs_bounded(a));
    assert(limbs_bounded(b));
    assert(scalar52_to_nat(b) < group_order());
    assert(spec_mul_internal(a, b) == spec_mul_internal(a, b));
}

/// Symmetric version: first argument is canonical
pub proof fn lemma_mul_internal_first_canonical(a: &Scalar52, b: &Scalar52)
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        scalar52_to_nat(a) < group_order(),
    ensures
        (exists|bounded: &Scalar52, canonical: &Scalar52|
            limbs_bounded(bounded) && limbs_bounded(canonical) && scalar52_to_nat(canonical)
                < group_order() && spec_mul_internal(bounded, canonical) == spec_mul_internal(
                a,
                b,
            )),
{
    // Provide explicit witness: bounded = b, canonical = a
    assert(limbs_bounded(b));
    assert(limbs_bounded(a));
    assert(scalar52_to_nat(a) < group_order());
    assert(spec_mul_internal(b, a) == spec_mul_internal(b, a));
    // Need commutativity: spec_mul_internal(a, b) == spec_mul_internal(b, a)
    assume(spec_mul_internal(a, b) == spec_mul_internal(b, a));  // TODO: prove commutativity
}

} // verus!
