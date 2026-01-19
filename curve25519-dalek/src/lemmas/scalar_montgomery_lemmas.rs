use crate::backend::serial::u64::scalar::Scalar52;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar52_specs::group_order;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar52_specs::limbs_bounded;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar52_specs::scalar52_to_nat;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar52_specs::spec_mul_internal;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar52_specs::limb_prod_bounded_u128;
use vstd::prelude::*;

verus! {

/// Lemma: A 9-limb array with first 5 limbs matching self and last 4 being 0
/// can be viewed as the product of self and 1
pub proof fn lemma_from_montgomery_is_product_with_one(self_scalar: &Scalar52, limbs: &[u128; 9])
    requires
        limb_prod_bounded_u128(self_scalar.limbs, self_scalar.limbs, 5),
        forall|j: int| #![auto] 0 <= j < 5 ==> limbs[j] == self_scalar.limbs[j] as u128,
        forall|j: int| #![auto] 5 <= j < 9 ==> limbs[j] == 0,
    ensures
        (exists|bounded1: &Scalar52, bounded2: &Scalar52|
            limb_prod_bounded_u128(bounded1.limbs, bounded2.limbs, 5) && spec_mul_internal(
                bounded1,
                bounded2,
            ) == limbs),
        // Stronger postcondition: one of them is canonical (< group_order)
        (exists|bounded: &Scalar52, canonical: &Scalar52|
            limb_prod_bounded_u128(bounded.limbs, canonical.limbs, 5) && scalar52_to_nat(&canonical)
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

} // verus!
