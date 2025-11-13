use vstd::prelude::*;
use crate::backend::serial::u64::scalar::Scalar52;
use crate::specs::scalar_specs_u64::limbs_bounded;
use crate::specs::scalar_specs_u64::spec_mul_internal;

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
{
    // Construct the scalar 1 as our second scalar
    let one = Scalar52 { limbs: [1, 0, 0, 0, 0] };
    // Prove limbs_bounded(one)
    assert(1 < (1u64 << 52)) by (bit_vector);
    // Prove spec_mul_internal(self_scalar, one) == limbs
    // When multiplying by 1, the result should be the first scalar
    let product = spec_mul_internal(self_scalar, &one);
    // product[0] = self[0] * 1 = self[0]
    assert(product[0] == (self_scalar.limbs[0] as u128) * 1);
    // product[1] = self[0] * 0 + self[1] * 1 = self[1]
    assert(product[1] == (self_scalar.limbs[0] as u128) * 0 + (self_scalar.limbs[1] as u128) * 1);
    // product[2] = self[0] * 0 + self[1] * 0 + self[2] * 1 = self[2]
    assert(product[2] == ((self_scalar.limbs[0] as u128) * (0) + (self_scalar.limbs[1] as u128) * (0) + (self_scalar.limbs[2] as u128) * (1)) as u128);
    // product[3] = self[0] * 0 + self[1] * 0 + self[2] * 0 + self[3] * 1 = self[3]
    assert(product[3] == ((self_scalar.limbs[0] as u128) * (0) + (self_scalar.limbs[1] as u128) * (0) + (self_scalar.limbs[2] as u128) * (0) + (self_scalar.limbs[3] as u128) * (1)) as u128);
    // product[4] = self[0] * 0 + ... + self[4] * 1 = self[4]
    assert(product[4] == ((self_scalar.limbs[0] as u128) * (0) + (self_scalar.limbs[1] as u128) * (0) + (self_scalar.limbs[2] as u128) * (0) + (self_scalar.limbs[3] as u128) * (0) + (self_scalar.limbs[4] as u128) * (1)) as u128);
    // product[5..8] = 0 (since one's upper limbs are 0)
    assert(product[8] == ((self_scalar.limbs[4] as u128) * (0)) as u128);
    // Therefore product == limbs
    // Assert each element individually to help Verus prove array equality
    assert(&product =~= limbs);
    // We've proven the existential with witnesses self_scalar and one
}
}
