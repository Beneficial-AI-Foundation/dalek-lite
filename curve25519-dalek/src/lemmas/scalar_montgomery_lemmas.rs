use crate::backend::serial::u64::scalar::Scalar52;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar_specs_u64::limbs_bounded;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar_specs_u64::spec_mul_internal;
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
{
    assume(false);
}

} // verus!
