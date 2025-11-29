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
            ) == *limbs),
{
    // Construct the witness: self_scalar * 1
    let one = Scalar52 { limbs: [1, 0, 0, 0, 0] };

    // Establish facts about one.limbs values
    assert(one.limbs[0] == 1u64);
    assert(one.limbs[1] == 0u64);
    assert(one.limbs[2] == 0u64);
    assert(one.limbs[3] == 0u64);
    assert(one.limbs[4] == 0u64);

    // Show that 'one' is bounded (all limbs < 2^52)
    // limbs_bounded requires: forall|i: int| 0 <= i < 5 ==> s.limbs[i] < (1u64 << 52)
    // Use assert by (compute_only) for bit shift computations
    assert((1u64 << 52) == 0x10000000000000u64) by (compute_only);
    assert(1u64 < (1u64 << 52)) by (compute_only);
    assert(0u64 < (1u64 << 52)) by (compute_only);

    assert(one.limbs[0] == 1u64);
    assert(one.limbs[1] == 0u64);
    assert(one.limbs[2] == 0u64);
    assert(one.limbs[3] == 0u64);
    assert(one.limbs[4] == 0u64);

    assert(one.limbs[0] < (1u64 << 52));
    assert(one.limbs[1] < (1u64 << 52));
    assert(one.limbs[2] < (1u64 << 52));
    assert(one.limbs[3] < (1u64 << 52));
    assert(one.limbs[4] < (1u64 << 52));

    assert(limbs_bounded(&one)) by {
        assert forall|i: int| 0 <= i < 5 implies one.limbs[i] < (1u64 << 52) by {
            if i == 0 {
                assert(one.limbs[0] < (1u64 << 52));
            } else if i == 1 {
                assert(one.limbs[1] < (1u64 << 52));
            } else if i == 2 {
                assert(one.limbs[2] < (1u64 << 52));
            } else if i == 3 {
                assert(one.limbs[3] < (1u64 << 52));
            } else {
                assert(one.limbs[4] < (1u64 << 52));
            }
        }
    }

    // Compute spec_mul_internal(self_scalar, one)
    let result = spec_mul_internal(self_scalar, &one);

    // The spec definition is:
    // result[0] = ((a.limbs[0] as u128) * (b.limbs[0] as u128)) as u128
    // = (self_scalar.limbs[0] as u128) * (one.limbs[0] as u128)
    // = (self_scalar.limbs[0] as u128) * (1 as u128)
    // = self_scalar.limbs[0] as u128
    // = limbs[0]  (by precondition)

    // First, assert what the result elements are according to the definition
    // Using the exact form from spec_mul_internal with substituted b values

    // result[0] = a[0] * b[0] = a[0] * 1 = a[0]
    assert(result[0] == ((self_scalar.limbs[0] as u128) * (one.limbs[0] as u128)) as u128);

    // result[1] = a[0]*b[1] + a[1]*b[0] = a[0]*0 + a[1]*1 = a[1]
    assert(result[1] == ((self_scalar.limbs[0] as u128) * (one.limbs[1] as u128)
        + (self_scalar.limbs[1] as u128) * (one.limbs[0] as u128)) as u128);

    // result[2]
    assert(result[2] == ((self_scalar.limbs[0] as u128) * (one.limbs[2] as u128)
        + (self_scalar.limbs[1] as u128) * (one.limbs[1] as u128)
        + (self_scalar.limbs[2] as u128) * (one.limbs[0] as u128)) as u128);

    // result[3]
    assert(result[3] == ((self_scalar.limbs[0] as u128) * (one.limbs[3] as u128)
        + (self_scalar.limbs[1] as u128) * (one.limbs[2] as u128)
        + (self_scalar.limbs[2] as u128) * (one.limbs[1] as u128)
        + (self_scalar.limbs[3] as u128) * (one.limbs[0] as u128)) as u128);

    // result[4]
    assert(result[4] == ((self_scalar.limbs[0] as u128) * (one.limbs[4] as u128)
        + (self_scalar.limbs[1] as u128) * (one.limbs[3] as u128)
        + (self_scalar.limbs[2] as u128) * (one.limbs[2] as u128)
        + (self_scalar.limbs[3] as u128) * (one.limbs[1] as u128)
        + (self_scalar.limbs[4] as u128) * (one.limbs[0] as u128)) as u128);

    // result[5]
    assert(result[5] == ((self_scalar.limbs[1] as u128) * (one.limbs[4] as u128)
        + (self_scalar.limbs[2] as u128) * (one.limbs[3] as u128)
        + (self_scalar.limbs[3] as u128) * (one.limbs[2] as u128)
        + (self_scalar.limbs[4] as u128) * (one.limbs[1] as u128)) as u128);

    // result[6]
    assert(result[6] == ((self_scalar.limbs[2] as u128) * (one.limbs[4] as u128)
        + (self_scalar.limbs[3] as u128) * (one.limbs[3] as u128)
        + (self_scalar.limbs[4] as u128) * (one.limbs[2] as u128)) as u128);

    // result[7]
    assert(result[7] == ((self_scalar.limbs[3] as u128) * (one.limbs[4] as u128)
        + (self_scalar.limbs[4] as u128) * (one.limbs[3] as u128)) as u128);

    // result[8]
    assert(result[8] == ((self_scalar.limbs[4] as u128) * (one.limbs[4] as u128)) as u128);

    // Now simplify using one.limbs[0] = 1 and one.limbs[1..4] = 0
    // For result[0]: (a*1) as u128 = a (when a is already u128 and fits)
    assert((one.limbs[0] as u128) == 1u128);
    assert(((self_scalar.limbs[0] as u128) * 1u128) as u128 == (self_scalar.limbs[0] as u128));
    assert(result[0] == self_scalar.limbs[0] as u128);

    // For result[1]: (a*0 + b*1) as u128 = b
    assert((one.limbs[1] as u128) == 0u128);
    assert((self_scalar.limbs[0] as u128) * 0u128 == 0u128);
    assert(((self_scalar.limbs[1] as u128) * 1u128) as u128 == (self_scalar.limbs[1] as u128));
    assert(result[1] == self_scalar.limbs[1] as u128);

    // For result[2]: a[0]*b[2] + a[1]*b[1] + a[2]*b[0] = 0 + 0 + a[2]
    assert((one.limbs[2] as u128) == 0u128);
    assert((self_scalar.limbs[0] as u128) * 0u128 == 0u128);
    assert((self_scalar.limbs[1] as u128) * 0u128 == 0u128);
    assert(((self_scalar.limbs[2] as u128) * 1u128) as u128 == (self_scalar.limbs[2] as u128));
    assert(result[2] == self_scalar.limbs[2] as u128);

    // For result[3]: a[0]*b[3] + a[1]*b[2] + a[2]*b[1] + a[3]*b[0] = 0 + 0 + 0 + a[3]
    assert((one.limbs[3] as u128) == 0u128);
    assert((self_scalar.limbs[0] as u128) * 0u128 == 0u128);
    assert((self_scalar.limbs[1] as u128) * 0u128 == 0u128);
    assert((self_scalar.limbs[2] as u128) * 0u128 == 0u128);
    assert(((self_scalar.limbs[3] as u128) * 1u128) as u128 == (self_scalar.limbs[3] as u128));
    assert(result[3] == self_scalar.limbs[3] as u128);

    // For result[4]: a[0]*b[4] + a[1]*b[3] + a[2]*b[2] + a[3]*b[1] + a[4]*b[0] = 0+0+0+0+a[4]
    assert((one.limbs[4] as u128) == 0u128);
    assert((self_scalar.limbs[0] as u128) * 0u128 == 0u128);
    assert((self_scalar.limbs[1] as u128) * 0u128 == 0u128);
    assert((self_scalar.limbs[2] as u128) * 0u128 == 0u128);
    assert((self_scalar.limbs[3] as u128) * 0u128 == 0u128);
    assert(((self_scalar.limbs[4] as u128) * 1u128) as u128 == (self_scalar.limbs[4] as u128));
    assert(result[4] == self_scalar.limbs[4] as u128);

    // For result[5]: a[1]*b[4] + a[2]*b[3] + a[3]*b[2] + a[4]*b[1] = 0+0+0+0 = 0
    assert((self_scalar.limbs[1] as u128) * 0u128 == 0u128);
    assert((self_scalar.limbs[2] as u128) * 0u128 == 0u128);
    assert((self_scalar.limbs[3] as u128) * 0u128 == 0u128);
    assert((self_scalar.limbs[4] as u128) * 0u128 == 0u128);
    assert(result[5] == 0u128);

    // For result[6]: a[2]*b[4] + a[3]*b[3] + a[4]*b[2] = 0+0+0 = 0
    assert(result[6] == 0u128);

    // For result[7]: a[3]*b[4] + a[4]*b[3] = 0+0 = 0
    assert(result[7] == 0u128);

    // For result[8]: a[4]*b[4] = 0
    assert(result[8] == 0u128);

    // By precondition, limbs matches
    assert(limbs[0] == self_scalar.limbs[0] as u128);
    assert(limbs[1] == self_scalar.limbs[1] as u128);
    assert(limbs[2] == self_scalar.limbs[2] as u128);
    assert(limbs[3] == self_scalar.limbs[3] as u128);
    assert(limbs[4] == self_scalar.limbs[4] as u128);
    assert(limbs[5] == 0u128);
    assert(limbs[6] == 0u128);
    assert(limbs[7] == 0u128);
    assert(limbs[8] == 0u128);

    // Check result equals limbs element by element
    assert(result[0] == limbs[0]);
    assert(result[1] == limbs[1]);
    assert(result[2] == limbs[2]);
    assert(result[3] == limbs[3]);
    assert(result[4] == limbs[4]);
    assert(result[5] == limbs[5]);
    assert(result[6] == limbs[6]);
    assert(result[7] == limbs[7]);
    assert(result[8] == limbs[8]);

    // Therefore result =~= *limbs
    assert(result =~= *limbs);

    // First verify spec_mul_internal(self_scalar, &one) =~= *limbs
    assert(spec_mul_internal(self_scalar, &one) =~= *limbs);

    // Assert each part of the witness conjunction
    assert(limbs_bounded(self_scalar));
    assert(limbs_bounded(&one));

    // For arrays, extensional equality and structural equality are equivalent
    // Call the axiom to make sure the SMT solver knows this
    vstd::array::axiom_array_ext_equal::<u128, 9>(spec_mul_internal(self_scalar, &one), *limbs);

    // Assert structural equality using assert_by that relies on the extensional equality
    assert(spec_mul_internal(self_scalar, &one) == *limbs) by {
        assert(spec_mul_internal(self_scalar, &one) =~= *limbs);
    }
}

} // verus!
