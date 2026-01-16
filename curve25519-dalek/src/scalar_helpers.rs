//! Helper functions for scalar operations in MODIFIED CODE
use crate::scalar::Scalar;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::specs::scalar52_specs::*;

#[allow(unused_imports)]
use crate::lemmas::common_lemmas::to_nat_lemmas::*;
#[allow(unused_imports)]
use crate::specs::core_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;

verus! {

// ============================================================================
// Core lemmas for Scalar::ZERO and Scalar::ONE
// ============================================================================
/// Lemma: bytes32_to_nat of all-zero bytes equals 0
pub proof fn lemma_bytes32_to_nat_zero()
    ensures
        bytes32_to_nat(&Scalar::ZERO.bytes) == 0,
{
    // 0 * x == 0 for all terms
    assert forall|i: nat| i < 32 implies (0nat) * #[trigger] pow2(i * 8) == 0 by {
        lemma_mul_basics(pow2(i * 8) as int);
    }
}

/// Lemma: bytes32_to_nat of ONE's bytes equals 1
pub proof fn lemma_bytes32_to_nat_one()
    ensures
        bytes32_to_nat(&Scalar::ONE.bytes) == 1,
{
    let bytes = Scalar::ONE.bytes;
    assert(bytes[0] == 1);
    // pow2(0) == 1
    lemma2_to64();
    // 0 * x == 0 for remaining terms
    assert forall|i: nat| 1 <= i < 32 implies (0nat) * #[trigger] pow2(i * 8) == 0 by {
        lemma_mul_basics(pow2(i * 8) as int);
    }
}

/// Combined lemma for ZERO: value is 0, less than L, and congruent to 0
pub proof fn lemma_scalar_zero_properties()
    ensures
        scalar_to_nat(&Scalar::ZERO) == 0,
        scalar_to_nat(&Scalar::ZERO) < group_order(),
        scalar_congruent_nat(&Scalar::ZERO, 0),
{
    lemma_bytes32_to_nat_zero();
    lemma_small_mod(0nat, group_order());
}

/// Combined lemma for ONE: value is 1, less than L, and congruent to 1
pub proof fn lemma_scalar_one_properties()
    ensures
        scalar_to_nat(&Scalar::ONE) == 1,
        scalar_to_nat(&Scalar::ONE) < group_order(),
        scalar_congruent_nat(&Scalar::ONE, 1),
{
    lemma_bytes32_to_nat_one();
    lemma_small_mod(1nat, group_order());
}

// ============================================================================
// Main helper functions
// ============================================================================
impl Scalar {
    /// Compute the product of all scalars in a slice.
    ///
    /// # Returns
    ///
    /// The product of all scalars modulo the group order.
    ///
    /// # Example
    ///
    /// ```
    /// # use curve25519_dalek::scalar::Scalar;
    /// let scalars = [
    ///     Scalar::from(2u64),
    ///     Scalar::from(3u64),
    ///     Scalar::from(5u64),
    /// ];
    ///
    /// let product = Scalar::product_of_slice(&scalars);
    /// assert_eq!(product, Scalar::from(30u64));
    /// ```
    #[allow(clippy::needless_range_loop, clippy::op_ref)]
    pub fn product_of_slice(scalars: &[Scalar]) -> (result: Scalar)
        ensures
            scalar_to_nat(&result) < group_order(),
            scalar_congruent_nat(&result, product_of_scalars(scalars@)),
    {
        let n = scalars.len();
        let mut acc = Scalar::ONE;

        proof {
            lemma_scalar_one_properties();
            assert(scalars@.subrange(0, 0) =~= Seq::<Scalar>::empty());
        }

        for i in 0..n
            invariant
                n == scalars.len(),
                scalar_to_nat(&acc) < group_order(),
                scalar_congruent_nat(&acc, product_of_scalars(scalars@.subrange(0, i as int))),
        {
            let _old_acc = acc;

            proof {
                // Inline: product extends by one element
                let sub = scalars@.subrange(0, (i + 1) as int);
                assert(sub.subrange(0, i as int) =~= scalars@.subrange(0, i as int));
            }

            acc = &acc * &scalars[i];

            proof {
                let L = group_order();
                let acc_val = bytes32_to_nat(&acc.bytes);
                let old_acc_val = bytes32_to_nat(&_old_acc.bytes);
                let scalar_val = bytes32_to_nat(&scalars[i as int].bytes);
                let prod_prev = product_of_scalars(scalars@.subrange(0, i as int));

                lemma_mul_mod_noop_general(old_acc_val as int, scalar_val as int, L as int);
                lemma_mul_mod_noop_general(prod_prev as int, scalar_val as int, L as int);
                lemma_mod_twice(prod_prev as int * scalar_val as int, L as int);
            }
        }

        proof {
            assert(scalars@.subrange(0, n as int) =~= scalars@);
        }

        acc
    }

    /// Compute the sum of all scalars in a slice.
    ///
    /// # Returns
    ///
    /// The sum of all scalars modulo the group order.
    ///
    /// # Example
    ///
    /// ```
    /// # use curve25519_dalek::scalar::Scalar;
    /// let scalars = [
    ///     Scalar::from(2u64),
    ///     Scalar::from(3u64),
    ///     Scalar::from(5u64),
    /// ];
    ///
    /// let sum = Scalar::sum_of_slice(&scalars);
    /// assert_eq!(sum, Scalar::from(10u64));
    /// ```
    #[allow(clippy::needless_range_loop, clippy::op_ref)]
    pub fn sum_of_slice(scalars: &[Scalar]) -> (result: Scalar)
        ensures
            scalar_to_nat(&result) < group_order(),
            scalar_congruent_nat(&result, sum_of_scalars(scalars@)),
    {
        let n = scalars.len();
        let mut acc = Scalar::ZERO;

        proof {
            lemma_scalar_zero_properties();
            assert(scalars@.subrange(0, 0) =~= Seq::<Scalar>::empty());
        }

        for i in 0..n
            invariant
                n == scalars.len(),
                scalar_to_nat(&acc) < group_order(),
                scalar_congruent_nat(&acc, sum_of_scalars(scalars@.subrange(0, i as int))),
        {
            let _old_acc = acc;

            proof {
                // Inline: sum extends by one element
                let sub = scalars@.subrange(0, (i + 1) as int);
                assert(sub.subrange(0, i as int) =~= scalars@.subrange(0, i as int));
            }

            acc = &acc + &scalars[i];

            proof {
                let L = group_order();
                let acc_val = bytes32_to_nat(&acc.bytes);
                let old_acc_val = bytes32_to_nat(&_old_acc.bytes);
                let scalar_val = bytes32_to_nat(&scalars[i as int].bytes);
                let sum_prev = sum_of_scalars(scalars@.subrange(0, i as int));

                lemma_mod_bound(old_acc_val as int + scalar_val as int, L as int);
                lemma_add_mod_noop(old_acc_val as int, scalar_val as int, L as int);
                lemma_add_mod_noop(sum_prev as int, scalar_val as int, L as int);
                lemma_mod_twice(sum_prev as int + scalar_val as int, L as int);
            }
        }

        proof {
            assert(scalars@.subrange(0, n as int) =~= scalars@);
        }

        acc
    }
}

// ============================================================================
// Lemmas for batch_invert verification
// ============================================================================

/// Lemma: Montgomery multiplication maintains partial product invariant
/// Proves that multiplying acc (which holds R * partial_product(scalars, i))
/// by tmp (which holds scalar[i] * R) gives R * partial_product(scalars, i+1)
pub proof fn lemma_montgomery_mul_partial_product(
    acc_before_val: nat,
    tmp_val: nat,
    acc_after_val: nat,
    scalars: Seq<Scalar>,
    i: int,
)
    requires
        0 <= i < scalars.len(),
        acc_before_val % group_order() == (montgomery_radix() * partial_product(scalars, i))
            % group_order(),
        tmp_val % group_order() == (bytes32_to_nat(&scalars[i].bytes) * montgomery_radix())
            % group_order(),
        (acc_after_val * montgomery_radix()) % group_order() == (acc_before_val * tmp_val)
            % group_order(),
    ensures
        acc_after_val % group_order() == (montgomery_radix() * partial_product(scalars, i + 1))
            % group_order(),
{
    let L = group_order();
    let R = montgomery_radix();
    let scalar_i = bytes32_to_nat(&scalars[i].bytes);

    // From postcondition of montgomery_mul:
    // (acc_after * R) % L == (acc_before * tmp) % L
    // We know:
    // acc_before % L == (R * partial_product(scalars, i)) % L
    // tmp % L == (scalar_i * R) % L

    // Goal: acc_after % L == (R * partial_product(scalars, i+1)) % L

    // By definition of partial_product:
    assert(partial_product(scalars, i + 1) == (partial_product(scalars, i) * scalar_i) % L);

    // Algebraic manipulation:
    // (acc_after * R) % L == (acc_before * tmp) % L
    //                     == ((R * partial_product(i)) * (scalar_i * R)) % L
    //                     == (R^2 * partial_product(i) * scalar_i) % L

    // Therefore:
    // acc_after % L == (R * partial_product(i) * scalar_i) % L
    //               == (R * (partial_product(i) * scalar_i)) % L
    //               == (R * partial_product(i+1)) % L

    // This requires modular arithmetic manipulation
    lemma_montgomery_mul_partial_product_arithmetic(
        acc_before_val,
        tmp_val,
        acc_after_val,
        partial_product(scalars, i),
        scalar_i,
        R,
        L,
    );
}

/// Helper lemma for modular arithmetic in montgomery_mul_partial_product
proof fn lemma_montgomery_mul_partial_product_arithmetic(
    acc_before: nat,
    tmp: nat,
    acc_after: nat,
    pp_i: nat,
    scalar_i: nat,
    R: nat,
    L: nat,
)
    requires
        L > 0,
        R > 0,
        acc_before % L == (R * pp_i) % L,
        tmp % L == (scalar_i * R) % L,
        (acc_after * R) % L == (acc_before * tmp) % L,
    ensures
        acc_after % L == (R * ((pp_i * scalar_i) % L)) % L,
{
    use vstd::arithmetic::mul::*;
    use vstd::arithmetic::div_mod::*;

    // Using modular arithmetic properties
    lemma_mul_mod_noop_general(acc_before as int, tmp as int, L as int);
    lemma_mul_mod_noop_general(R as int, pp_i as int, L as int);
    lemma_mul_mod_noop_general(scalar_i as int, R as int, L as int);
    lemma_mul_mod_noop_general(acc_after as int, R as int, L as int);
    lemma_mul_mod_noop_general(R as int, (pp_i * scalar_i) as int, L as int);
    lemma_mul_mod_noop_general(pp_i as int, scalar_i as int, L as int);
}

/// Lemma: Correctness of Montgomery inversion chain
/// Proves that montgomery_invert followed by from_montgomery produces the modular inverse
pub proof fn lemma_invert_chain(
    acc_before_val: nat,
    acc_after_invert_val: nat,
    final_acc_val: nat,
    P: nat,
)
    requires
        group_order() > 0,
        acc_before_val % group_order() == (montgomery_radix() * P) % group_order(),
        (acc_after_invert_val * acc_before_val) % group_order() == (montgomery_radix()
            * montgomery_radix()) % group_order(),
        (final_acc_val * montgomery_radix()) % group_order() == acc_after_invert_val
            % group_order(),
    ensures
        (final_acc_val * P) % group_order() == 1nat,
{
    use vstd::arithmetic::mul::*;
    use vstd::arithmetic::div_mod::*;
    use crate::lemmas::scalar_lemmas::lemma_montgomery_inverse;

    let L = group_order();
    let R = montgomery_radix();
    let R_inv = inv_montgomery_radix();

    // From montgomery_inverse lemma: (R * R_inv) % L == 1
    lemma_montgomery_inverse();

    // Algebraic steps:
    // We have:
    // 1. acc_before % L == (R * P) % L
    // 2. (acc_after_invert * acc_before) % L == (R * R) % L
    // 3. (final_acc * R) % L == acc_after_invert % L

    // From (3): acc_after_invert % L == (final_acc * R) % L
    // Substitute into (2): ((final_acc * R) * acc_before) % L == (R * R) % L
    // Using (1): ((final_acc * R) * (R * P)) % L == (R * R) % L
    //            (final_acc * R * R * P) % L == (R * R) % L
    //            (final_acc * P * R * R) % L == (R * R) % L

    // Multiply both sides by (R_inv * R_inv):
    // (final_acc * P * R * R * R_inv * R_inv) % L == (R * R * R_inv * R_inv) % L
    // (final_acc * P) % L == 1 % L

    // This algebraic manipulation needs modular arithmetic lemmas
    assume((final_acc_val * P) % L == 1nat);  // TODO: Complete algebraic proof
}

/// Lemma: Backward loop maintains is_inverse property
/// Proves that each element is replaced with its modular inverse
pub proof fn lemma_backward_loop_is_inverse(
    acc_before_val: nat,
    scratch_val: nat,
    result_m: nat,
    result: nat,
    original_inputs: Seq<Scalar>,
    i: int,
)
    requires
        0 <= i < original_inputs.len(),
        group_order() > 0,
        acc_before_val < group_order(),
        result_m < group_order(),
        result == result_m,
        scratch_val % group_order() == (montgomery_radix() * partial_product(original_inputs, i))
            % group_order(),
        (result_m * montgomery_radix()) % group_order() == (acc_before_val * scratch_val)
            % group_order(),
        (acc_before_val * partial_product(original_inputs, i + 1)) % group_order() == 1nat,
    ensures
        (bytes32_to_nat(&original_inputs[i].bytes) * result) % group_order() == 1nat,
{
    use vstd::arithmetic::div_mod::*;

    let L = group_order();
    let R = montgomery_radix();
    let scalar_i = bytes32_to_nat(&original_inputs[i].bytes);

    // From partial_product definition:
    // partial_product(i+1) == (partial_product(i) * scalar_i) % L

    // From preconditions:
    // (result_m * R) % L == (acc_before * scratch) % L
    // scratch % L == (R * partial_product(i)) % L
    // (acc_before * partial_product(i+1)) % L == 1

    // Algebraic manipulation to show: (scalar_i * result) % L == 1
    assume((scalar_i * result) % L == 1nat);  // TODO: Complete algebraic proof
}

/// Lemma: Backward loop maintains accumulator invariant
/// Proves that acc continues to represent the inverse of the remaining partial product
pub proof fn lemma_backward_loop_acc_invariant(
    acc_before_val: nat,
    input_val: nat,
    acc_after_val: nat,
    original_inputs: Seq<Scalar>,
    i: int,
)
    requires
        0 <= i < original_inputs.len(),
        group_order() > 0,
        acc_before_val < group_order(),
        input_val == bytes32_to_nat(&original_inputs[i].bytes),
        (acc_after_val * montgomery_radix()) % group_order() == (acc_before_val * input_val)
            % group_order(),
        (acc_before_val * partial_product(original_inputs, i + 1)) % group_order() == 1nat,
    ensures
        (acc_after_val * partial_product(original_inputs, i)) % group_order() == 1nat,
{
    use vstd::arithmetic::div_mod::*;

    let L = group_order();
    let R = montgomery_radix();

    // From partial_product definition:
    // partial_product(i+1) == (partial_product(i) * input_val) % L

    // Goal: (acc_after * partial_product(i)) % L == 1

    // From preconditions:
    // (acc_after * R) % L == (acc_before * input_val) % L
    // (acc_before * partial_product(i+1)) % L == 1
    // (acc_before * (partial_product(i) * input_val)) % L == 1

    // Therefore: (acc_before * partial_product(i) * input_val) % L == 1
    // We have: (acc_after * R) % L == (acc_before * input_val) % L

    // Algebraic manipulation shows: (acc_after * partial_product(i)) % L == 1
    assume((acc_after_val * partial_product(original_inputs, i)) % L == 1nat);  // TODO: Complete algebraic proof
}

} // verus!
