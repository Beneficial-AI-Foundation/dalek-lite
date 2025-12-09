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
use crate::specs::scalar_specs_u64::*;

#[allow(unused_imports)]
use crate::specs::scalar_specs::*;

verus! {

// ============================================================================
// Core lemmas for Scalar::ZERO and Scalar::ONE
// ============================================================================
/// Lemma: bytes_to_nat of all-zero bytes equals 0
pub proof fn lemma_bytes_to_nat_zero()
    ensures
        bytes_to_nat(&Scalar::ZERO.bytes) == 0,
{
    let bytes = Scalar::ZERO.bytes;
    // Help Verus see that all bytes are 0
    assert forall|i: int| 0 <= i < 32 implies #[trigger] bytes[i] == 0 by {}
    // 0 * x == 0 for all terms
    assert forall|i: nat| i < 32 implies (0nat) * #[trigger] pow2(i * 8) == 0 by {
        lemma_mul_basics(pow2(i * 8) as int);
    }
}

/// Lemma: bytes_to_nat of ONE's bytes equals 1
pub proof fn lemma_bytes_to_nat_one()
    ensures
        bytes_to_nat(&Scalar::ONE.bytes) == 1,
{
    let bytes = Scalar::ONE.bytes;
    // Help Verus see the byte values
    assert(bytes[0] == 1);
    assert forall|i: int| 1 <= i < 32 implies #[trigger] bytes[i] == 0 by {}
    // pow2(0) == 1
    lemma2_to64();
    // 1 * 1 == 1 and 0 * x == 0
    lemma_mul_basics(1int);
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
    lemma_bytes_to_nat_zero();
    lemma_small_mod(0nat, group_order());
}

/// Combined lemma for ONE: value is 1, less than L, and congruent to 1
pub proof fn lemma_scalar_one_properties()
    ensures
        scalar_to_nat(&Scalar::ONE) == 1,
        scalar_to_nat(&Scalar::ONE) < group_order(),
        scalar_congruent_nat(&Scalar::ONE, 1),
{
    lemma_bytes_to_nat_one();
    lemma_small_mod(1nat, group_order());
}

// ============================================================================
// Lemmas for sum_of_scalars and product_of_scalars
// ============================================================================
/// Lemma: subrange(0, 0) equals empty sequence
pub proof fn lemma_subrange_0_0_empty<T>(seq: Seq<T>)
    ensures
        seq.subrange(0, 0) == Seq::<T>::empty(),
{
    assert(seq.subrange(0, 0) =~= Seq::<T>::empty());
}

/// Lemma: Extending sum by one element
pub proof fn lemma_sum_of_scalars_extend(scalars: Seq<Scalar>, i: int)
    requires
        0 <= i < scalars.len(),
    ensures
        sum_of_scalars(scalars.subrange(0, i + 1)) == (sum_of_scalars(scalars.subrange(0, i))
            + bytes_to_nat(&scalars[i].bytes)) % group_order(),
{
    let sub = scalars.subrange(0, i + 1);
    assert(sub.subrange(0, i) =~= scalars.subrange(0, i));
}

/// Lemma: Extending product by one element
pub proof fn lemma_product_of_scalars_extend(scalars: Seq<Scalar>, i: int)
    requires
        0 <= i < scalars.len(),
    ensures
        product_of_scalars(scalars.subrange(0, i + 1)) == (product_of_scalars(
            scalars.subrange(0, i),
        ) * bytes_to_nat(&scalars[i].bytes)) % group_order(),
{
    let sub = scalars.subrange(0, i + 1);
    assert(sub.subrange(0, i) =~= scalars.subrange(0, i));
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
            lemma_subrange_0_0_empty(scalars@);
            // product_of_scalars(empty) == 1 by definition
            assert(product_of_scalars(scalars@.subrange(0, 0)) == 1);
        }

        for i in 0..n
            invariant
                n == scalars.len(),
                scalar_to_nat(&acc) < group_order(),
                scalar_congruent_nat(&acc, product_of_scalars(scalars@.subrange(0, i as int))),
        {
            let _old_acc = acc;

            proof {
                lemma_product_of_scalars_extend(scalars@, i as int);
            }

            acc = &acc * &scalars[i];

            proof {
                let L = group_order();
                let acc_val = bytes_to_nat(&acc.bytes);
                let old_acc_val = bytes_to_nat(&_old_acc.bytes);
                let scalar_val = bytes_to_nat(&scalars[i as int].bytes);
                let prod_prev = product_of_scalars(scalars@.subrange(0, i as int));
                let prod_next = product_of_scalars(scalars@.subrange(0, (i + 1) as int));

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
            lemma_subrange_0_0_empty(scalars@);
            // sum_of_scalars(empty) == 0 by definition
            assert(sum_of_scalars(scalars@.subrange(0, 0)) == 0);
        }

        for i in 0..n
            invariant
                n == scalars.len(),
                scalar_to_nat(&acc) < group_order(),
                scalar_congruent_nat(&acc, sum_of_scalars(scalars@.subrange(0, i as int))),
        {
            let _old_acc = acc;

            proof {
                lemma_sum_of_scalars_extend(scalars@, i as int);
            }

            acc = &acc + &scalars[i];

            proof {
                let L = group_order();
                let acc_val = bytes_to_nat(&acc.bytes);
                let old_acc_val = bytes_to_nat(&_old_acc.bytes);
                let scalar_val = bytes_to_nat(&scalars[i as int].bytes);
                let sum_prev = sum_of_scalars(scalars@.subrange(0, i as int));
                let sum_next = sum_of_scalars(scalars@.subrange(0, (i + 1) as int));

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

} // verus!
