//! Lemmas for Edwards curve scalar multiplication
//!
//! This module contains proofs about scalar multiplication on Edwards curve points.
//!
//! ## Lemmas
//!
//! - `lemma_edwards_scalar_mul_pow2_succ`: Scalar multiplication by 2^(k+1) unfolds to doubling.
#[cfg(verus_keep_ghost)]
use crate::lemmas::common_lemmas::pow_lemmas::{lemma_pow2_even, pow2_MUL_div};
#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::{edwards_double, edwards_scalar_mul};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{lemma2_to64, lemma_pow2_pos, pow2};
use vstd::prelude::*;

verus! {

/// Lemma: scalar multiplication by a power-of-two exponent unfolds to a doubling.
///
/// For any point P and exponent k ≥ 0:
///   [2^(k+1)]P = double([2^k]P)
///
/// This is used to prove `mul_by_pow_2` correct by showing each doubling step
/// computes the next power-of-two multiple.
pub proof fn lemma_edwards_scalar_mul_pow2_succ(point_affine: (nat, nat), k: nat)
    ensures
        edwards_scalar_mul(point_affine, pow2(k + 1)) == {
            let half = edwards_scalar_mul(point_affine, pow2(k));
            edwards_double(half.0, half.1)
        },
{
    // Unfold one step of scalar multiplication at n = 2^(k+1).
    reveal_with_fuel(edwards_scalar_mul, 1);

    // pow2(k+1) is positive and even.
    assert(pow2(k + 1) != 0 && pow2(k + 1) % 2 == 0) by {
        lemma_pow2_pos(k + 1);
        lemma_pow2_even(k + 1);
    }

    // pow2(k+1) / 2 == pow2(k).
    assert(pow2(k + 1) / 2 == pow2(k)) by {
        pow2_MUL_div(1, k + 1, 1);  // (1 * pow2(k+1)) / pow2(1) == 1 * pow2(k)
        assert(pow2(1) == 2) by {
            lemma2_to64();
        }
    }

    // Since pow2(k+1) is even and nonzero, it cannot be 1.
    assert(pow2(k + 1) != 1) by {
        assert(1nat % 2 == 1) by (compute);
    }

    // Now the even branch applies.
    assert(edwards_scalar_mul(point_affine, pow2(k + 1)) == {
        let half = edwards_scalar_mul(point_affine, (pow2(k + 1) / 2) as nat);
        edwards_double(half.0, half.1)
    });
}

} // verus!
