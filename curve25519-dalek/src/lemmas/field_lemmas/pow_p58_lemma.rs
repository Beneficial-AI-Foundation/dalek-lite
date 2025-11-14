//! Lemma for proving pow_p58: x^(2^252-3)
//!
//! This lemma proves that pow_p58 correctly computes x^((p-5)/8) = x^(2^252-3).
//!
//! The computation is straightforward:
//! 1. Start with t19 = x^(2^250-1) from pow22501
//! 2. Square twice: t20 = t19^4 = x^(4*(2^250-1)) = x^(2^252-4)
//! 3. Multiply by x: t21 = x * t20 = x^(1 + 2^252-4) = x^(2^252-3)
//!
//! This follows the same direct proof pattern as pow22501_t3_lemma.
//!
#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use crate::lemmas::common_lemmas::div_mod_lemmas::*;
use crate::lemmas::common_lemmas::mul_lemmas::*;
use crate::lemmas::common_lemmas::pow_lemmas::*;
use crate::specs::field_specs_u64::*;

verus! {

/// Proves that pow_p58 correctly computes x^(2^252-3)
///
/// # Arguments
/// * `self_limbs` - The base value x
/// * `t19_limbs` - x^(2^250-1) (from pow22501)
/// * `t20_limbs` - Result of t19.pow2k(2) = x^(2^252-4)
/// * `t21_limbs` - Result of self * t20 = x^(2^252-3)
///
/// # Preconditions
/// * t19 = x^(2^250-1) mod p
/// * t20 = t19^4 mod p (from pow2k(2))
/// * t21 = self * t20 mod p
///
/// # Postconditions
/// * as_nat(t21_limbs) % p() == pow(as_nat(self_limbs) as int, (pow2(252) - 3) as nat) % p()
pub proof fn lemma_pow_p58_prove(
    self_limbs: [u64; 5],
    t19_limbs: [u64; 5],
    t20_limbs: [u64; 5],
    t21_limbs: [u64; 5],
)
    requires
// t19 = x^(2^250-1) from pow22501

        as_nat(t19_limbs) % p() == pow(as_nat(self_limbs) as int, (pow2(250) - 1) as nat) as nat
            % p(),
        // t20 = t19^4 (from pow2k(2))
        as_nat(t20_limbs) % p() == pow(as_nat(t19_limbs) as int, pow2(2)) as nat % p(),
        // t21 = self * t20
        as_nat(t21_limbs) % p() == (as_nat(self_limbs) * as_nat(t20_limbs)) % p(),
    ensures
        as_nat(t21_limbs) % p() == pow(as_nat(self_limbs) as int, (pow2(252) - 3) as nat) as nat
            % p(),
{
    let base = as_nat(self_limbs) as int;

    assert(p() > 0) by {
        pow255_gt_19();
    }

    // ========================================================================
    // Prove t20 = x^(2^252-4)
    // ========================================================================
    // From postcondition: t20 = t19^4 = (x^(2^250-1))^4
    // By lemma_pow_multiplies: (x^a)^b = x^(a*b)
    // So t20 = x^(4*(2^250-1))
    // And we need to show: 4*(2^250-1) = 2^252-4

    let exp_250_m1 = (pow2(250) - 1) as nat;
    let exp_252_m4 = (pow2(252) - 4) as nat;
    let exp_252_m3 = (pow2(252) - 3) as nat;

    // Prove pow(base, exp_250_m1) >= 0
    assert(pow(base, exp_250_m1) >= 0) by {
        lemma_pow_nonnegative(base, exp_250_m1);
    }

    // Prove pow(t19_limbs, 4) >= 0
    let t19_val = as_nat(t19_limbs) as int;
    assert(t19_val >= 0);
    assert(pow(t19_val, 4) >= 0) by {
        lemma_pow_even_nonnegative(t19_val, 2);
    }

    // Prove pow(base, 4 * exp_250_m1) >= 0
    assert(pow(base, 4 * exp_250_m1) >= 0) by {
        lemma_pow_nonnegative(base, 4 * exp_250_m1);
    }

    // Apply power congruence: since t19 ≡ x^(2^250-1) (mod p), then t19^4 ≡ (x^(2^250-1))^4 (mod p)
    assert((pow(t19_val, 4) % (p() as int)) as nat == (pow(pow(base, exp_250_m1), 4) % (
    p() as int)) as nat) by {
        lemma_pow_mod_congruent(t19_val, pow(base, exp_250_m1), 4, p() as int);
    }

    // Apply power multiplication: (x^a)^b = x^(a*b)
    assert(pow(pow(base, exp_250_m1), 4) == pow(base, exp_250_m1 * 4)) by {
        lemma_pow_multiplies(base, exp_250_m1, 4);
    }

    // Prove the arithmetic: 4 * (2^250 - 1) = 2^252 - 4
    assert(pow2(2) == 4) by {
        lemma2_to64();
    }
    assert(pow2(252) == pow2(2) * pow2(250)) by {
        lemma_pow2_adds(2, 250);
    }
    assert(4 * pow2(250) == pow2(252));

    // Step 2: Prove 2^250 >= 1 and 2^252 >= 4
    assert(pow2(250) >= 1) by {
        lemma_pow2_pos(250);
    }
    assert(pow2(252) >= 4) by {
        lemma_pow2_pos(252);
        assert(pow2(252) >= pow2(2)) by {
            lemma_pow2_strictly_increases(2, 252);
        }
    }

    // Step 3: Use distributive property in int, then cast to nat
    assert(4 * exp_250_m1 == exp_252_m4) by {
        // Use distributive property: 4 * (2^250 - 1) = 4 * 2^250 - 4 = 2^252 - 4
        let a_int = pow2(250) as int - 1;
        let b_int = pow2(252) as int - 4;

        assert(4 * a_int == b_int) by {
            lemma_mul_is_distributive_sub(4, pow2(250) as int, 1);
            assert(4 * (pow2(250) as int - 1) == 4 * pow2(250) as int - 4);
            assert(4 * pow2(250) as int == pow2(252) as int);
        }

        // Cast to nat (both are non-negative)
        assert(a_int >= 0);
        assert(b_int >= 0);
        assert((4 * a_int) as nat == 4 * (a_int as nat));
        assert(exp_250_m1 == a_int as nat);
        assert(exp_252_m4 == b_int as nat);
    }

    // Therefore t20 = x^(2^252-4) mod p
    assert(as_nat(t20_limbs) % p() == pow(base, exp_252_m4) as nat % p());

    // ========================================================================
    // Prove t21 = x^(2^252-3)
    // ========================================================================
    // From postcondition: t21 = x * t20 = x^1 * x^(2^252-4)
    // By lemma_pow_adds: x^a * x^b = x^(a+b)
    // So t21 = x^(1 + (2^252-4)) = x^(2^252-3)

    // Establish self = x^1
    assert(pow(base, 1) == base) by {
        lemma_pow1(base);
    }
    assert(pow(base, 1) as nat == as_nat(self_limbs));

    // Expand multiplication modulo: (a * b) % p = ((a % p) * (b % p)) % p
    assert(as_nat(t21_limbs) % p() == ((as_nat(self_limbs) % p()) * (as_nat(t20_limbs) % p()))
        % p()) by {
        lemma_mul_mod_noop_general(as_nat(self_limbs) as int, as_nat(t20_limbs) as int, p() as int);
    }

    // Substitute known powers: self = x^1, t20 = x^(2^252-4)
    assert(as_nat(t21_limbs) % p() == ((pow(base, 1) as nat % p()) * (pow(base, exp_252_m4) as nat
        % p())) % p());

    // Apply modular multiplication lemma: ((a % p) * (b % p)) % p = (a * b) % p
    assert(as_nat(t21_limbs) % p() == (pow(base, 1) as nat * pow(base, exp_252_m4) as nat) % p())
        by {
        lemma_mul_mod_noop_general(
            pow(base, 1) as nat as int,
            pow(base, exp_252_m4) as nat as int,
            p() as int,
        );
    }

    // Prove x^1 * x^(2^252-4) = x^(1 + 2^252-4) in int
    assert(pow(base, 1) * pow(base, exp_252_m4) == pow(base, 1 + exp_252_m4)) by {
        lemma_pow_adds(base, 1, exp_252_m4);
    }

    // Prove the arithmetic: 1 + (2^252 - 4) = 2^252 - 3
    assert(1 + exp_252_m4 == exp_252_m3) by {
        // Simple arithmetic: 1 + (n - 4) = n - 3
        // We just need pow2(252) >= 4
        assert(pow2(252) >= 4) by {
            lemma_pow2_pos(252);  // 2^252 > 0
            assert(pow2(2) == 4);
            // 2^252 = 2^2 * 2^250 = 4 * 2^250, so definitely >= 4
            assert(pow2(252) == pow2(2) * pow2(250)) by {
                lemma_pow2_adds(2, 250);
            }
        }
    }

    // Convert to nat: casting preserves multiplication for non-negative values
    assert(pow(base, exp_252_m3) >= 0) by {
        lemma_pow_nonnegative(base, exp_252_m3);
    }
    assert(pow(base, 1) as nat * pow(base, exp_252_m4) as nat == (pow(base, 1) * pow(
        base,
        exp_252_m4,
    )) as nat);
    assert(pow(base, 1) as nat * pow(base, exp_252_m4) as nat == pow(base, exp_252_m3) as nat);

    assert(as_nat(t21_limbs) % p() == pow(base, exp_252_m3) as nat % p());
}

} // verus!
