//! Lemma for proving t19 = x^(2^250-1) in pow22501
//!
//! This lemma proves the complete exponentiation chain in pow22501:
//! Starting from x^11 (t3), we compute through a series of squaring and multiplication
//! operations to reach x^(2^250-1) (t19).
//!
//! The computation follows a pattern of building larger exponents:
//! - t4 = x^22         (square of t3)
//! - t5 = x^31         (= x^(2^5-1))
//! - t7 = x^(2^10-1)
//! - t9 = x^(2^20-1)
//! - t11 = x^(2^40-1)
//! - t13 = x^(2^50-1)
//! - t15 = x^(2^100-1)
//! - t17 = x^(2^200-1)
//! - t19 = x^(2^250-1)
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

/// Proves that t19 = x^(2^250-1) given the complete computation chain from pow22501
///
/// # Arguments
/// * `self_limbs` - The base value x
/// * `t0_limbs` - x^2
/// * `t1_limbs` - x^8
/// * `t2_limbs` - x^9
/// * `t3_limbs` - x^11
/// * `t4_limbs` - x^22 (result of t3.square())
/// * `t5_limbs` - x^31 = x^(2^5-1) (result of t2 * t4)
/// * `t6_limbs` - x^((2^5-1)*2^5) (result of t5.pow2k(5))
/// * `t7_limbs` - x^(2^10-1) (result of t6 * t5)
/// * `t8_limbs` - x^((2^10-1)*2^10) (result of t7.pow2k(10))
/// * `t9_limbs` - x^(2^20-1) (result of t8 * t7)
/// * `t10_limbs` - x^((2^20-1)*2^20) (result of t9.pow2k(20))
/// * `t11_limbs` - x^(2^40-1) (result of t10 * t9)
/// * `t12_limbs` - x^((2^40-1)*2^10) (result of t11.pow2k(10))
/// * `t13_limbs` - x^(2^50-1) (result of t12 * t7)
/// * `t14_limbs` - x^((2^50-1)*2^50) (result of t13.pow2k(50))
/// * `t15_limbs` - x^(2^100-1) (result of t14 * t13)
/// * `t16_limbs` - x^((2^100-1)*2^100) (result of t15.pow2k(100))
/// * `t17_limbs` - x^(2^200-1) (result of t16 * t15)
/// * `t18_limbs` - x^((2^200-1)*2^50) (result of t17.pow2k(50))
/// * `t19_limbs` - x^(2^250-1) (result of t18 * t13)
///
/// # Preconditions
/// * Limbs are properly bounded (< 2^54)
/// * Each step follows the correct field operation postconditions
/// * t0, t1, t2, t3 satisfy the t3 checkpoint properties
///
/// # Postconditions
/// * as_nat(t19_limbs) % p() == pow(as_nat(self_limbs) as int, (pow2(250) - 1) as nat) as nat % p()
/// * Also proves all intermediate values through the chain
pub proof fn lemma_pow22501_prove_t19(
    self_limbs: [u64; 5],
    t0_limbs: [u64; 5],
    t1_limbs: [u64; 5],
    t2_limbs: [u64; 5],
    t3_limbs: [u64; 5],
    t4_limbs: [u64; 5],
    t5_limbs: [u64; 5],
    t6_limbs: [u64; 5],
    t7_limbs: [u64; 5],
    t8_limbs: [u64; 5],
    t9_limbs: [u64; 5],
    t10_limbs: [u64; 5],
    t11_limbs: [u64; 5],
    t12_limbs: [u64; 5],
    t13_limbs: [u64; 5],
    t14_limbs: [u64; 5],
    t15_limbs: [u64; 5],
    t16_limbs: [u64; 5],
    t17_limbs: [u64; 5],
    t18_limbs: [u64; 5],
    t19_limbs: [u64; 5],
)
    requires
// Limbs are bounded

        forall|i: int| 0 <= i < 5 ==> self_limbs[i] < 1u64 << 54,
        // Postconditions from square operations
        as_nat(t0_limbs) % p() == pow(as_nat(self_limbs) as int, 2) as nat % p(),
        as_nat(t1_limbs) % p() == pow(as_nat(self_limbs) as int, 8) as nat % p(),
        as_nat(t4_limbs) % p() == pow(as_nat(t3_limbs) as int, 2) as nat % p(),
        // Postconditions from pow2k operations
        as_nat(t6_limbs) % p() == pow(as_nat(t5_limbs) as int, pow2(5)) as nat % p(),
        as_nat(t8_limbs) % p() == pow(as_nat(t7_limbs) as int, pow2(10)) as nat % p(),
        as_nat(t10_limbs) % p() == pow(as_nat(t9_limbs) as int, pow2(20)) as nat % p(),
        as_nat(t12_limbs) % p() == pow(as_nat(t11_limbs) as int, pow2(10)) as nat % p(),
        as_nat(t14_limbs) % p() == pow(as_nat(t13_limbs) as int, pow2(50)) as nat % p(),
        as_nat(t16_limbs) % p() == pow(as_nat(t15_limbs) as int, pow2(100)) as nat % p(),
        as_nat(t18_limbs) % p() == pow(as_nat(t17_limbs) as int, pow2(50)) as nat % p(),
        // Postconditions from mul operations
        as_nat(t2_limbs) % p() == (as_nat(self_limbs) * as_nat(t1_limbs)) % p(),
        as_nat(t3_limbs) % p() == (as_nat(t0_limbs) * as_nat(t2_limbs)) % p(),
        as_nat(t5_limbs) % p() == (as_nat(t2_limbs) * as_nat(t4_limbs)) % p(),
        as_nat(t7_limbs) % p() == (as_nat(t6_limbs) * as_nat(t5_limbs)) % p(),
        as_nat(t9_limbs) % p() == (as_nat(t8_limbs) * as_nat(t7_limbs)) % p(),
        as_nat(t11_limbs) % p() == (as_nat(t10_limbs) * as_nat(t9_limbs)) % p(),
        as_nat(t13_limbs) % p() == (as_nat(t12_limbs) * as_nat(t7_limbs)) % p(),
        as_nat(t15_limbs) % p() == (as_nat(t14_limbs) * as_nat(t13_limbs)) % p(),
        as_nat(t17_limbs) % p() == (as_nat(t16_limbs) * as_nat(t15_limbs)) % p(),
        as_nat(t19_limbs) % p() == (as_nat(t18_limbs) * as_nat(t13_limbs)) % p(),
    ensures
        as_nat(t19_limbs) % p() == pow(as_nat(self_limbs) as int, (pow2(250) - 1) as nat) as nat
            % p(),
        as_nat(t2_limbs) % p() == pow(as_nat(self_limbs) as int, 9) as nat % p(),
        as_nat(t3_limbs) % p() == pow(as_nat(self_limbs) as int, 11) as nat % p(),
        as_nat(t4_limbs) % p() == pow(as_nat(self_limbs) as int, 22) as nat % p(),
        as_nat(t5_limbs) % p() == pow(as_nat(self_limbs) as int, (pow2(5) - 1) as nat) as nat % p(),
        as_nat(t7_limbs) % p() == pow(as_nat(self_limbs) as int, (pow2(10) - 1) as nat) as nat
            % p(),
        as_nat(t9_limbs) % p() == pow(as_nat(self_limbs) as int, (pow2(20) - 1) as nat) as nat
            % p(),
        as_nat(t11_limbs) % p() == pow(as_nat(self_limbs) as int, (pow2(40) - 1) as nat) as nat
            % p(),
        as_nat(t13_limbs) % p() == pow(as_nat(self_limbs) as int, (pow2(50) - 1) as nat) as nat
            % p(),
        as_nat(t15_limbs) % p() == pow(as_nat(self_limbs) as int, (pow2(100) - 1) as nat) as nat
            % p(),
        as_nat(t17_limbs) % p() == pow(as_nat(self_limbs) as int, (pow2(200) - 1) as nat) as nat
            % p(),
{
    let base = as_nat(self_limbs) as int;

    assert(p() > 0) by {
        pow255_gt_19();
    }

    // Establish that base >= 0, which makes all pow(base, n) >= 0
    assert(base >= 0);

    // ========================================================================
    // Establish base facts from t3 checkpoint
    // ========================================================================

    // Prove t2 = x^9 and t3 = x^11 using the helper lemmas
    assert(pow(base, 1) == base) by {
        lemma_pow1(base);
    }
    assert(pow(base, 1) as nat == as_nat(self_limbs));
    assert(as_nat(self_limbs) % p() == pow(base, 1) as nat % p());

    // t2 = self * t1 = x^1 * x^8 = x^9
    assert(as_nat(t2_limbs) % p() == ((as_nat(self_limbs) % p()) * (as_nat(t1_limbs) % p())) % p())
        by {
        lemma_mul_mod_noop_general(as_nat(self_limbs) as int, as_nat(t1_limbs) as int, p() as int);
    }

    assert(as_nat(t2_limbs) % p() == ((pow(base, 1) as nat % p()) * (pow(base, 8) as nat % p()))
        % p());

    assert(as_nat(t2_limbs) % p() == (pow(base, 1) as nat * pow(base, 8) as nat) % p()) by {
        lemma_mul_mod_both(pow(base, 1) as nat as int, pow(base, 8) as nat as int, p() as int);
    }

    assert(pow(base, 1) * pow(base, 8) == pow(base, 9)) by {
        lemma_pow_adds(base, 1, 8);
    }

    // Convert to nat
    assert(pow(base, 1) >= 0);
    assert(pow(base, 8) >= 0) by {
        lemma_pow_even_nonnegative(base, 4);
    }
    assert((pow(base, 1) * pow(base, 8)) >= 0) by {
        lemma_mul_nonnegative(pow(base, 1), pow(base, 8));
    }
    assert(pow(base, 1) as nat * pow(base, 8) as nat == (pow(base, 1) * pow(base, 8)) as nat);
    assert(pow(base, 1) as nat * pow(base, 8) as nat == pow(base, 9) as nat);

    assert(as_nat(t2_limbs) % p() == pow(base, 9) as nat % p());

    // t3 = t0 * t2 = x^2 * x^9 = x^11
    assert(as_nat(t3_limbs) % p() == ((as_nat(t0_limbs) % p()) * (as_nat(t2_limbs) % p())) % p())
        by {
        lemma_mul_mod_noop_general(as_nat(t0_limbs) as int, as_nat(t2_limbs) as int, p() as int);
    }

    assert(as_nat(t3_limbs) % p() == ((pow(base, 2) as nat % p()) * (pow(base, 9) as nat % p()))
        % p());

    assert(as_nat(t3_limbs) % p() == (pow(base, 2) as nat * pow(base, 9) as nat) % p()) by {
        lemma_mul_mod_both(pow(base, 2) as nat as int, pow(base, 9) as nat as int, p() as int);
    }

    assert(pow(base, 2) * pow(base, 9) == pow(base, 11)) by {
        lemma_pow_adds(base, 2, 9);
    }

    assert(pow(base, 2) >= 0) by {
        lemma_pow_even_nonnegative(base, 1);
    }
    assert(pow(base, 9) >= 0) by {
        assert(pow(base, 1) * pow(base, 8) == pow(base, 9));  // known
        assert(pow(base, 1) >= 0);
        assert(pow(base, 8) >= 0);  // known
        lemma_mul_nonnegative(pow(base, 1), pow(base, 8));
    }
    assert((pow(base, 2) * pow(base, 9)) >= 0) by {
        lemma_mul_nonnegative(pow(base, 2), pow(base, 9));
    }
    assert(pow(base, 2) as nat * pow(base, 9) as nat == (pow(base, 2) * pow(base, 9)) as nat);
    assert(pow(base, 2) as nat * pow(base, 9) as nat == pow(base, 11) as nat);

    assert(as_nat(t3_limbs) % p() == pow(base, 11) as nat % p());

    // ========================================================================
    // Prove t4 = x^22
    // ========================================================================
    // t4 = t3^2 = (x^11)^2 = x^22

    assert(pow(base, 11) >= 0) by {
        assert(pow(base, 2) * pow(base, 9) == pow(base, 11));  // known
        lemma_mul_nonnegative(pow(base, 2), pow(base, 9));
    }

    let t3_val = as_nat(t3_limbs) as int;
    assert(t3_val >= 0);
    assert(pow(t3_val, 2) >= 0) by {
        lemma_pow_even_nonnegative(t3_val, 1);
    }
    assert(pow(base, 22) >= 0) by {
        lemma_pow_even_nonnegative(base, 11);
    }

    assert((pow(as_nat(t3_limbs) as int, 2) as nat) % p() == (pow(as_nat(t3_limbs) as int, 2) % (
    p() as int)) as nat);
    assert((pow(base, 22) as nat) % p() == (pow(base, 22) % (p() as int)) as nat);

    assert((pow(as_nat(t3_limbs) as int, 2) % (p() as int)) as nat == (pow(pow(base, 11), 2) % (
    p() as int)) as nat) by {
        lemma_pow_mod_congruent(as_nat(t3_limbs) as int, pow(base, 11), 2, p() as int);
    }

    assert(pow(pow(base, 11), 2) == pow(base, 22)) by {
        lemma_pow_multiplies(base, 11, 2);
    }

    assert(as_nat(t4_limbs) % p() == pow(base, 22) as nat % p());

    // ========================================================================
    // Prove t5 = x^31 = x^(2^5-1)
    // ========================================================================
    // t5 = t2 * t4 = x^9 * x^22 = x^31

    assert(as_nat(t5_limbs) % p() == ((as_nat(t2_limbs) % p()) * (as_nat(t4_limbs) % p())) % p())
        by {
        lemma_mul_mod_noop_general(as_nat(t2_limbs) as int, as_nat(t4_limbs) as int, p() as int);
    }

    assert(as_nat(t5_limbs) % p() == ((pow(base, 9) as nat % p()) * (pow(base, 22) as nat % p()))
        % p());

    assert(as_nat(t5_limbs) % p() == (pow(base, 9) as nat * pow(base, 22) as nat) % p()) by {
        lemma_mul_mod_both(pow(base, 9) as nat as int, pow(base, 22) as nat as int, p() as int);
    }

    assert(pow(base, 9) * pow(base, 22) == pow(base, 31)) by {
        lemma_pow_adds(base, 9, 22);
    }

    assert(pow(base, 22) >= 0);  // known from earlier
    assert((pow(base, 9) * pow(base, 22)) >= 0) by {
        lemma_mul_nonnegative(pow(base, 9), pow(base, 22));
    }
    assert(pow(base, 9) as nat * pow(base, 22) as nat == (pow(base, 9) * pow(base, 22)) as nat);
    assert(pow(base, 9) as nat * pow(base, 22) as nat == pow(base, 31) as nat);

    assert(31 == pow2(5) - 1) by {
        lemma2_to64();
    }

    assert(as_nat(t5_limbs) % p() == pow(base, (pow2(5) - 1) as nat) as nat % p());

    // ========================================================================
    // Prove t6 = x^((2^5-1)*2^5)
    // ========================================================================
    // t6 = t5.pow2k(5) = (x^(2^5-1))^(2^5)

    let t5_val = as_nat(t5_limbs) as int;
    assert(t5_val >= 0);

    // Prove powers are non-negative (pow2(5) = 32 is even, so use lemma for even exponents)
    assert(pow(as_nat(t5_limbs) as int, pow2(5)) >= 0) by {
        assert(pow2(5) == 2 * 16) by {
            lemma2_to64();
        }
        lemma_pow_even_nonnegative(as_nat(t5_limbs) as int, 16);
    }
    assert(pow(base, ((pow2(5) - 1) * pow2(5)) as nat) >= 0) by {
        assert(pow2(5) == 32) by {
            lemma2_to64();
        }
        // ((2^5-1) * 2^5) = (31 * 32) = 992 = 2 * 496
        assert(((pow2(5) - 1) * pow2(5)) as nat == 2 * 496) by {
            lemma2_to64();
        }
        lemma_pow_even_nonnegative(base, 496);
    }

    assert((pow(as_nat(t5_limbs) as int, pow2(5)) as nat) % p() == (pow(
        as_nat(t5_limbs) as int,
        pow2(5),
    ) % (p() as int)) as nat);
    assert((pow(base, ((pow2(5) - 1) * pow2(5)) as nat) as nat) % p() == (pow(
        base,
        ((pow2(5) - 1) * pow2(5)) as nat,
    ) % (p() as int)) as nat);

    assert((pow(as_nat(t5_limbs) as int, pow2(5)) % (p() as int)) as nat == (pow(
        pow(base, (pow2(5) - 1) as nat),
        pow2(5),
    ) % (p() as int)) as nat) by {
        lemma_pow_mod_congruent(
            as_nat(t5_limbs) as int,
            pow(base, (pow2(5) - 1) as nat),
            pow2(5),
            p() as int,
        );
    }

    assert(pow(pow(base, (pow2(5) - 1) as nat), pow2(5) as nat) == pow(
        base,
        (((pow2(5) - 1) as nat) * (pow2(5) as nat)) as nat,
    )) by {
        lemma_pow_multiplies(base, (pow2(5) - 1) as nat, pow2(5) as nat);
    }

    assert(as_nat(t6_limbs) % p() == pow(base, ((pow2(5) - 1) * pow2(5)) as nat) as nat % p());

    // ========================================================================
    // Prove t7 = x^(2^10-1)
    // ========================================================================
    // t7 = t6 * t5 = x^((2^5-1)*2^5) * x^(2^5-1) = x^(2^10-1)

    assert(as_nat(t7_limbs) % p() == ((as_nat(t6_limbs) % p()) * (as_nat(t5_limbs) % p())) % p())
        by {
        lemma_mul_mod_noop_general(as_nat(t6_limbs) as int, as_nat(t5_limbs) as int, p() as int);
    }

    assert(as_nat(t7_limbs) % p() == ((pow(base, ((pow2(5) - 1) * pow2(5)) as nat) as nat % p()) * (
    pow(base, (pow2(5) - 1) as nat) as nat % p())) % p());

    assert(as_nat(t7_limbs) % p() == (pow(base, ((pow2(5) - 1) * pow2(5)) as nat) as nat * pow(
        base,
        (pow2(5) - 1) as nat,
    ) as nat) % p()) by {
        lemma_mul_mod_both(
            pow(base, ((pow2(5) - 1) * pow2(5)) as nat) as nat as int,
            pow(base, (pow2(5) - 1) as nat) as nat as int,
            p() as int,
        );
    }

    assert(pow(base, ((pow2(5) - 1) * pow2(5)) as nat) * pow(base, (pow2(5) - 1) as nat) == pow(
        base,
        (((pow2(5) - 1) * pow2(5)) + (pow2(5) - 1)) as nat,
    )) by {
        lemma_pow_adds(base, ((pow2(5) - 1) * pow2(5)) as nat, (pow2(5) - 1) as nat);
    }

    assert((((pow2(5) - 1) * pow2(5)) + (pow2(5) - 1)) as nat == (pow2(10) - 1) as nat) by {
        lemma_pow2_geometric_double(5);
    }

    assert(pow(base, ((pow2(5) - 1) * pow2(5)) as nat) >= 0);  // known from earlier
    assert(pow(base, (pow2(5) - 1) as nat) >= 0) by {
        assert(pow(base, 9) * pow(base, 22) == pow(base, 31));  // known
        lemma_mul_nonnegative(pow(base, 9), pow(base, 22));
    }
    assert((pow(base, ((pow2(5) - 1) * pow2(5)) as nat) * pow(base, (pow2(5) - 1) as nat)) >= 0)
        by {
        lemma_mul_nonnegative(
            pow(base, ((pow2(5) - 1) * pow2(5)) as nat),
            pow(base, (pow2(5) - 1) as nat),
        );
    }
    assert(pow(base, ((pow2(5) - 1) * pow2(5)) as nat) as nat * pow(
        base,
        (pow2(5) - 1) as nat,
    ) as nat == (pow(base, ((pow2(5) - 1) * pow2(5)) as nat) * pow(
        base,
        (pow2(5) - 1) as nat,
    )) as nat);
    assert(pow(base, ((pow2(5) - 1) * pow2(5)) as nat) as nat * pow(
        base,
        (pow2(5) - 1) as nat,
    ) as nat == pow(base, (pow2(10) - 1) as nat) as nat);

    assert(as_nat(t7_limbs) % p() == pow(base, (pow2(10) - 1) as nat) as nat % p());

    // ========================================================================
    // Prove t8 = x^((2^10-1)*2^10)
    // ========================================================================
    // t8 = t7.pow2k(10) = (x^(2^10-1))^(2^10)

    let t7_val = as_nat(t7_limbs) as int;
    assert(t7_val >= 0);

    // Prove powers are non-negative (pow2(10) = 1024 is even)
    assert(pow(as_nat(t7_limbs) as int, pow2(10)) >= 0) by {
        assert(pow2(10) == 2 * 512) by {
            lemma2_to64();
        }
        lemma_pow_even_nonnegative(as_nat(t7_limbs) as int, 512);
    }
    assert(pow(base, ((pow2(10) - 1) * pow2(10)) as nat) >= 0) by {
        assert(pow2(10) == 1024) by {
            lemma2_to64();
        }
        // ((2^10-1) * 2^10) = (1023 * 1024) = 1047552 = 2 * 523776
        assert(((pow2(10) - 1) * pow2(10)) as nat == 2 * 523776) by {
            lemma2_to64();
        }
        lemma_pow_even_nonnegative(base, 523776);
    }

    assert((pow(as_nat(t7_limbs) as int, pow2(10)) as nat) % p() == (pow(
        as_nat(t7_limbs) as int,
        pow2(10),
    ) % (p() as int)) as nat);
    assert((pow(base, ((pow2(10) - 1) * pow2(10)) as nat) as nat) % p() == (pow(
        base,
        ((pow2(10) - 1) * pow2(10)) as nat,
    ) % (p() as int)) as nat);

    assert((pow(as_nat(t7_limbs) as int, pow2(10)) % (p() as int)) as nat == (pow(
        pow(base, (pow2(10) - 1) as nat),
        pow2(10),
    ) % (p() as int)) as nat) by {
        lemma_pow_mod_congruent(
            as_nat(t7_limbs) as int,
            pow(base, (pow2(10) - 1) as nat),
            pow2(10),
            p() as int,
        );
    }

    assert(pow(pow(base, (pow2(10) - 1) as nat), pow2(10) as nat) == pow(
        base,
        (((pow2(10) - 1) as nat) * (pow2(10) as nat)),
    )) by {
        lemma_pow_multiplies(base, (pow2(10) - 1) as nat, pow2(10) as nat);
    }

    // Connect nat multiplication to int multiplication cast: (a as nat) * (b as nat) == (a * b) as nat when a*b >= 0
    assert((((pow2(10) - 1) as nat) * (pow2(10) as nat)) == ((pow2(10) - 1) * pow2(10)) as nat) by {
        assert(pow2(10) - 1 >= 0) by {
            lemma2_to64();
        }
        assert(pow2(10) >= 0) by {
            lemma_pow2_pos(10);
        }
        assert((pow2(10) - 1) * pow2(10) >= 0) by {
            lemma_mul_nonnegative(pow2(10) - 1, pow2(10) as int);
        }
    }

    assert(as_nat(t8_limbs) % p() == pow(base, ((pow2(10) - 1) * pow2(10)) as nat) as nat % p());

    // ========================================================================
    // Prove t9 = x^(2^20-1)
    // ========================================================================
    // t9 = t8 * t7 = x^((2^10-1)*2^10) * x^(2^10-1) = x^(2^20-1)

    assert(as_nat(t9_limbs) % p() == ((as_nat(t8_limbs) % p()) * (as_nat(t7_limbs) % p())) % p())
        by {
        lemma_mul_mod_noop_general(as_nat(t8_limbs) as int, as_nat(t7_limbs) as int, p() as int);
    }

    assert(as_nat(t9_limbs) % p() == ((pow(base, ((pow2(10) - 1) * pow2(10)) as nat) as nat % p())
        * (pow(base, (pow2(10) - 1) as nat) as nat % p())) % p());

    assert(as_nat(t9_limbs) % p() == (pow(base, ((pow2(10) - 1) * pow2(10)) as nat) as nat * pow(
        base,
        (pow2(10) - 1) as nat,
    ) as nat) % p()) by {
        lemma_mul_mod_both(
            pow(base, ((pow2(10) - 1) * pow2(10)) as nat) as nat as int,
            pow(base, (pow2(10) - 1) as nat) as nat as int,
            p() as int,
        );
    }

    assert(pow(base, ((pow2(10) - 1) * pow2(10)) as nat) * pow(base, (pow2(10) - 1) as nat) == pow(
        base,
        (((pow2(10) - 1) * pow2(10)) as nat) + ((pow2(10) - 1) as nat),
    )) by {
        lemma_pow_adds(base, ((pow2(10) - 1) * pow2(10)) as nat, (pow2(10) - 1) as nat);
    }

    // Connect nat addition to int addition cast: (a as nat) + (b as nat) == (a + b) as nat when a,b,a+b >= 0
    assert((((pow2(10) - 1) * pow2(10)) as nat) + ((pow2(10) - 1) as nat) == (((pow2(10) - 1)
        * pow2(10)) + (pow2(10) - 1)) as nat) by {
        assert(pow2(10) - 1 >= 0) by {
            lemma2_to64();
        }
        assert(pow2(10) >= 0) by {
            lemma_pow2_pos(10);
        }
        assert((pow2(10) - 1) * pow2(10) >= 0) by {
            lemma_mul_nonnegative(pow2(10) - 1, pow2(10) as int);
        }
        assert(((pow2(10) - 1) * pow2(10)) + (pow2(10) - 1) >= 0);
    }

    assert((((pow2(10) - 1) * pow2(10)) + (pow2(10) - 1)) as nat == (pow2(20) - 1) as nat) by {
        lemma_pow2_geometric_double(10);
    }

    assert(pow(base, ((pow2(10) - 1) * pow2(10)) as nat) >= 0);  // known from earlier
    assert(pow(base, (pow2(10) - 1) as nat) >= 0) by {
        assert(pow(base, ((pow2(5) - 1) * pow2(5)) as nat) * pow(base, (pow2(5) - 1) as nat) == pow(
            base,
            (pow2(10) - 1) as nat,
        ));  // known
        lemma_mul_nonnegative(
            pow(base, ((pow2(5) - 1) * pow2(5)) as nat),
            pow(base, (pow2(5) - 1) as nat),
        );
    }
    assert((pow(base, ((pow2(10) - 1) * pow2(10)) as nat) * pow(base, (pow2(10) - 1) as nat)) >= 0)
        by {
        lemma_mul_nonnegative(
            pow(base, ((pow2(10) - 1) * pow2(10)) as nat),
            pow(base, (pow2(10) - 1) as nat),
        );
    }
    assert(pow(base, ((pow2(10) - 1) * pow2(10)) as nat) as nat * pow(
        base,
        (pow2(10) - 1) as nat,
    ) as nat == (pow(base, ((pow2(10) - 1) * pow2(10)) as nat) * pow(
        base,
        (pow2(10) - 1) as nat,
    )) as nat);
    assert(pow(base, ((pow2(10) - 1) * pow2(10)) as nat) as nat * pow(
        base,
        (pow2(10) - 1) as nat,
    ) as nat == pow(base, (pow2(20) - 1) as nat) as nat);

    assert(as_nat(t9_limbs) % p() == pow(base, (pow2(20) - 1) as nat) as nat % p());

    // ========================================================================
    // Prove t10 = x^((2^20-1)*2^20)
    // ========================================================================
    // t10 = t9.pow2k(20) = (x^(2^20-1))^(2^20)

    let t9_val = as_nat(t9_limbs) as int;
    assert(t9_val >= 0);

    // Prove powers are non-negative (pow2(20) is even)
    assert(pow(as_nat(t9_limbs) as int, pow2(20)) >= 0) by {
        assert(pow2(20) == 2 * 524288) by {
            lemma2_to64();
        }
        lemma_pow_even_nonnegative(as_nat(t9_limbs) as int, 524288);
    }
    assert(pow(base, ((pow2(20) - 1) * pow2(20)) as nat) >= 0) by {
        // ((2^20-1) * 2^20) is even since 2^20 is even
        assert(pow2(20) == 2 * 524288) by {
            lemma2_to64();
        }
        // (2^20-1) * 2^20 = (2^20-1) * 2 * 524288, which is even
        lemma_pow_even_nonnegative(base, ((pow2(20) - 1) * 524288) as nat);
    }

    assert((pow(as_nat(t9_limbs) as int, pow2(20)) as nat) % p() == (pow(
        as_nat(t9_limbs) as int,
        pow2(20),
    ) % (p() as int)) as nat);
    assert((pow(base, ((pow2(20) - 1) * pow2(20)) as nat) as nat) % p() == (pow(
        base,
        ((pow2(20) - 1) * pow2(20)) as nat,
    ) % (p() as int)) as nat);

    assert((pow(as_nat(t9_limbs) as int, pow2(20)) % (p() as int)) as nat == (pow(
        pow(base, (pow2(20) - 1) as nat),
        pow2(20),
    ) % (p() as int)) as nat) by {
        lemma_pow_mod_congruent(
            as_nat(t9_limbs) as int,
            pow(base, (pow2(20) - 1) as nat),
            pow2(20),
            p() as int,
        );
    }

    assert(pow(pow(base, (pow2(20) - 1) as nat), pow2(20) as nat) == pow(
        base,
        (((pow2(20) - 1) as nat) * (pow2(20) as nat)),
    )) by {
        lemma_pow_multiplies(base, (pow2(20) - 1) as nat, pow2(20) as nat);
    }

    // Connect nat multiplication to int multiplication cast
    assert((((pow2(20) - 1) as nat) * (pow2(20) as nat)) == ((pow2(20) - 1) * pow2(20)) as nat) by {
        assert(pow2(20) - 1 >= 0) by {
            lemma2_to64();
        }
        assert(pow2(20) >= 0) by {
            lemma_pow2_pos(20);
        }
        assert((pow2(20) - 1) * pow2(20) >= 0) by {
            lemma_mul_nonnegative(pow2(20) - 1, pow2(20) as int);
        }
    }

    assert(as_nat(t10_limbs) % p() == pow(base, ((pow2(20) - 1) * pow2(20)) as nat) as nat % p());

    // ========================================================================
    // Prove t11 = x^(2^40-1)
    // ========================================================================
    // t11 = t10 * t9 = x^((2^20-1)*2^20) * x^(2^20-1) = x^(2^40-1)

    assert(as_nat(t11_limbs) % p() == ((as_nat(t10_limbs) % p()) * (as_nat(t9_limbs) % p())) % p())
        by {
        lemma_mul_mod_noop_general(as_nat(t10_limbs) as int, as_nat(t9_limbs) as int, p() as int);
    }

    assert(as_nat(t11_limbs) % p() == ((pow(base, ((pow2(20) - 1) * pow2(20)) as nat) as nat % p())
        * (pow(base, (pow2(20) - 1) as nat) as nat % p())) % p());

    assert(as_nat(t11_limbs) % p() == (pow(base, ((pow2(20) - 1) * pow2(20)) as nat) as nat * pow(
        base,
        (pow2(20) - 1) as nat,
    ) as nat) % p()) by {
        lemma_mul_mod_both(
            pow(base, ((pow2(20) - 1) * pow2(20)) as nat) as nat as int,
            pow(base, (pow2(20) - 1) as nat) as nat as int,
            p() as int,
        );
    }

    assert(pow(base, ((pow2(20) - 1) * pow2(20)) as nat) * pow(base, (pow2(20) - 1) as nat) == pow(
        base,
        (((pow2(20) - 1) * pow2(20)) as nat) + ((pow2(20) - 1) as nat),
    )) by {
        lemma_pow_adds(base, ((pow2(20) - 1) * pow2(20)) as nat, (pow2(20) - 1) as nat);
    }

    // Connect nat addition to int addition cast
    assert((((pow2(20) - 1) * pow2(20)) as nat) + ((pow2(20) - 1) as nat) == (((pow2(20) - 1)
        * pow2(20)) + (pow2(20) - 1)) as nat) by {
        assert(pow2(20) - 1 >= 0) by {
            lemma2_to64();
        }
        assert(pow2(20) >= 0) by {
            lemma_pow2_pos(20);
        }
        assert((pow2(20) - 1) * pow2(20) >= 0) by {
            lemma_mul_nonnegative(pow2(20) - 1, pow2(20) as int);
        }
        assert(((pow2(20) - 1) * pow2(20)) + (pow2(20) - 1) >= 0);
    }

    assert((((pow2(20) - 1) * pow2(20)) + (pow2(20) - 1)) as nat == (pow2(40) - 1) as nat) by {
        lemma_pow2_geometric_double(20);
    }

    assert(pow(base, ((pow2(20) - 1) * pow2(20)) as nat) >= 0);  // known from earlier
    assert(pow(base, (pow2(20) - 1) as nat) >= 0);  // known from earlier
    assert((pow(base, ((pow2(20) - 1) * pow2(20)) as nat) * pow(base, (pow2(20) - 1) as nat)) >= 0)
        by {
        lemma_mul_nonnegative(
            pow(base, ((pow2(20) - 1) * pow2(20)) as nat),
            pow(base, (pow2(20) - 1) as nat),
        );
    }
    assert(pow(base, ((pow2(20) - 1) * pow2(20)) as nat) as nat * pow(
        base,
        (pow2(20) - 1) as nat,
    ) as nat == (pow(base, ((pow2(20) - 1) * pow2(20)) as nat) * pow(
        base,
        (pow2(20) - 1) as nat,
    )) as nat);
    assert(pow(base, ((pow2(20) - 1) * pow2(20)) as nat) as nat * pow(
        base,
        (pow2(20) - 1) as nat,
    ) as nat == pow(base, (pow2(40) - 1) as nat) as nat);

    assert(as_nat(t11_limbs) % p() == pow(base, (pow2(40) - 1) as nat) as nat % p());

    // ========================================================================
    // Prove t12 = x^((2^40-1)*2^10)
    // ========================================================================
    // t12 = t11.pow2k(10) = (x^(2^40-1))^(2^10)

    let t11_val = as_nat(t11_limbs) as int;
    assert(t11_val >= 0);

    // Prove powers are non-negative (pow2(10) is even)
    assert(pow(as_nat(t11_limbs) as int, pow2(10)) >= 0) by {
        assert(pow2(10) == 2 * 512) by {
            lemma2_to64();
        }
        lemma_pow_even_nonnegative(as_nat(t11_limbs) as int, 512);
    }
    assert(pow(base, ((pow2(40) - 1) * pow2(10)) as nat) >= 0) by {
        assert(pow2(10) == 2 * 512) by {
            lemma2_to64();
        }
        // (pow2(40) - 1) * pow2(10) = (pow2(40) - 1) * (2 * 512) = 2 * ((pow2(40) - 1) * 512)
        assert((pow2(40) - 1) * pow2(10) == 2 * ((pow2(40) - 1) * 512)) by {
            lemma_mul_is_associative(pow2(40) - 1, 2, 512);
        }
        assert(((pow2(40) - 1) * pow2(10)) as nat == 2 * (((pow2(40) - 1) * 512) as nat)) by {
            assert((pow2(40) - 1) * 512 >= 0) by {
                assert(pow2(40) - 1 >= 0) by {
                    assert(pow2(40) > 0) by {
                        lemma_pow2_pos(40);
                    }
                }
                lemma_mul_nonnegative(pow2(40) - 1, 512);
            }
        }
        lemma_pow_even_nonnegative(base, ((pow2(40) - 1) * 512) as nat);
    }

    assert((pow(as_nat(t11_limbs) as int, pow2(10)) as nat) % p() == (pow(
        as_nat(t11_limbs) as int,
        pow2(10),
    ) % (p() as int)) as nat);
    assert((pow(base, ((pow2(40) - 1) * pow2(10)) as nat) as nat) % p() == (pow(
        base,
        ((pow2(40) - 1) * pow2(10)) as nat,
    ) % (p() as int)) as nat);

    assert((pow(as_nat(t11_limbs) as int, pow2(10)) % (p() as int)) as nat == (pow(
        pow(base, (pow2(40) - 1) as nat),
        pow2(10),
    ) % (p() as int)) as nat) by {
        lemma_pow_mod_congruent(
            as_nat(t11_limbs) as int,
            pow(base, (pow2(40) - 1) as nat),
            pow2(10),
            p() as int,
        );
    }

    assert(pow(pow(base, (pow2(40) - 1) as nat), pow2(10) as nat) == pow(
        base,
        (((pow2(40) - 1) as nat) * (pow2(10) as nat)),
    )) by {
        lemma_pow_multiplies(base, (pow2(40) - 1) as nat, pow2(10) as nat);
    }

    // Connect nat multiplication to int multiplication cast
    assert((((pow2(40) - 1) as nat) * (pow2(10) as nat)) == ((pow2(40) - 1) * pow2(10)) as nat) by {
        assert(pow2(40) - 1 >= 0) by {
            assert(pow2(40) > 0) by {
                lemma_pow2_pos(40);
            }
        }
        assert(pow2(10) >= 0) by {
            lemma_pow2_pos(10);
        }
        assert((pow2(40) - 1) * pow2(10) >= 0) by {
            lemma_mul_nonnegative(pow2(40) - 1, pow2(10) as int);
        }
    }

    assert(as_nat(t12_limbs) % p() == pow(base, ((pow2(40) - 1) * pow2(10)) as nat) as nat % p());

    // ========================================================================
    // Prove t13 = x^(2^50-1)
    // ========================================================================
    // t13 = t12 * t7 = x^((2^40-1)*2^10) * x^(2^10-1) = x^(2^50-1)

    assert(as_nat(t13_limbs) % p() == ((as_nat(t12_limbs) % p()) * (as_nat(t7_limbs) % p())) % p())
        by {
        lemma_mul_mod_noop_general(as_nat(t12_limbs) as int, as_nat(t7_limbs) as int, p() as int);
    }

    assert(as_nat(t13_limbs) % p() == ((pow(base, ((pow2(40) - 1) * pow2(10)) as nat) as nat % p())
        * (pow(base, (pow2(10) - 1) as nat) as nat % p())) % p());

    assert(as_nat(t13_limbs) % p() == (pow(base, ((pow2(40) - 1) * pow2(10)) as nat) as nat * pow(
        base,
        (pow2(10) - 1) as nat,
    ) as nat) % p()) by {
        lemma_mul_mod_both(
            pow(base, ((pow2(40) - 1) * pow2(10)) as nat) as nat as int,
            pow(base, (pow2(10) - 1) as nat) as nat as int,
            p() as int,
        );
    }

    assert(pow(base, ((pow2(40) - 1) * pow2(10)) as nat) * pow(base, (pow2(10) - 1) as nat) == pow(
        base,
        (((pow2(40) - 1) * pow2(10)) as nat) + ((pow2(10) - 1) as nat),
    )) by {
        lemma_pow_adds(base, ((pow2(40) - 1) * pow2(10)) as nat, (pow2(10) - 1) as nat);
    }

    // Connect nat addition to int addition cast
    assert((((pow2(40) - 1) * pow2(10)) as nat) + ((pow2(10) - 1) as nat) == (((pow2(40) - 1)
        * pow2(10)) + (pow2(10) - 1)) as nat) by {
        assert(pow2(40) - 1 >= 0) by {
            assert(pow2(40) > 0) by {
                lemma_pow2_pos(40);
            }
        }
        assert(pow2(10) >= 0) by {
            lemma_pow2_pos(10);
        }
        assert((pow2(40) - 1) * pow2(10) >= 0) by {
            lemma_mul_nonnegative(pow2(40) - 1, pow2(10) as int);
        }
        assert(pow2(10) - 1 >= 0) by {
            lemma2_to64();
        }
        assert(((pow2(40) - 1) * pow2(10)) + (pow2(10) - 1) >= 0);
    }

    assert((((pow2(40) - 1) * pow2(10)) + (pow2(10) - 1)) as nat == (pow2(50) - 1) as nat) by {
        lemma_pow2_geometric(40, 10);
    }

    assert(pow(base, ((pow2(40) - 1) * pow2(10)) as nat) >= 0);  // known from earlier
    assert(pow(base, (pow2(10) - 1) as nat) >= 0);  // known from earlier
    assert((pow(base, ((pow2(40) - 1) * pow2(10)) as nat) * pow(base, (pow2(10) - 1) as nat)) >= 0)
        by {
        lemma_mul_nonnegative(
            pow(base, ((pow2(40) - 1) * pow2(10)) as nat),
            pow(base, (pow2(10) - 1) as nat),
        );
    }
    assert(pow(base, ((pow2(40) - 1) * pow2(10)) as nat) as nat * pow(
        base,
        (pow2(10) - 1) as nat,
    ) as nat == (pow(base, ((pow2(40) - 1) * pow2(10)) as nat) * pow(
        base,
        (pow2(10) - 1) as nat,
    )) as nat);
    assert(pow(base, ((pow2(40) - 1) * pow2(10)) as nat) as nat * pow(
        base,
        (pow2(10) - 1) as nat,
    ) as nat == pow(base, (pow2(50) - 1) as nat) as nat);

    assert(as_nat(t13_limbs) % p() == pow(base, (pow2(50) - 1) as nat) as nat % p());

    // ========================================================================
    // Prove t14 = x^((2^50-1)*2^50)
    // ========================================================================
    // t14 = t13.pow2k(50) = (x^(2^50-1))^(2^50)

    let t13_val = as_nat(t13_limbs) as int;
    assert(t13_val >= 0);

    // Prove powers are non-negative (pow2(50) is even)
    assert(pow(as_nat(t13_limbs) as int, pow2(50)) >= 0) by {
        assert(pow2(50) == 2 * pow2(49)) by {
            lemma_pow2_unfold(50);
            lemma_pow2_unfold(49);
        }
        lemma_pow_even_nonnegative(as_nat(t13_limbs) as int, pow2(49) as nat);
    }
    assert(pow(base, ((pow2(50) - 1) * pow2(50)) as nat) >= 0) by {
        assert(pow2(50) == 2 * pow2(49)) by {
            lemma_pow2_unfold(50);
            lemma_pow2_unfold(49);
        }
        // (pow2(50) - 1) * pow2(50) = (pow2(50) - 1) * (2 * pow2(49)) = 2 * ((pow2(50) - 1) * pow2(49))
        assert((pow2(50) - 1) * pow2(50) == 2 * ((pow2(50) - 1) * pow2(49))) by {
            // Use commutativity and associativity: a * (b * c) = b * (a * c)
            assert((pow2(50) - 1) * (2 * pow2(49)) == ((pow2(50) - 1) * 2) * pow2(49)) by {
                lemma_mul_is_associative(pow2(50) - 1, 2, pow2(49) as int);
            }
            assert(((pow2(50) - 1) * 2) * pow2(49) == (2 * (pow2(50) - 1)) * pow2(49)) by {
                lemma_mul_is_commutative(pow2(50) - 1, 2);
            }
            assert((2 * (pow2(50) - 1)) * pow2(49) == 2 * ((pow2(50) - 1) * pow2(49))) by {
                lemma_mul_is_associative(2, pow2(50) - 1, pow2(49) as int);
            }
        }
        assert(((pow2(50) - 1) * pow2(50)) as nat == 2 * (((pow2(50) - 1) * pow2(49)) as nat)) by {
            assert((pow2(50) - 1) * pow2(49) >= 0) by {
                assert(pow2(50) - 1 >= 0) by {
                    assert(pow2(50) > 0) by {
                        lemma_pow2_pos(50);
                    }
                }
                assert(pow2(49) >= 0) by {
                    lemma_pow2_pos(49);
                }
                lemma_mul_nonnegative(pow2(50) - 1, pow2(49) as int);
            }
        }
        lemma_pow_even_nonnegative(base, ((pow2(50) - 1) * pow2(49)) as nat);
    }

    assert((pow(as_nat(t13_limbs) as int, pow2(50)) as nat) % p() == (pow(
        as_nat(t13_limbs) as int,
        pow2(50),
    ) % (p() as int)) as nat);
    assert((pow(base, ((pow2(50) - 1) * pow2(50)) as nat) as nat) % p() == (pow(
        base,
        ((pow2(50) - 1) * pow2(50)) as nat,
    ) % (p() as int)) as nat);

    assert((pow(as_nat(t13_limbs) as int, pow2(50)) % (p() as int)) as nat == (pow(
        pow(base, (pow2(50) - 1) as nat),
        pow2(50),
    ) % (p() as int)) as nat) by {
        lemma_pow_mod_congruent(
            as_nat(t13_limbs) as int,
            pow(base, (pow2(50) - 1) as nat),
            pow2(50),
            p() as int,
        );
    }

    assert(pow(pow(base, (pow2(50) - 1) as nat), pow2(50) as nat) == pow(
        base,
        (((pow2(50) - 1) as nat) * (pow2(50) as nat)),
    )) by {
        lemma_pow_multiplies(base, (pow2(50) - 1) as nat, pow2(50) as nat);
    }

    // Connect nat multiplication to int multiplication cast
    assert((((pow2(50) - 1) as nat) * (pow2(50) as nat)) == ((pow2(50) - 1) * pow2(50)) as nat) by {
        assert(pow2(50) - 1 >= 0) by {
            assert(pow2(50) > 0) by {
                lemma_pow2_pos(50);
            }
        }
        assert(pow2(50) >= 0) by {
            lemma_pow2_pos(50);
        }
        assert((pow2(50) - 1) * pow2(50) >= 0) by {
            lemma_mul_nonnegative(pow2(50) - 1, pow2(50) as int);
        }
    }

    assert(as_nat(t14_limbs) % p() == pow(base, ((pow2(50) - 1) * pow2(50)) as nat) as nat % p());

    // ========================================================================
    // Prove t15 = x^(2^100-1)
    // ========================================================================
    // t15 = t14 * t13 = x^((2^50-1)*2^50) * x^(2^50-1) = x^(2^100-1)

    assert(as_nat(t15_limbs) % p() == ((as_nat(t14_limbs) % p()) * (as_nat(t13_limbs) % p())) % p())
        by {
        lemma_mul_mod_noop_general(as_nat(t14_limbs) as int, as_nat(t13_limbs) as int, p() as int);
    }

    assert(as_nat(t15_limbs) % p() == ((pow(base, ((pow2(50) - 1) * pow2(50)) as nat) as nat % p())
        * (pow(base, (pow2(50) - 1) as nat) as nat % p())) % p());

    assert(as_nat(t15_limbs) % p() == (pow(base, ((pow2(50) - 1) * pow2(50)) as nat) as nat * pow(
        base,
        (pow2(50) - 1) as nat,
    ) as nat) % p()) by {
        lemma_mul_mod_both(
            pow(base, ((pow2(50) - 1) * pow2(50)) as nat) as nat as int,
            pow(base, (pow2(50) - 1) as nat) as nat as int,
            p() as int,
        );
    }

    assert(pow(base, ((pow2(50) - 1) * pow2(50)) as nat) * pow(base, (pow2(50) - 1) as nat) == pow(
        base,
        (((pow2(50) - 1) * pow2(50)) as nat) + ((pow2(50) - 1) as nat),
    )) by {
        lemma_pow_adds(base, ((pow2(50) - 1) * pow2(50)) as nat, (pow2(50) - 1) as nat);
    }

    // Connect nat addition to int addition cast
    assert((((pow2(50) - 1) * pow2(50)) as nat) + ((pow2(50) - 1) as nat) == (((pow2(50) - 1)
        * pow2(50)) + (pow2(50) - 1)) as nat) by {
        assert(pow2(50) - 1 >= 0) by {
            assert(pow2(50) > 0) by {
                lemma_pow2_pos(50);
            }
        }
        assert(pow2(50) >= 0) by {
            lemma_pow2_pos(50);
        }
        assert((pow2(50) - 1) * pow2(50) >= 0) by {
            lemma_mul_nonnegative(pow2(50) - 1, pow2(50) as int);
        }
        assert(((pow2(50) - 1) * pow2(50)) + (pow2(50) - 1) >= 0);
    }

    assert((((pow2(50) - 1) * pow2(50)) + (pow2(50) - 1)) as nat == (pow2(100) - 1) as nat) by {
        lemma_pow2_geometric_double(50);
    }

    assert(pow(base, ((pow2(50) - 1) * pow2(50)) as nat) >= 0);  // known from earlier
    assert(pow(base, (pow2(50) - 1) as nat) >= 0) by {
        assert(pow(base, ((pow2(40) - 1) * pow2(10)) as nat) * pow(base, (pow2(10) - 1) as nat)
            == pow(base, (pow2(50) - 1) as nat));  // known
        lemma_mul_nonnegative(
            pow(base, ((pow2(40) - 1) * pow2(10)) as nat),
            pow(base, (pow2(10) - 1) as nat),
        );
    }
    assert((pow(base, ((pow2(50) - 1) * pow2(50)) as nat) * pow(base, (pow2(50) - 1) as nat)) >= 0)
        by {
        lemma_mul_nonnegative(
            pow(base, ((pow2(50) - 1) * pow2(50)) as nat),
            pow(base, (pow2(50) - 1) as nat),
        );
    }
    assert(pow(base, ((pow2(50) - 1) * pow2(50)) as nat) as nat * pow(
        base,
        (pow2(50) - 1) as nat,
    ) as nat == (pow(base, ((pow2(50) - 1) * pow2(50)) as nat) * pow(
        base,
        (pow2(50) - 1) as nat,
    )) as nat);
    assert(pow(base, ((pow2(50) - 1) * pow2(50)) as nat) as nat * pow(
        base,
        (pow2(50) - 1) as nat,
    ) as nat == pow(base, (pow2(100) - 1) as nat) as nat);

    assert(as_nat(t15_limbs) % p() == pow(base, (pow2(100) - 1) as nat) as nat % p());

    // ========================================================================
    // Prove t16 = x^((2^100-1)*2^100)
    // ========================================================================
    // t16 = t15.pow2k(100) = (x^(2^100-1))^(2^100)

    let t15_val = as_nat(t15_limbs) as int;
    assert(t15_val >= 0);

    // Prove powers are non-negative (pow2(100) is even)
    assert(pow(as_nat(t15_limbs) as int, pow2(100)) >= 0) by {
        assert(pow2(100) == 2 * pow2(99)) by {
            lemma_pow2_unfold(100);
            lemma_pow2_unfold(99);
        }
        lemma_pow_even_nonnegative(as_nat(t15_limbs) as int, pow2(99) as nat);
    }
    assert(pow(base, ((pow2(100) - 1) * pow2(100)) as nat) >= 0) by {
        assert(pow2(100) == 2 * pow2(99)) by {
            lemma_pow2_unfold(100);
            lemma_pow2_unfold(99);
        }
        // (pow2(100) - 1) * pow2(100) = (pow2(100) - 1) * (2 * pow2(99)) = 2 * ((pow2(100) - 1) * pow2(99))
        assert((pow2(100) - 1) * pow2(100) == 2 * ((pow2(100) - 1) * pow2(99))) by {
            // Use commutativity and associativity: a * (b * c) = b * (a * c)
            assert((pow2(100) - 1) * (2 * pow2(99)) == ((pow2(100) - 1) * 2) * pow2(99)) by {
                lemma_mul_is_associative(pow2(100) - 1, 2, pow2(99) as int);
            }
            assert(((pow2(100) - 1) * 2) * pow2(99) == (2 * (pow2(100) - 1)) * pow2(99)) by {
                lemma_mul_is_commutative(pow2(100) - 1, 2);
            }
            assert((2 * (pow2(100) - 1)) * pow2(99) == 2 * ((pow2(100) - 1) * pow2(99))) by {
                lemma_mul_is_associative(2, pow2(100) - 1, pow2(99) as int);
            }
        }
        assert(((pow2(100) - 1) * pow2(100)) as nat == 2 * (((pow2(100) - 1) * pow2(99)) as nat))
            by {
            assert((pow2(100) - 1) * pow2(99) >= 0) by {
                assert(pow2(100) - 1 >= 0) by {
                    assert(pow2(100) > 0) by {
                        lemma_pow2_pos(100);
                    }
                }
                assert(pow2(99) >= 0) by {
                    lemma_pow2_pos(99);
                }
                lemma_mul_nonnegative(pow2(100) - 1, pow2(99) as int);
            }
        }
        lemma_pow_even_nonnegative(base, ((pow2(100) - 1) * pow2(99)) as nat);
    }

    assert((pow(as_nat(t15_limbs) as int, pow2(100)) as nat) % p() == (pow(
        as_nat(t15_limbs) as int,
        pow2(100),
    ) % (p() as int)) as nat);
    assert((pow(base, ((pow2(100) - 1) * pow2(100)) as nat) as nat) % p() == (pow(
        base,
        ((pow2(100) - 1) * pow2(100)) as nat,
    ) % (p() as int)) as nat);

    assert((pow(as_nat(t15_limbs) as int, pow2(100)) % (p() as int)) as nat == (pow(
        pow(base, (pow2(100) - 1) as nat),
        pow2(100),
    ) % (p() as int)) as nat) by {
        lemma_pow_mod_congruent(
            as_nat(t15_limbs) as int,
            pow(base, (pow2(100) - 1) as nat),
            pow2(100),
            p() as int,
        );
    }

    assert(pow(pow(base, (pow2(100) - 1) as nat), pow2(100) as nat) == pow(
        base,
        (((pow2(100) - 1) as nat) * (pow2(100) as nat)),
    )) by {
        lemma_pow_multiplies(base, (pow2(100) - 1) as nat, pow2(100) as nat);
    }

    // Connect nat multiplication to int multiplication cast
    assert((((pow2(100) - 1) as nat) * (pow2(100) as nat)) == ((pow2(100) - 1) * pow2(100)) as nat)
        by {
        assert(pow2(100) - 1 >= 0) by {
            assert(pow2(100) > 0) by {
                lemma_pow2_pos(100);
            }
        }
        assert(pow2(100) >= 0) by {
            lemma_pow2_pos(100);
        }
        assert((pow2(100) - 1) * pow2(100) >= 0) by {
            lemma_mul_nonnegative(pow2(100) - 1, pow2(100) as int);
        }
    }

    assert(as_nat(t16_limbs) % p() == pow(base, ((pow2(100) - 1) * pow2(100)) as nat) as nat % p());

    // ========================================================================
    // Prove t17 = x^(2^200-1)
    // ========================================================================
    // t17 = t16 * t15 = x^((2^100-1)*2^100) * x^(2^100-1) = x^(2^200-1)

    assert(as_nat(t17_limbs) % p() == ((as_nat(t16_limbs) % p()) * (as_nat(t15_limbs) % p())) % p())
        by {
        lemma_mul_mod_noop_general(as_nat(t16_limbs) as int, as_nat(t15_limbs) as int, p() as int);
    }

    assert(as_nat(t17_limbs) % p() == ((pow(base, ((pow2(100) - 1) * pow2(100)) as nat) as nat
        % p()) * (pow(base, (pow2(100) - 1) as nat) as nat % p())) % p());

    assert(as_nat(t17_limbs) % p() == (pow(base, ((pow2(100) - 1) * pow2(100)) as nat) as nat * pow(
        base,
        (pow2(100) - 1) as nat,
    ) as nat) % p()) by {
        lemma_mul_mod_both(
            pow(base, ((pow2(100) - 1) * pow2(100)) as nat) as nat as int,
            pow(base, (pow2(100) - 1) as nat) as nat as int,
            p() as int,
        );
    }

    assert(pow(base, ((pow2(100) - 1) * pow2(100)) as nat) * pow(base, (pow2(100) - 1) as nat)
        == pow(base, (((pow2(100) - 1) * pow2(100)) as nat) + ((pow2(100) - 1) as nat))) by {
        lemma_pow_adds(base, ((pow2(100) - 1) * pow2(100)) as nat, (pow2(100) - 1) as nat);
    }

    // Connect nat addition to int addition cast
    assert((((pow2(100) - 1) * pow2(100)) as nat) + ((pow2(100) - 1) as nat) == (((pow2(100) - 1)
        * pow2(100)) + (pow2(100) - 1)) as nat) by {
        assert(pow2(100) - 1 >= 0) by {
            assert(pow2(100) > 0) by {
                lemma_pow2_pos(100);
            }
        }
        assert(pow2(100) >= 0) by {
            lemma_pow2_pos(100);
        }
        assert((pow2(100) - 1) * pow2(100) >= 0) by {
            lemma_mul_nonnegative(pow2(100) - 1, pow2(100) as int);
        }
        assert(((pow2(100) - 1) * pow2(100)) + (pow2(100) - 1) >= 0);
    }

    assert((((pow2(100) - 1) * pow2(100)) + (pow2(100) - 1)) as nat == (pow2(200) - 1) as nat) by {
        lemma_pow2_geometric_double(100);
    }

    assert(pow(base, ((pow2(100) - 1) * pow2(100)) as nat) >= 0);  // known from earlier
    assert(pow(base, (pow2(100) - 1) as nat) >= 0) by {
        assert(pow(base, ((pow2(50) - 1) * pow2(50)) as nat) * pow(base, (pow2(50) - 1) as nat)
            == pow(base, (pow2(100) - 1) as nat));  // known
        lemma_mul_nonnegative(
            pow(base, ((pow2(50) - 1) * pow2(50)) as nat),
            pow(base, (pow2(50) - 1) as nat),
        );
    }
    assert((pow(base, ((pow2(100) - 1) * pow2(100)) as nat) * pow(base, (pow2(100) - 1) as nat))
        >= 0) by {
        lemma_mul_nonnegative(
            pow(base, ((pow2(100) - 1) * pow2(100)) as nat),
            pow(base, (pow2(100) - 1) as nat),
        );
    }
    assert(pow(base, ((pow2(100) - 1) * pow2(100)) as nat) as nat * pow(
        base,
        (pow2(100) - 1) as nat,
    ) as nat == (pow(base, ((pow2(100) - 1) * pow2(100)) as nat) * pow(
        base,
        (pow2(100) - 1) as nat,
    )) as nat);
    assert(pow(base, ((pow2(100) - 1) * pow2(100)) as nat) as nat * pow(
        base,
        (pow2(100) - 1) as nat,
    ) as nat == pow(base, (pow2(200) - 1) as nat) as nat);

    assert(as_nat(t17_limbs) % p() == pow(base, (pow2(200) - 1) as nat) as nat % p());

    // ========================================================================
    // Prove t18 = x^((2^200-1)*2^50)
    // ========================================================================
    // t18 = t17.pow2k(50) = (x^(2^200-1))^(2^50)

    let t17_val = as_nat(t17_limbs) as int;
    assert(t17_val >= 0);

    // Prove powers are non-negative (pow2(50) is even)
    assert(pow(as_nat(t17_limbs) as int, pow2(50)) >= 0) by {
        assert(pow2(50) == 2 * pow2(49)) by {
            lemma_pow2_unfold(50);
            lemma_pow2_unfold(49);
        }
        lemma_pow_even_nonnegative(as_nat(t17_limbs) as int, pow2(49) as nat);
    }
    assert(pow(base, ((pow2(200) - 1) * pow2(50)) as nat) >= 0) by {
        assert(pow2(50) == 2 * pow2(49)) by {
            lemma_pow2_unfold(50);
            lemma_pow2_unfold(49);
        }
        // (pow2(200) - 1) * pow2(50) = (pow2(200) - 1) * (2 * pow2(49)) = 2 * ((pow2(200) - 1) * pow2(49))
        assert((pow2(200) - 1) * pow2(50) == 2 * ((pow2(200) - 1) * pow2(49))) by {
            // Use commutativity and associativity: a * (b * c) = b * (a * c)
            assert((pow2(200) - 1) * (2 * pow2(49)) == ((pow2(200) - 1) * 2) * pow2(49)) by {
                lemma_mul_is_associative(pow2(200) - 1, 2, pow2(49) as int);
            }
            assert(((pow2(200) - 1) * 2) * pow2(49) == (2 * (pow2(200) - 1)) * pow2(49)) by {
                lemma_mul_is_commutative(pow2(200) - 1, 2);
            }
            assert((2 * (pow2(200) - 1)) * pow2(49) == 2 * ((pow2(200) - 1) * pow2(49))) by {
                lemma_mul_is_associative(2, pow2(200) - 1, pow2(49) as int);
            }
        }
        assert(((pow2(200) - 1) * pow2(50)) as nat == 2 * (((pow2(200) - 1) * pow2(49)) as nat))
            by {
            assert((pow2(200) - 1) * pow2(49) >= 0) by {
                assert(pow2(200) - 1 >= 0) by {
                    assert(pow2(200) > 0) by {
                        lemma_pow2_pos(200);
                    }
                }
                assert(pow2(49) >= 0) by {
                    lemma_pow2_pos(49);
                }
                lemma_mul_nonnegative(pow2(200) - 1, pow2(49) as int);
            }
        }
        lemma_pow_even_nonnegative(base, ((pow2(200) - 1) * pow2(49)) as nat);
    }

    assert((pow(as_nat(t17_limbs) as int, pow2(50)) as nat) % p() == (pow(
        as_nat(t17_limbs) as int,
        pow2(50),
    ) % (p() as int)) as nat);
    assert((pow(base, ((pow2(200) - 1) * pow2(50)) as nat) as nat) % p() == (pow(
        base,
        ((pow2(200) - 1) * pow2(50)) as nat,
    ) % (p() as int)) as nat);

    assert((pow(as_nat(t17_limbs) as int, pow2(50)) % (p() as int)) as nat == (pow(
        pow(base, (pow2(200) - 1) as nat),
        pow2(50),
    ) % (p() as int)) as nat) by {
        lemma_pow_mod_congruent(
            as_nat(t17_limbs) as int,
            pow(base, (pow2(200) - 1) as nat),
            pow2(50),
            p() as int,
        );
    }

    assert(pow(pow(base, (pow2(200) - 1) as nat), pow2(50) as nat) == pow(
        base,
        (((pow2(200) - 1) as nat) * (pow2(50) as nat)),
    )) by {
        lemma_pow_multiplies(base, (pow2(200) - 1) as nat, pow2(50) as nat);
    }

    // Connect nat multiplication to int multiplication cast
    assert((((pow2(200) - 1) as nat) * (pow2(50) as nat)) == ((pow2(200) - 1) * pow2(50)) as nat)
        by {
        assert(pow2(200) - 1 >= 0) by {
            assert(pow2(200) > 0) by {
                lemma_pow2_pos(200);
            }
        }
        assert(pow2(50) >= 0) by {
            lemma_pow2_pos(50);
        }
        assert((pow2(200) - 1) * pow2(50) >= 0) by {
            lemma_mul_nonnegative(pow2(200) - 1, pow2(50) as int);
        }
    }

    assert(as_nat(t18_limbs) % p() == pow(base, ((pow2(200) - 1) * pow2(50)) as nat) as nat % p());

    // ========================================================================
    // Prove t19 = x^(2^250-1) - FINAL STEP
    // ========================================================================
    // t19 = t18 * t13 = x^((2^200-1)*2^50) * x^(2^50-1) = x^(2^250-1)

    assert(as_nat(t19_limbs) % p() == ((as_nat(t18_limbs) % p()) * (as_nat(t13_limbs) % p())) % p())
        by {
        lemma_mul_mod_noop_general(as_nat(t18_limbs) as int, as_nat(t13_limbs) as int, p() as int);
    }

    assert(as_nat(t19_limbs) % p() == ((pow(base, ((pow2(200) - 1) * pow2(50)) as nat) as nat % p())
        * (pow(base, (pow2(50) - 1) as nat) as nat % p())) % p());

    assert(as_nat(t19_limbs) % p() == (pow(base, ((pow2(200) - 1) * pow2(50)) as nat) as nat * pow(
        base,
        (pow2(50) - 1) as nat,
    ) as nat) % p()) by {
        lemma_mul_mod_both(
            pow(base, ((pow2(200) - 1) * pow2(50)) as nat) as nat as int,
            pow(base, (pow2(50) - 1) as nat) as nat as int,
            p() as int,
        );
    }

    assert(pow(base, ((pow2(200) - 1) * pow2(50)) as nat) * pow(base, (pow2(50) - 1) as nat) == pow(
        base,
        (((pow2(200) - 1) * pow2(50)) as nat) + ((pow2(50) - 1) as nat),
    )) by {
        lemma_pow_adds(base, ((pow2(200) - 1) * pow2(50)) as nat, (pow2(50) - 1) as nat);
    }

    // Connect nat addition to int addition cast
    assert((((pow2(200) - 1) * pow2(50)) as nat) + ((pow2(50) - 1) as nat) == (((pow2(200) - 1)
        * pow2(50)) + (pow2(50) - 1)) as nat) by {
        assert(pow2(200) - 1 >= 0) by {
            assert(pow2(200) > 0) by {
                lemma_pow2_pos(200);
            }
        }
        assert(pow2(50) >= 0) by {
            lemma_pow2_pos(50);
        }
        assert((pow2(200) - 1) * pow2(50) >= 0) by {
            lemma_mul_nonnegative(pow2(200) - 1, pow2(50) as int);
        }
        assert(pow2(50) - 1 >= 0) by {
            assert(pow2(50) > 0) by {
                lemma_pow2_pos(50);
            }
        }
        assert(((pow2(200) - 1) * pow2(50)) + (pow2(50) - 1) >= 0);
    }

    assert((((pow2(200) - 1) * pow2(50)) + (pow2(50) - 1)) as nat == (pow2(250) - 1) as nat) by {
        lemma_pow2_geometric(200, 50);
    }

    assert(pow(base, ((pow2(200) - 1) * pow2(50)) as nat) >= 0);  // known from earlier
    assert(pow(base, (pow2(50) - 1) as nat) >= 0);  // known from earlier
    assert((pow(base, ((pow2(200) - 1) * pow2(50)) as nat) * pow(base, (pow2(50) - 1) as nat)) >= 0)
        by {
        lemma_mul_nonnegative(
            pow(base, ((pow2(200) - 1) * pow2(50)) as nat),
            pow(base, (pow2(50) - 1) as nat),
        );
    }
    assert(pow(base, ((pow2(200) - 1) * pow2(50)) as nat) as nat * pow(
        base,
        (pow2(50) - 1) as nat,
    ) as nat == (pow(base, ((pow2(200) - 1) * pow2(50)) as nat) * pow(
        base,
        (pow2(50) - 1) as nat,
    )) as nat);
    assert(pow(base, ((pow2(200) - 1) * pow2(50)) as nat) as nat * pow(
        base,
        (pow2(50) - 1) as nat,
    ) as nat == pow(base, (pow2(250) - 1) as nat) as nat);

    assert(as_nat(t19_limbs) % p() == pow(base, (pow2(250) - 1) as nat) as nat % p());
}

} // verus!
