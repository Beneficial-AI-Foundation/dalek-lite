#![allow(unused)]
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::lemma_small_mod;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;

use crate::backend::serial::u64::field::FieldElement51;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;

verus! {

// Lemma: Bridges from u64_5_as_nat postcondition to fe51_as_canonical_nat postcondition for power operations
pub proof fn lemma_bridge_pow_as_nat_to_spec(
    result: &FieldElement51,
    base: &FieldElement51,
    exp: nat,
)
    requires
        u64_5_as_nat(result.limbs) % p() == (pow(u64_5_as_nat(base.limbs) as int, exp) as nat)
            % p(),
    ensures
        fe51_as_canonical_nat(result) == (pow(fe51_as_canonical_nat(base) as int, exp) as nat)
            % p(),
{
    // Prove p() > 0
    pow255_gt_19();

    // By definition: fe51_as_canonical_nat(result) == u64_5_as_nat(result.limbs) % p()
    //                fe51_as_canonical_nat(base) == u64_5_as_nat(base.limbs) % p()
    // The solver should unfold these automatically

    // Apply lemma_pow_mod_noop: pow(b, e) % m == pow(b % m, e) % m
    lemma_pow_mod_noop(u64_5_as_nat(base.limbs) as int, exp, p() as int);

    // Let's use clear names for the key values
    let x = u64_5_as_nat(base.limbs);
    let y = fe51_as_canonical_nat(base);

    // y == x % p() by definition
    assert(y == x % p());

    // From lemma_pow_mod_noop, in int arithmetic:
    // pow(x as int, exp) % (p() as int) == pow((x % p()) as int, exp) % (p() as int)
    assert(pow(x as int, exp) % (p() as int) == pow((x % p()) as int, exp) % (p() as int));

    // Since y == x % p():
    assert(pow(x as int, exp) % (p() as int) == pow(y as int, exp) % (p() as int));

    assert(pow(x as int, exp) >= 0) by {
        lemma_pow_nonnegative(x as int, exp);
    }

    assert(pow(y as int, exp) >= 0) by {
        lemma_pow_nonnegative(y as int, exp);
    }

    // Now we have: pow(x, exp) % p() == pow(y, exp) % p()
    // With type conversions: (pow(x, exp) as nat) % p() == (pow(y, exp) as nat) % p()
    assert((pow(x as int, exp) as nat) % p() == (pow(y as int, exp) as nat) % p());
}

pub proof fn lemma_u64_5_as_nat_add(a: [u64; 5], b: [u64; 5])
    requires
        forall|i: int| 0 <= i < 5 ==> b[i] as nat + a[i] as nat <= u64::MAX,
    ensures
        u64_5_as_nat(
            [
                (a[0] + b[0]) as u64,
                (a[1] + b[1]) as u64,
                (a[2] + b[2]) as u64,
                (a[3] + b[3]) as u64,
                (a[4] + b[4]) as u64,
            ],
        ) == u64_5_as_nat(a) + u64_5_as_nat(b),
{
    let c: [u64; 5] = [
        (a[0] + b[0]) as u64,
        (a[1] + b[1]) as u64,
        (a[2] + b[2]) as u64,
        (a[3] + b[3]) as u64,
        (a[4] + b[4]) as u64,
    ];
    // distribute pow2
    assert(u64_5_as_nat(c) == (a[0] + b[0]) + pow2(51) * a[1] + pow2(51) * b[1] + pow2(102) * a[2]
        + pow2(102) * b[2] + pow2(153) * a[3] + pow2(153) * b[3] + pow2(204) * a[4] + pow2(204)
        * b[4]) by {
        lemma_mul_is_distributive_add(pow2(1 * 51) as int, a[1] as int, b[1] as int);
        lemma_mul_is_distributive_add(pow2(2 * 51) as int, a[2] as int, b[2] as int);
        lemma_mul_is_distributive_add(pow2(3 * 51) as int, a[3] as int, b[3] as int);
        lemma_mul_is_distributive_add(pow2(4 * 51) as int, a[4] as int, b[4] as int);
    }
}

// Lemma: If a > b pointwise, then u64_5_as_nat(a - b) = u64_5_as_nat(a) - u64_5_as_nat(b)
pub proof fn lemma_u64_5_as_nat_sub(a: [u64; 5], b: [u64; 5])
    requires
        forall|i: int| 0 <= i < 5 ==> b[i] <= a[i],
    ensures
        u64_5_as_nat(
            [
                (a[0] - b[0]) as u64,
                (a[1] - b[1]) as u64,
                (a[2] - b[2]) as u64,
                (a[3] - b[3]) as u64,
                (a[4] - b[4]) as u64,
            ],
        ) == u64_5_as_nat(a) - u64_5_as_nat(b),
{
    let c: [u64; 5] = [
        (a[0] - b[0]) as u64,
        (a[1] - b[1]) as u64,
        (a[2] - b[2]) as u64,
        (a[3] - b[3]) as u64,
        (a[4] - b[4]) as u64,
    ];
    // distribute pow2
    assert(u64_5_as_nat(c) == (a[0] - b[0]) + pow2(51) * a[1] - pow2(51) * b[1] + pow2(102) * a[2]
        - pow2(102) * b[2] + pow2(153) * a[3] - pow2(153) * b[3] + pow2(204) * a[4] - pow2(204)
        * b[4]) by {
        lemma_mul_is_distributive_sub(pow2(1 * 51) as int, a[1] as int, b[1] as int);
        lemma_mul_is_distributive_sub(pow2(2 * 51) as int, a[2] as int, b[2] as int);
        lemma_mul_is_distributive_sub(pow2(3 * 51) as int, a[3] as int, b[3] as int);
        lemma_mul_is_distributive_sub(pow2(4 * 51) as int, a[4] as int, b[4] as int);
    }
}

pub proof fn lemma_u64_5_as_nat_k(a: [u64; 5], k: u64)
    requires
        forall|i: int| 0 <= i < 5 ==> (k * a[i]) <= u64::MAX,
    ensures
        u64_5_as_nat(
            [
                (k * a[0]) as u64,
                (k * a[1]) as u64,
                (k * a[2]) as u64,
                (k * a[3]) as u64,
                (k * a[4]) as u64,
            ],
        ) == k * u64_5_as_nat(a),
{
    let ka = [
        (k * a[0]) as u64,
        (k * a[1]) as u64,
        (k * a[2]) as u64,
        (k * a[3]) as u64,
        (k * a[4]) as u64,
    ];

    assert(u64_5_as_nat(ka) == k * a[0] + k * (pow2(51) * a[1]) + k * (pow2(102) * a[2]) + k * (
    pow2(153) * a[3]) + k * (pow2(204) * a[4])) by {
        lemma_mul_is_associative(pow2(51) as int, a[1] as int, k as int);
        lemma_mul_is_associative(pow2(102) as int, a[2] as int, k as int);
        lemma_mul_is_associative(pow2(153) as int, a[3] as int, k as int);
        lemma_mul_is_associative(pow2(204) as int, a[4] as int, k as int);
    }

    assert(k * a[0] + k * (pow2(51) * a[1]) + k * (pow2(102) * a[2]) + k * (pow2(153) * a[3]) + k
        * (pow2(204) * a[4]) == k * (a[0] + (pow2(51) * a[1]) + (pow2(102) * a[2]) + (pow2(153)
        * a[3]) + (pow2(204) * a[4]))) by {
        lemma_mul_is_distributive_add(k as int, a[0] as int, pow2(51) * a[1]);
        lemma_mul_is_distributive_add(k as int, a[0] + pow2(51) * a[1], pow2(102) * a[2]);
        lemma_mul_is_distributive_add(
            k as int,
            a[0] + pow2(51) * a[1] + pow2(102) * a[2],
            pow2(153) * a[3],
        );
        lemma_mul_is_distributive_add(
            k as int,
            a[0] + pow2(51) * a[1] + pow2(102) * a[2] + pow2(153) * a[3],
            (pow2(204) * a[4]),
        );
    }
}

#[verusfmt::skip]
pub proof fn lemma_u64_5_as_nat_product(a: [u64; 5], b: [u64; 5])
    ensures
        // Full polynomial expansion
        u64_5_as_nat(a) * u64_5_as_nat(b) ==
            pow2(8 * 51) * (a[4] * b[4]) +
            pow2(7 * 51) * (a[3] * b[4] + a[4] * b[3]) +
            pow2(6 * 51) * (a[2] * b[4] + a[3] * b[3] + a[4] * b[2]) +
            pow2(5 * 51) * (a[1] * b[4] + a[2] * b[3] + a[3] * b[2] + a[4] * b[1]) +
            pow2(4 * 51) * (a[0] * b[4] + a[1] * b[3] + a[2] * b[2] + a[3] * b[1] + a[4] * b[0]) +
            pow2(3 * 51) * (a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0]) +
            pow2(2 * 51) * (a[0] * b[2] + a[1] * b[1] + a[2] * b[0]) +
            pow2(1 * 51) * (a[0] * b[1] + a[1] * b[0]) +
                           (a[0] * b[0]),
        // Mod-p reduction (using pow2(5*51) = p + 19)
        (u64_5_as_nat(a) * u64_5_as_nat(b)) % p() ==
            (
                pow2(4 * 51) * (a[0] * b[4] + a[1] * b[3] + a[2] * b[2] + a[3] * b[1] + a[4] * b[0]) +
                pow2(3 * 51) * (a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0] + 19 * (a[4] * b[4])) +
                pow2(2 * 51) * (a[0] * b[2] + a[1] * b[1] + a[2] * b[0] + 19 * (a[3] * b[4] + a[4] * b[3])) +
                pow2(1 * 51) * (a[0] * b[1] + a[1] * b[0] + 19 * (a[2] * b[4] + a[3] * b[3] + a[4] * b[2])) +
                               (a[0] * b[0] + 19 * (a[1] * b[4] + a[2] * b[3] + a[3] * b[2] + a[4] * b[1]))
            ) as nat % p(),
{
    let a0 = a[0]; let a1 = a[1]; let a2 = a[2]; let a3 = a[3]; let a4 = a[4];
    let b0 = b[0]; let b1 = b[1]; let b2 = b[2]; let b3 = b[3]; let b4 = b[4];

    let s1 = pow2(1 * 51);
    let s2 = pow2(2 * 51);
    let s3 = pow2(3 * 51);
    let s4 = pow2(4 * 51);
    let s5 = pow2(5 * 51);
    let s6 = pow2(6 * 51);
    let s7 = pow2(7 * 51);
    let s8 = pow2(8 * 51);

    assert(s1 * s1 == s2) by { lemma_pow2_adds(51, 51) }
    assert(s1 * s2 == s2 * s1 == s3) by { lemma_pow2_adds(51, 102) }
    assert(s1 * s3 == s3 * s1 == s4) by { lemma_pow2_adds(51, 153) }
    assert(s1 * s4 == s4 * s1 == s5) by { lemma_pow2_adds(51, 204) }
    assert(s2 * s2 == s4) by { lemma_pow2_adds(102, 102) }
    assert(s2 * s3 == s3 * s2 == s5) by { lemma_pow2_adds(102, 153) }
    assert(s2 * s4 == s4 * s2 == s6) by { lemma_pow2_adds(102, 204) }
    assert(s3 * s3 == s6) by { lemma_pow2_adds(153, 153) }
    assert(s3 * s4 == s4 * s3 == s7) by { lemma_pow2_adds(153, 204) }
    assert(s4 * s4 == s8) by { lemma_pow2_adds(204, 204) }

    // Step 1: Distribute u64_5_as_nat(a) * u64_5_as_nat(b) into 5 rows
    assert(u64_5_as_nat(a) * u64_5_as_nat(b) == a0 * u64_5_as_nat(b) + (s1 * a1)
        * u64_5_as_nat(b) + (s2 * a2) * u64_5_as_nat(b) + (s3 * a3) * u64_5_as_nat(b) + (s4
        * a4) * u64_5_as_nat(b)) by {
        lemma_mul_distributive_5_terms(
            u64_5_as_nat(b) as int,
            a0 as int,
            s1 * a1,
            s2 * a2,
            s3 * a3,
            s4 * a4,
        );
    }

    // Step 2: Expand each row
    assert(a0 * u64_5_as_nat(b) == s4 * (a0 * b4) + s3 * (a0 * b3) + s2 * (a0 * b2) + s1 * (a0
        * b1) + a0 * b0) by {
        lemma_mul_w0_and_reorder(
            a0 as int,
            b0 as int,
            s1 as int,
            b1 as int,
            s2 as int,
            b2 as int,
            s3 as int,
            b3 as int,
            s4 as int,
            b4 as int,
        );
    }

    assert((s1 * a1) * u64_5_as_nat(b) == s5 * (a1 * b4) + s4 * (a1 * b3) + s3 * (a1 * b2) + s2
        * (a1 * b1) + s1 * (a1 * b0)) by {
        lemma_mul_si_vi_and_reorder(
            s1 as int,
            a1 as int,
            b0 as int,
            s1 as int,
            b1 as int,
            s2 as int,
            b2 as int,
            s3 as int,
            b3 as int,
            s4 as int,
            b4 as int,
        );
    }

    assert((s2 * a2) * u64_5_as_nat(b) == s6 * (a2 * b4) + s5 * (a2 * b3) + s4 * (a2 * b2) + s3
        * (a2 * b1) + s2 * (a2 * b0)) by {
        lemma_mul_si_vi_and_reorder(
            s2 as int,
            a2 as int,
            b0 as int,
            s1 as int,
            b1 as int,
            s2 as int,
            b2 as int,
            s3 as int,
            b3 as int,
            s4 as int,
            b4 as int,
        );
    }

    assert((s3 * a3) * u64_5_as_nat(b) == s7 * (a3 * b4) + s6 * (a3 * b3) + s5 * (a3 * b2) + s4
        * (a3 * b1) + s3 * (a3 * b0)) by {
        lemma_mul_si_vi_and_reorder(
            s3 as int,
            a3 as int,
            b0 as int,
            s1 as int,
            b1 as int,
            s2 as int,
            b2 as int,
            s3 as int,
            b3 as int,
            s4 as int,
            b4 as int,
        );
    }

    assert((s4 * a4) * u64_5_as_nat(b) == s8 * (a4 * b4) + s7 * (a4 * b3) + s6 * (a4 * b2) + s5
        * (a4 * b1) + s4 * (a4 * b0)) by {
        lemma_mul_si_vi_and_reorder(
            s4 as int,
            a4 as int,
            b0 as int,
            s1 as int,
            b1 as int,
            s2 as int,
            b2 as int,
            s3 as int,
            b3 as int,
            s4 as int,
            b4 as int,
        );
    }

    // Step 3: Group by power
    assert(u64_5_as_nat(a) * u64_5_as_nat(b) == s8 * (a4 * b4) + s7 * (a3 * b4 + a4 * b3) + s6
        * (a2 * b4 + a3 * b3 + a4 * b2) + s5 * (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1) + s4
        * (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0) + s3 * (a0 * b3 + a1 * b2 + a2 * b1
        + a3 * b0) + s2 * (a0 * b2 + a1 * b1 + a2 * b0) + s1 * (a0 * b1 + a1 * b0) + (a0 * b0))
        by {
        // s1 terms
        assert(s1 * (a0 * b1) + s1 * (a1 * b0) == s1 * (a0 * b1 + a1 * b0)) by {
            lemma_mul_is_distributive_add(s1 as int, a0 * b1, a1 * b0);
        }
        // s2 terms
        assert(s2 * (a0 * b2) + s2 * (a1 * b1) + s2 * (a2 * b0) == s2 * (a0 * b2 + a1 * b1 + a2
            * b0)) by {
            lemma_mul_distributive_3_terms(s2 as int, a0 * b2, a1 * b1, a2 * b0);
        }
        // s3 terms
        assert(s3 * (a0 * b3) + s3 * (a1 * b2) + s3 * (a2 * b1) + s3 * (a3 * b0) == s3 * (a0
            * b3 + a1 * b2 + a2 * b1 + a3 * b0)) by {
            lemma_mul_distributive_4_terms(s3 as int, a0 * b3, a1 * b2, a2 * b1, a3 * b0);
        }
        // s4 terms
        assert(s4 * (a0 * b4) + s4 * (a1 * b3) + s4 * (a2 * b2) + s4 * (a3 * b1) + s4 * (a4
            * b0) == s4 * (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0)) by {
            lemma_mul_distributive_5_terms(s4 as int, a0 * b4, a1 * b3, a2 * b2, a3 * b1, a4 * b0);
        }
        // s5 terms
        assert(s5 * (a1 * b4) + s5 * (a2 * b3) + s5 * (a3 * b2) + s5 * (a4 * b1) == s5 * (a1
            * b4 + a2 * b3 + a3 * b2 + a4 * b1)) by {
            lemma_mul_distributive_4_terms(s5 as int, a1 * b4, a2 * b3, a3 * b2, a4 * b1);
        }
        // s6 terms
        assert(s6 * (a2 * b4) + s6 * (a3 * b3) + s6 * (a4 * b2) == s6 * (a2 * b4 + a3 * b3 + a4
            * b2)) by {
            lemma_mul_distributive_3_terms(s6 as int, a2 * b4, a3 * b3, a4 * b2);
        }
        // s7 terms
        assert(s7 * (a3 * b4) + s7 * (a4 * b3) == s7 * (a3 * b4 + a4 * b3)) by {
            lemma_mul_is_distributive_add(s7 as int, a3 * b4, a4 * b3);
        }
    }

    // Step 4: Factor out s5 = p + 19 for high-order terms
    pow255_gt_19();
    assert(s5 == (p() + 19));

    let c0_x19 = a[1] * b[4] + a[2] * b[3] + a[3] * b[2] + a[4] * b[1];
    let c1_x19 = a[2] * b[4] + a[3] * b[3] + a[4] * b[2];
    let c2_x19 = a[3] * b[4] + a[4] * b[3];
    let c3_x19 = a[4] * b[4];

    let c0_base = a[0] * b[0];
    let c1_base = a[0] * b[1] + a[1] * b[0];
    let c2_base = a[0] * b[2] + a[1] * b[1] + a[2] * b[0];
    let c3_base = a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0];
    let c4 = a[0] * b[4] + a[1] * b[3] + a[2] * b[2] + a[3] * b[1] + a[4] * b[0];

    let c0 = c0_base + 19 * c0_x19;
    let c1 = c1_base + 19 * c1_x19;
    let c2 = c2_base + 19 * c2_x19;
    let c3 = c3_base + 19 * c3_x19;

    // Group in preparation for the s5 = p+19 substitution
    assert(u64_5_as_nat(a) * u64_5_as_nat(b) == s4 * c4 + s3 * (s5 * c3_x19 + c3_base) + s2
        * (s5 * c2_x19 + c2_base) + s1 * (s5 * c1_x19 + c1_base) + (s5 * c0_x19 + c0_base)) by {
        assert(s8 * c3_x19 + s3 * c3_base == s3 * (s5 * c3_x19 + c3_base)) by {
            assert(s8 == (s3 * s5)) by {
                lemma_pow2_adds(3 * 51, 5 * 51);
            }
            lemma_mul_is_associative(s3 as int, s5 as int, c3_x19);
            lemma_mul_is_distributive_add(s3 as int, s5 * c3_x19, c3_base);
        }

        assert(s7 * c2_x19 + s2 * c2_base == s2 * (s5 * c2_x19 + c2_base)) by {
            assert(s7 == (s2 * s5)) by {
                lemma_pow2_adds(2 * 51, 5 * 51);
            }
            lemma_mul_is_associative(s2 as int, s5 as int, c2_x19);
            lemma_mul_is_distributive_add(s2 as int, s5 * c2_x19, c2_base);
        }

        assert(s6 * c1_x19 + s1 * c1_base == s1 * (s5 * c1_x19 + c1_base)) by {
            assert(s6 == (s1 * s5)) by {
                lemma_pow2_adds(1 * 51, 5 * 51);
            }
            lemma_mul_is_associative(s1 as int, s5 as int, c1_x19);
            lemma_mul_is_distributive_add(s1 as int, s5 * c1_x19, c1_base);
        }
    }

    // Step 5: Substitute s5 = p + 19
    assert(s5 * c3_x19 + c3_base == p() * c3_x19 + c3) by {
        lemma_mul_is_distributive_add(c3_x19 as int, p() as int, 19);
    }

    assert(s5 * c2_x19 + c2_base == p() * c2_x19 + c2) by {
        lemma_mul_is_distributive_add(c2_x19 as int, p() as int, 19);
    }

    assert(s5 * c1_x19 + c1_base == p() * c1_x19 + c1) by {
        lemma_mul_is_distributive_add(c1_x19 as int, p() as int, 19);
    }

    assert(s5 * c0_x19 + c0_base == p() * c0_x19 + c0) by {
        lemma_mul_is_distributive_add(c0_x19 as int, p() as int, 19);
    }

    // Regroup: X * p() + Y
    assert(u64_5_as_nat(a) * u64_5_as_nat(b) == p() * (s3 * c3_x19 + s2 * c2_x19 + s1 * c1_x19
        + c0_x19) + (s4 * c4 + s3 * c3 + s2 * c2 + s1 * c1 + c0)) by {
        lemma_mul_is_distributive_add(s3 as int, p() * c3_x19, c3 as int);
        lemma_mul_is_distributive_add(s2 as int, p() * c2_x19, c2 as int);
        lemma_mul_is_distributive_add(s1 as int, p() * c1_x19, c1 as int);

        assert(s3 * (p() * c3_x19) + s2 * (p() * c2_x19) + s1 * (p() * c1_x19) + p() * c0_x19
            == p() * (s3 * c3_x19 + s2 * c2_x19 + s1 * c1_x19 + c0_x19)) by {
            lemma_mul_is_associative(s3 as int, c3_x19 as int, p() as int);
            lemma_mul_is_associative(s2 as int, c2_x19 as int, p() as int);
            lemma_mul_is_associative(s1 as int, c1_x19 as int, p() as int);

            lemma_mul_is_distributive_add(p() as int, s3 * c3_x19, s2 * c2_x19);
            lemma_mul_is_distributive_add(p() as int, s3 * c3_x19 + s2 * c2_x19, s1 * c1_x19);
            lemma_mul_is_distributive_add(
                p() as int,
                s3 * c3_x19 + s2 * c2_x19 + s1 * c1_x19,
                c0_x19 as int,
            );
        }
    }

    // Step 6: Take mod p
    let k = (s3 * c3_x19 + s2 * c2_x19 + s1 * c1_x19 + c0_x19);
    let sum = (s4 * c4 + s3 * c3 + s2 * c2 + s1 * c1 + c0);

    assert(u64_5_as_nat(a) * u64_5_as_nat(b) == k * p() + sum);
    assert(k * p() + sum == (k as nat) * p() + (sum as nat));

    assert((u64_5_as_nat(a) * u64_5_as_nat(b)) % p() == ((k as nat) * p() + (sum as nat)) % p());
    assert(((k as nat) * p() + (sum as nat)) % p() == (sum as nat) % p()) by {
        lemma_mod_sum_factor(k as int, sum as int, p() as int);
    }
}

/// A FieldElement51 with limbs [1, 0, 0, 0, 0] has canonical value 1.
pub proof fn lemma_fe51_unit_is_one(fe: &FieldElement51)
    requires
        fe.limbs[0] == 1,
        fe.limbs[1] == 0,
        fe.limbs[2] == 0,
        fe.limbs[3] == 0,
        fe.limbs[4] == 0,
    ensures
        fe51_as_canonical_nat(fe) == 1,
{
    assert(fe51_as_nat(fe) == 1nat) by {
        reveal(pow2);
        lemma_mul_by_zero_is_zero(pow2(51) as int);
        lemma_mul_by_zero_is_zero(pow2(102) as int);
        lemma_mul_by_zero_is_zero(pow2(153) as int);
        lemma_mul_by_zero_is_zero(pow2(204) as int);
    }
    p_gt_2();
    lemma_small_mod(1nat, p());
}

// =============================================================================
// nat_to_fe51 lemmas
// =============================================================================

/// Each limb of nat_to_fe51(n) is less than pow2(51).
pub proof fn lemma_nat_to_fe51_bounded(n: nat)
    ensures
        forall|i: int| 0 <= i < 5 ==> (nat_to_fe51(n).limbs[i] as nat) < pow2(51),
{
    let b = pow2(51) as int;
    lemma_pow2_pos(51);

    // Each limb is (something) % pow2(51), which is < pow2(51)
    vstd::arithmetic::div_mod::lemma_mod_bound(n as int, b);
    vstd::arithmetic::div_mod::lemma_mod_bound((n / pow2(51)) as int, b);
    vstd::arithmetic::div_mod::lemma_mod_bound((n / pow2(102)) as int, b);
    vstd::arithmetic::div_mod::lemma_mod_bound((n / pow2(153)) as int, b);
    vstd::arithmetic::div_mod::lemma_mod_bound((n / pow2(204)) as int, b);
}

/// The base-2^51 decomposition reconstructs the original value for n < pow2(255).
pub proof fn lemma_nat_to_fe51_roundtrip(n: nat)
    requires
        n < pow2(255),
    ensures
        u64_5_as_nat(nat_to_fe51(n).limbs) == n,
{
    let b = pow2(51) as int;
    lemma_pow2_pos(51);
    lemma_pow2_pos(102);
    lemma_pow2_pos(153);
    lemma_pow2_pos(204);

    // Decompose n into base-2^51 digits using fundamental_div_mod.
    let n0 = (n % pow2(51)) as nat;
    let q0 = (n / pow2(51)) as nat;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, b);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(n as int, b);

    let n1 = (q0 % pow2(51)) as nat;
    let q1 = (q0 / pow2(51)) as nat;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q0 as int, b);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(q0 as int, b);

    let n2 = (q1 % pow2(51)) as nat;
    let q2 = (q1 / pow2(51)) as nat;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q1 as int, b);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(q1 as int, b);

    let n3 = (q2 % pow2(51)) as nat;
    let q3 = (q2 / pow2(51)) as nat;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q2 as int, b);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(q2 as int, b);

    let n4 = (q3 % pow2(51)) as nat;
    let q4 = (q3 / pow2(51)) as nat;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q3 as int, b);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(q3 as int, b);

    // Show q3 < pow2(51), hence q4 == 0 and n4 == q3.
    // n < pow2(255) = pow2(51) * pow2(204), so n/pow2(204) < pow2(51).
    // Use chained division to establish q3 = n / pow2(204).
    assert(pow2(51) * pow2(51) == pow2(102)) by { lemma_pow2_adds(51, 51); }
    assert(pow2(102) * pow2(51) == pow2(153)) by { lemma_pow2_adds(102, 51); }
    assert(pow2(153) * pow2(51) == pow2(204)) by { lemma_pow2_adds(153, 51); }
    assert(pow2(51) * pow2(204) == pow2(255)) by { lemma_pow2_adds(51, 204); }

    // Chain: q0 = n/b, q1 = q0/b = n/b^2, q2 = q1/b = n/b^3, q3 = q2/b = n/b^4
    vstd::arithmetic::div_mod::lemma_div_denominator(n as int, b, b);
    assert(q1 == (n / pow2(102)) as nat);

    vstd::arithmetic::div_mod::lemma_div_denominator(n as int, pow2(102) as int, b);
    assert(q2 == (n / pow2(153)) as nat);

    vstd::arithmetic::div_mod::lemma_div_denominator(n as int, pow2(153) as int, b);
    assert(q3 == (n / pow2(204)) as nat);

    // q3 < pow2(51) because n < pow2(51) * pow2(204)
    assert(q3 < pow2(51)) by {
        if q3 >= pow2(51) {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, pow2(204) as int);
            lemma_mul_inequality(pow2(51) as int, q3 as int, pow2(204) as int);
            lemma_mul_is_commutative(pow2(51) as int, pow2(204) as int);
            lemma_mul_is_commutative(q3 as int, pow2(204) as int);
        }
    }

    assert(q4 == 0) by {
        vstd::arithmetic::div_mod::lemma_basic_div(q3 as int, b);
    }

    assert(n4 == q3) by {
        vstd::arithmetic::div_mod::lemma_small_mod(q3 as nat, pow2(51));
    }

    // Now prove the reconstruction identity:
    // n = n0 + pow2(51)*n1 + pow2(102)*n2 + pow2(153)*n3 + pow2(204)*q3
    assert(pow2(51) * pow2(102) == pow2(153)) by { lemma_pow2_adds(51, 102); }
    assert(pow2(51) * pow2(153) == pow2(204)) by { lemma_pow2_adds(51, 153); }

    // n = b*q0 + n0
    //   = b*(b*q1 + n1) + n0 = b*b*q1 + b*n1 + n0 = pow2(102)*q1 + pow2(51)*n1 + n0
    lemma_mul_is_distributive_add(pow2(51) as int, (pow2(51) * q1) as int, n1 as int);
    lemma_mul_is_associative(pow2(51) as int, pow2(51) as int, q1 as int);

    // ... = pow2(102)*(b*q2 + n2) + pow2(51)*n1 + n0
    //     = pow2(153)*q2 + pow2(102)*n2 + pow2(51)*n1 + n0
    lemma_mul_is_distributive_add(pow2(102) as int, (pow2(51) * q2) as int, n2 as int);
    lemma_mul_is_associative(pow2(102) as int, pow2(51) as int, q2 as int);
    lemma_mul_is_commutative(pow2(102) as int, pow2(51) as int);

    // ... = pow2(153)*(b*q3 + n3) + pow2(102)*n2 + pow2(51)*n1 + n0
    //     = pow2(204)*q3 + pow2(153)*n3 + pow2(102)*n2 + pow2(51)*n1 + n0
    lemma_mul_is_distributive_add(pow2(153) as int, (pow2(51) * q3) as int, n3 as int);
    lemma_mul_is_associative(pow2(153) as int, pow2(51) as int, q3 as int);
    lemma_mul_is_commutative(pow2(153) as int, pow2(51) as int);

    // Prove the limb values fit in u64 so the as-u64 casts are identity.
    lemma_nat_to_fe51_bounded(n);
    assert(pow2(51) <= u64::MAX as nat) by {
        lemma2_to64();
        lemma_pow2_strictly_increases(51, 64);
    }

    // Connect nat_to_fe51 limbs to decomposition variables.
    let limbs = nat_to_fe51(n).limbs;

    // n == n0 + pow2(51)*n1 + pow2(102)*n2 + pow2(153)*n3 + pow2(204)*q3
    // which is u64_5_as_nat(limbs) since limbs encode exactly these values.
    assert(n == n0 + pow2(51) * n1 + pow2(102) * n2 + pow2(153) * n3 + pow2(204) * q3);
}

/// Corollary: fe51_as_canonical_nat(&nat_to_fe51(n)) == n for n < p().
pub proof fn lemma_nat_to_fe51_canonical(n: nat)
    requires
        n < p(),
    ensures
        fe51_as_canonical_nat(&nat_to_fe51(n)) == n,
{
    pow255_gt_19();
    // n < p() < pow2(255)
    lemma_nat_to_fe51_roundtrip(n);
    vstd::arithmetic::div_mod::lemma_small_mod(n as nat, p());
}

fn main() {
}

} // verus!
