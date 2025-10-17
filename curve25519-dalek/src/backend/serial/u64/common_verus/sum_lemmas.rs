#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;

use super::mul_lemmas::*;

verus! {

pub open spec fn add(a: nat, b: nat) -> nat
{
    a + b
}

pub open spec fn seq_sum(coefs: Seq<nat>, k: nat) -> nat
    decreases k
{
    if (k == 0){
        coefs[0]
    }
    else {
        seq_sum(coefs, (k-1) as nat) + coefs[k as int]
    }
}

pub proof fn sum_bounds(coefs: Seq<nat>, k: nat, s: nat)
    requires
        k <= coefs.len(),
        forall |i: nat| 0 <= i <= k ==> #[trigger] coefs[i as int] <= pow2((i + 1) * s) - pow2(i * s)
    ensures
        seq_sum(coefs, k) <= pow2((k + 1) * s) - 1
    decreases k
{
    if (k == 0){
        assert(pow2(0) ==1) by {
            lemma2_to64();
        }
    }
    else {
        assert(
            seq_sum(coefs, k)
            ==
            seq_sum(coefs, (k-1) as nat) + coefs[k as int]
        ) by {
            reveal_with_fuel(seq_sum, 1);
        }

        assert(seq_sum(coefs, (k-1) as nat) <= pow2(k  * s) - 1) by {
            sum_bounds(coefs, (k-1) as nat, s);
        }

        // "requires" for i = k
        assert(coefs[k as int] <= pow2((k + 1) * s) - pow2(k * s));

        assert((pow2((k + 1) * s) - pow2(k * s)) + (pow2(k  * s) - 1) == pow2((k + 1) * s) - 1) by {
            assert(pow2((k + 1) * s) >= pow2(k * s)) by {
                if (s > 0) {
                    assert((k + 1) * s == k * s + s) by {
                        lemma_mul_is_distributive_add_other_way(s as int, k as int, 1);
                    }
                    lemma_pow2_strictly_increases(k * s, (k + 1nat) * s);
                }
            }

            assert(pow2((k + 1) * s) >= 1) by {
                assert(1 == pow2(0)) by {
                    lemma2_to64();
                }
                if (s > 0){
                    assert(0 < (k + 1) * s) by {
                        lemma_mul_strictly_positive((k + 1) as int, s as int);
                    }
                    lemma_pow2_strictly_increases(0, (k + 1nat) * s);
                }
            }
        }
    }
}

pub open spec fn fold_sum(coefs: Seq<nat>, k: nat) -> nat
{
    let add_local = (|i: nat, j: nat| add(i,j));
    coefs.take(k as int).fold_left(0nat, add_local)
}

pub proof fn fold_sum_bounds(coefs: Seq<nat>, k: nat, s: nat)
    requires
        k <= coefs.len(),
        forall |i: nat| 0 <= i <= k ==> #[trigger] coefs[i as int] <= pow2((i + 1) * s) - pow2(i * s)
    ensures
        fold_sum(coefs, k) <= pow2((k + 1) * s) - 1
{
    assume(false);
}

}
