use vstd::arithmetic::mul::lemma_mul_nonzero;
use vstd::prelude::*;

verus! {
        proof fn lemma_mul_nonzero_nat(b1: nat, b2: nat)
            requires b1 != 0,
                     b2 != 0,
            ensures b1*b2 != 0,
        {
            lemma_mul_nonzero(b1 as int, b2 as int);
        }
}
