//! Lemmas for proving `as_montgomery` correctness.

#[allow(unused_imports)]
use crate::specs::scalar_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs_u64::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

#[allow(unused_imports)]
use super::common_lemmas::pow_lemmas::*;
#[allow(unused_imports)]
use super::scalar_lemmas::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::constants;

verus! {

/// Specialized Montgomery variant of modular cancellation.
/// 
/// We only accept the Montgomery-specific case where r = montgomery_radix()
/// and n = group_order(), since the radix is invertible modulo the curve
/// group order.
pub proof fn lemma_mul_mod(x: nat, r: nat, a: nat, rr: nat, n: nat)
    requires
        r == montgomery_radix(),
        n == group_order(),
        ((x * r) % n) == ((a * rr) % n),
        (rr % n) == ((r * r) % n),
        n > 0,
    ensures
        (x % n) == ((a * r) % n),
{
    // Delegate to the Montgomery-specific cancellation lemma
    assert((x % n) == ((a * r) % n)) by {
        lemma_cancel_mul_montgomery_mod(x, a, rr);
    }
}

/// Helper lemma: if b ≡ c (mod n), then a*b ≡ a*c (mod n)
proof fn lemma_mul_mod_right_eq(a: nat, b: nat, c: nat, n: nat)
    requires
        n > 0,
        b % n == c % n,
    ensures
        (a * b) % n == (a * c) % n,
{
    let a_int = a as int;
    let b_int = b as int;
    let c_int = c as int;
    let n_int = n as int;

    // (a * b) % n == (a * (b % n)) % n
    assert((a * b) % n == (a * (b % n)) % n) by {
        lemma_mul_mod_noop_right(a_int, b_int, n_int);
    }

    // (a * c) % n == (a * (c % n)) % n
    assert((a * c) % n == (a * (c % n)) % n) by {
        lemma_mul_mod_noop_right(a_int, c_int, n_int);
    }

    // Since b % n == c % n, we have (a * (b % n)) % n == (a * (c % n)) % n
    // Therefore (a * b) % n == (a * c) % n
}

/// Proves that the RR constant equals R² mod L
/// 
/// RR is precomputed as R² mod L where R = montgomery_radix() = 2^260
/// and L = group_order().
pub(crate) proof fn lemma_rr_equals_radix_squared()
    ensures
        to_nat(&constants::RR.limbs) % group_order() == (montgomery_radix() * montgomery_radix())
            % group_order(),
{
    // Step 1: Establish that to_nat equals five_limbs_to_nat_aux for RR
    lemma_five_limbs_equals_to_nat(&constants::RR.limbs);

    // Step 2: Establish pow2 values needed for the computation
    // These are needed to connect montgomery_radix() = pow2(260) to concrete values
    lemma2_to64();
    lemma2_to64_rest();
    lemma_pow2_adds(52, 52);   // pow2(104)
    lemma_pow2_adds(104, 52);  // pow2(156)
    lemma_pow2_adds(156, 52);  // pow2(208)
    lemma_pow2_adds(208, 44);  // pow2(252)
    lemma_pow2_adds(208, 52);  // pow2(260)

    // Step 3: Get the concrete value of RR's limbs as nat
    let rr_calc: nat = five_limbs_to_nat_aux(constants::RR.limbs);

    // Step 4: Since rr_calc < group_order(), rr_calc % group_order() == rr_calc
    lemma_small_mod(rr_calc, group_order());

    // Step 5: Show R² mod L == rr_calc using concrete values
    // R = montgomery_radix() = 2^260 = 1852673427797059126777135760139006525652319754650249024631321344126610074238976
    // L = group_order() = 7237005577332262213973186563042994240857116359379907606001950938285454250989
    assert((1852673427797059126777135760139006525652319754650249024631321344126610074238976_nat
        * 1852673427797059126777135760139006525652319754650249024631321344126610074238976_nat)
        % 7237005577332262213973186563042994240857116359379907606001950938285454250989_nat
        == rr_calc);
}

} // verus!
