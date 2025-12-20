#[allow(unused_imports)]
use super::core_specs::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::scalar::Scalar52;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

pub open spec fn seq_to_nat(limbs: Seq<nat>) -> nat
    decreases limbs.len(),
{
    if limbs.len() == 0 {
        0
    } else {
        limbs[0] + seq_to_nat(limbs.subrange(1, limbs.len() as int)) * pow2(52)
    }
}

pub open spec fn slice128_to_nat(limbs: &[u128]) -> nat {
    seq_to_nat(limbs@.map(|i, x| x as nat))
}

pub open spec fn seq_u64_to_nat(limbs: Seq<u64>) -> nat {
    seq_to_nat(limbs.map(|i, x| x as nat))
}

/// Convert radix-2^52 scalar limbs to natural number.
/// This is the primary spec function for Scalar52 limb interpretation.
pub open spec fn scalar52_to_nat(limbs: &[u64]) -> nat {
    seq_to_nat(limbs@.map(|i, x| x as nat))
}

#[verusfmt::skip]
pub open spec fn nine_limbs_to_nat_aux(limbs: &[u128; 9]) -> nat {
    (limbs[0] as nat) +
    (limbs[1] as nat) * pow2( 52) +
    (limbs[2] as nat) * pow2(104) +
    (limbs[3] as nat) * pow2(156) +
    (limbs[4] as nat) * pow2(208) +
    (limbs[5] as nat) * pow2(260) +
    (limbs[6] as nat) * pow2(312) +
    (limbs[7] as nat) * pow2(364) +
    (limbs[8] as nat) * pow2(416)
}

#[verusfmt::skip]
pub open spec fn five_limbs_to_nat_aux(limbs: [u64; 5]) -> nat {
                (limbs[0] as nat) +
    pow2( 52) * (limbs[1] as nat) +
    pow2(104) * (limbs[2] as nat) +
    pow2(156) * (limbs[3] as nat) +
    pow2(208) * (limbs[4] as nat)
}

/// Modular reduction of scalar52 limbs mod group order (L).
/// Returns the mathematical scalar value in [0, L).
pub open spec fn scalar52_mod_order(limbs: &[u64; 5]) -> nat {
    scalar52_to_nat(limbs) % group_order()
}

/// natural value of a 256 bit bitstring represented as array of 32 bytes
///
/// Note: This is now an alias for the shared `u8_32_as_nat` function from core_specs.
/// Both field and scalar code use the same underlying byte-to-nat conversion.
pub open spec fn bytes_to_nat(bytes: &[u8; 32]) -> nat {
    u8_32_as_nat(bytes)
}

/// Recursive version of bytes_to_nat (now delegating to core_specs)
pub open spec fn bytes_to_nat_rec(bytes: &[u8; 32], index: int) -> nat
    decreases 32 - index,
{
    u8_32_as_nat_rec(bytes, index as nat)
}

/// natural value of a 512 bit bitstring represented as array of 64 bytes
pub open spec fn bytes_wide_to_nat(bytes: &[u8; 64]) -> nat {
    // Convert bytes to nat in little-endian order using recursive helper
    bytes_wide_to_nat_rec(bytes, 0)
}

pub open spec fn bytes_wide_to_nat_rec(bytes: &[u8; 64], index: int) -> nat
    decreases 64 - index,
{
    if index >= 64 {
        0
    } else {
        (bytes[index] as nat) * pow2((index * 8) as nat) + bytes_wide_to_nat_rec(bytes, index + 1)
    }
}


// Group order: the value of L as a natural number
pub open spec fn group_order() -> nat {
    pow2(252) + 27742317777372353535851937790883648493nat
}

// Montgomery radix R = 2^260
pub open spec fn montgomery_radix() -> nat {
    pow2(260)
}

// Montgomery radix inverse under L
pub open spec fn inv_montgomery_radix() -> nat {
    0x8e84371e098e4fc4_u64 as nat + pow2(64) * 0xfb2697cda3adacf5_u64 as nat + pow2(128)
        * 0x3614e75438ffa36b_u64 as nat + pow2(192) * 0xc9db6c6f26fe918_u64 as nat
}

// Check that all limbs of a Scalar52 are properly bounded (< 2^52)
pub open spec fn limbs_bounded(s: &Scalar52) -> bool {
    forall|i: int| 0 <= i < 5 ==> s.limbs[i] < (1u64 << 52)
}

pub open spec fn spec_mul_internal(a: &Scalar52, b: &Scalar52) -> [u128; 9]
    recommends
        limbs_bounded(a),
        limbs_bounded(b),
{
    [
        ((a.limbs[0] as u128) * (b.limbs[0] as u128)) as u128,
        ((a.limbs[0] as u128) * (b.limbs[1] as u128) + (a.limbs[1] as u128) * (
        b.limbs[0] as u128)) as u128,
        ((a.limbs[0] as u128) * (b.limbs[2] as u128) + (a.limbs[1] as u128) * (b.limbs[1] as u128)
            + (a.limbs[2] as u128) * (b.limbs[0] as u128)) as u128,
        ((a.limbs[0] as u128) * (b.limbs[3] as u128) + (a.limbs[1] as u128) * (b.limbs[2] as u128)
            + (a.limbs[2] as u128) * (b.limbs[1] as u128) + (a.limbs[3] as u128) * (
        b.limbs[0] as u128)) as u128,
        ((a.limbs[0] as u128) * (b.limbs[4] as u128) + (a.limbs[1] as u128) * (b.limbs[3] as u128)
            + (a.limbs[2] as u128) * (b.limbs[2] as u128) + (a.limbs[3] as u128) * (
        b.limbs[1] as u128) + (a.limbs[4] as u128) * (b.limbs[0] as u128)) as u128,
        ((a.limbs[1] as u128) * (b.limbs[4] as u128) + (a.limbs[2] as u128) * (b.limbs[3] as u128)
            + (a.limbs[3] as u128) * (b.limbs[2] as u128) + (a.limbs[4] as u128) * (
        b.limbs[1] as u128)) as u128,
        ((a.limbs[2] as u128) * (b.limbs[4] as u128) + (a.limbs[3] as u128) * (b.limbs[3] as u128)
            + (a.limbs[4] as u128) * (b.limbs[2] as u128)) as u128,
        ((a.limbs[3] as u128) * (b.limbs[4] as u128) + (a.limbs[4] as u128) * (
        b.limbs[3] as u128)) as u128,
        ((a.limbs[4] as u128) * (b.limbs[4] as u128)) as u128,
    ]
}

} // verus!
