//! Specification functions for high-level Scalar operations

use crate::backend::serial::u64::scalar_specs::*;
#[allow(unused_imports)]
use crate::scalar::Scalar;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*; // Import all power2 functions including pow2
use vstd::prelude::*;

verus! {

/// Convert a boolean array (bits in little-endian order) to a natural number
pub open spec fn bits_to_nat(bits: &[bool; 256]) -> nat {
    bits_to_nat_rec(bits, 0)
}

pub open spec fn bits_to_nat_rec(bits: &[bool; 256], index: int) -> nat
decreases 256 - index
{
    if index >= 256 {
        0
    } else {
        let bit_value = if bits[index] { 1nat } else { 0nat };
        bit_value * pow2(index as nat) + bits_to_nat_rec(bits, index + 1)
    }
}

pub open spec fn scalar_to_nat(s: &Scalar) -> nat {
    bytes_to_nat(&s.bytes)
}

/// Checks if a Scalar satisfies the canonical representation invariants:
/// - Invariant #1: High bit (bit 255) is clear, ensuring s < 2^255
/// - Invariant #2: Scalar is reduced modulo group order, i.e., s < ℓ
pub open spec fn is_canonical_scalar(s: &Scalar) -> bool {
    // Invariant #2: Scalar is reduced (< group order)
    bytes_to_nat(&s.bytes) < group_order()
    // Invariant #1: High bit is clear (< 2^255)
    && s.bytes[31] <= 127
}

/// Returns true iff a and b are multiplicative inverses modulo group_order
/// i.e., a * b ≡ 1 (mod group_order)
pub open spec fn is_inverse(a: &Scalar, b: &Scalar) -> bool {
    (bytes_to_nat(&a.bytes) * bytes_to_nat(&b.bytes)) % group_order() == 1
}

/// Spec function to compute product of all scalars in a sequence (mod group_order)
/// Returns the natural number representation
pub open spec fn product_of_scalars(scalars: Seq<Scalar>) -> nat
    decreases scalars.len()
{
    if scalars.len() == 0 {
        1
    } else {
        (product_of_scalars(scalars.skip(1)) * bytes_to_nat(&scalars[0].bytes)) % group_order()
    }
}

/// Spec function to compute sum of all scalars in a sequence (mod group_order)
/// Returns the natural number representation
pub open spec fn sum_of_scalars(scalars: Seq<Scalar>) -> nat
    decreases scalars.len()
{
    if scalars.len() == 0 {
        0
    } else {
        (sum_of_scalars(scalars.skip(1)) + bytes_to_nat(&scalars[0].bytes)) % group_order()
    }
}

/// Returns true iff a scalar's byte representation equals the given natural number (mod group_order)
pub open spec fn scalar_congruent_nat(s: &Scalar, n: nat) -> bool {
    bytes_to_nat(&s.bytes) % group_order() == n % group_order()
}

/// Returns true iff a scalar is the inverse of a natural number (mod group_order)
pub open spec fn is_inverse_of_nat(s: &Scalar, n: nat) -> bool {
    (bytes_to_nat(&s.bytes) * n) % group_order() == 1
}

/// Returns true iff a byte array represents a clamped integer for X25519.
/// A clamped integer has:
/// - The 3 least significant bits cleared (divisible by 8)
/// - Bit 255 (MSB) cleared (< 2^255)
/// - Bit 254 set (>= 2^254)
/// This creates values in range: 2^254 + 8*{0, 1, 2, ..., 2^251 - 1}
pub open spec fn is_clamped_integer(bytes: &[u8; 32]) -> bool {
    // The 3 least significant bits are cleared (divisible by 8)
    bytes[0] & 0b0000_0111 == 0
    // Bit 255 (MSB) is cleared, making it < 2^255
    && bytes[31] & 0b1000_0000 == 0
    // Bit 254 is set, so result >= 2^254
    && bytes[31] & 0b0100_0000 == 0b0100_0000
}

// spec functions for NAF
// integer value of a NAF
pub open spec fn reconstruct(naf: Seq<int>) -> int
    decreases naf.len()
{
    if naf.len() == 0 { 0 }
    else { naf[0] + 2 * reconstruct(naf.skip(1)) }
}

/// Predicate describing a valid width-w Non-Adjacent Form.
pub open spec fn is_valid_naf(naf: Seq<int>, w: nat) -> bool
    recommends 2 <= w <= 8
    decreases naf.len()
{
    forall |i: int| 0 <= i < naf.len() ==>
        // each digit is odd or zero
        ((#[trigger] naf[i]) == 0 || (#[trigger] naf[i]) % 2 != 0) &&
        // bounded magnitude
        -pow2((w - 1) as nat) < (#[trigger] naf[i]) && (#[trigger] naf[i]) < pow2((w - 1) as nat) &&
        // no adjacent nonzero digits
        !((#[trigger] naf[i]) != 0 && i + 1 < naf.len() && naf[i + 1] != 0)
}

} // verus!
