//! Specification functions for high-level Scalar operations
#[allow(unused_imports)]
use crate::scalar::Scalar;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

#[allow(unused_imports)]
use super::core_specs::*;
#[allow(unused_imports)]
use super::scalar52_specs::*;

verus! {

pub open spec fn scalar_to_nat(s: &Scalar) -> nat {
    bytes32_to_nat(&s.bytes)
}

/// Returns the mathematical value of a Scalar modulo the group order.
/// This is the value used in scalar multiplication: [n]P where n = spec_scalar(s).
pub open spec fn spec_scalar(s: &Scalar) -> nat {
    bytes32_to_nat(&s.bytes) % group_order()
}

/// Checks if a Scalar satisfies the canonical representation invariants:
/// - Invariant #1: High bit (bit 255) is clear, ensuring s < 2^255
/// - Invariant #2: Scalar is reduced modulo group order, i.e., s < ℓ
pub open spec fn is_canonical_scalar(s: &Scalar) -> bool {
    // Invariant #2: Scalar is reduced (< group order)
    bytes32_to_nat(&s.bytes)
        < group_order()
    // Invariant #1: High bit is clear (< 2^255)
     && s.bytes[31] <= 127
}

/// Returns true iff a and b are multiplicative inverses modulo group_order
/// i.e., a * b ≡ 1 (mod group_order)
pub open spec fn is_inverse(a: &Scalar, b: &Scalar) -> bool {
    (bytes32_to_nat(&a.bytes) * bytes32_to_nat(&b.bytes)) % group_order() == 1
}

/// Spec function to compute product of all scalars in a sequence (mod group_order)
/// Returns the natural number representation
/// Note: Processes from back to front to match iterative loop order
pub open spec fn product_of_scalars(scalars: Seq<Scalar>) -> nat
    decreases scalars.len(),
{
    if scalars.len() == 0 {
        1
    } else {
        let last = (scalars.len() - 1) as int;
        (product_of_scalars(scalars.subrange(0, last)) * bytes32_to_nat(&scalars[last].bytes))
            % group_order()
    }
}

/// Spec function to compute sum of all scalars in a sequence (mod group_order)
/// Returns the natural number representation
/// Note: Processes from back to front to match iterative loop order
pub open spec fn sum_of_scalars(scalars: Seq<Scalar>) -> nat
    decreases scalars.len(),
{
    if scalars.len() == 0 {
        0
    } else {
        let last = (scalars.len() - 1) as int;
        (sum_of_scalars(scalars.subrange(0, last)) + bytes32_to_nat(&scalars[last].bytes))
            % group_order()
    }
}

/// Returns true iff a scalar's byte representation equals the given natural number (mod group_order)
pub open spec fn scalar_congruent_nat(s: &Scalar, n: nat) -> bool {
    bytes32_to_nat(&s.bytes) % group_order() == n % group_order()
}

/// Returns true iff a scalar is the inverse of a natural number (mod group_order)
pub open spec fn is_inverse_of_nat(s: &Scalar, n: nat) -> bool {
    (bytes32_to_nat(&s.bytes) * n) % group_order() == 1
}

/// Returns true iff a byte array represents a clamped integer for X25519.
/// A clamped integer has:
/// - The 3 least significant bits cleared (divisible by 8)
/// - Bit 255 (MSB) cleared (< 2^255), which means bytes[31] <= 127
/// - Bit 254 set (>= 2^254)
/// This creates values in range: 2^254 + 8*{0, 1, 2, ..., 2^251 - 1}
pub open spec fn is_clamped_integer(bytes: &[u8; 32]) -> bool {
    // The 3 least significant bits are cleared (divisible by 8)
    bytes[0] & 0b0000_0111
        == 0
    // Bit 255 (MSB) is cleared, making it < 2^255
     && bytes[31] & 0b1000_0000 == 0
    // Bit 254 is set, so result >= 2^254
     && bytes[31] & 0b0100_0000
        == 0b0100_0000
    // MSB cleared implies bytes[31] <= 127 (needed for mul_req precondition)
     && bytes[31] <= 127
}

/// Spec function for clamping a byte array to produce a valid X25519 scalar.
/// This is the spec-level version of the `clamp_integer` exec function.
///
/// The clamping operation:
/// - Clears the 3 least significant bits (bits 0-2 of byte 0)
/// - Clears bit 255 (bit 7 of byte 31)
/// - Sets bit 6 of byte 31)
///
/// This produces a value in the range [2^254, 2^255) that is divisible by 8.
pub open spec fn spec_clamp_integer(bytes: [u8; 32]) -> [u8; 32] {
    // Build the result array element by element
    [
        bytes[0] & 0b1111_1000,  // Clear low 3 bits of byte 0
        bytes[1],
        bytes[2],
        bytes[3],
        bytes[4],
        bytes[5],
        bytes[6],
        bytes[7],
        bytes[8],
        bytes[9],
        bytes[10],
        bytes[11],
        bytes[12],
        bytes[13],
        bytes[14],
        bytes[15],
        bytes[16],
        bytes[17],
        bytes[18],
        bytes[19],
        bytes[20],
        bytes[21],
        bytes[22],
        bytes[23],
        bytes[24],
        bytes[25],
        bytes[26],
        bytes[27],
        bytes[28],
        bytes[29],
        bytes[30],
        (bytes[31] & 0b0111_1111) | 0b0100_0000,  // Clear bit 7 and set bit 6 of byte 31
    ]
}

// spec functions for NAF
// integer value of a NAF, little-endian
pub open spec fn reconstruct(naf: Seq<i8>) -> int
    decreases naf.len(),
{
    if naf.len() == 0 {
        0
    } else {
        (naf[0] as int) + 2 * reconstruct(naf.skip(1))
    }
}

/// Predicate describing a valid width-w Non-Adjacent Form.
pub open spec fn is_valid_naf(naf: Seq<i8>, w: nat) -> bool {
    forall|i: int|
        0 <= i < naf.len() ==> {
            let digit = (#[trigger] naf[i]) as int;
            // Each nonzero digit is odd and within bound
            (digit == 0 || (digit % 2 != 0 && -pow2((w - 1) as nat) < digit && digit < pow2(
                (w - 1) as nat,
            ))) &&
            // At most one nonzero in any w consecutive digits
            forall|j: int|
                1 <= j < w && #[trigger] (i + j) < naf.len() ==> !(digit != 0 && (naf[#[trigger] (i
                    + j)] as int) != 0)
        }
}

// Spec functions for radix-2^w representation (generic)
/// Reconstructs an integer from a radix-2^w digit representation
/// The scalar is represented as: a_0 + a_1*2^w + a_2*2^(2w) + ...
pub open spec fn reconstruct_radix_2w(digits: Seq<i8>, w: nat) -> int
    decreases digits.len(),
{
    if digits.len() == 0 {
        0
    } else {
        (digits[0] as int) + pow2(w) * reconstruct_radix_2w(digits.skip(1), w)
    }
}

/// Predicate describing a valid radix-2^w representation with signed digits
/// For window size w, coefficients are in [-2^(w-1), 2^(w-1)) for most indices,
/// and [-2^(w-1), 2^(w-1)] for the last non-zero index
pub open spec fn is_valid_radix_2w(digits: &[i8; 64], w: nat, digits_count: nat) -> bool {
    4 <= w <= 8 && digits_count <= 64 && forall|i: int|
        0 <= i < digits_count ==> {
            let bound = pow2((w - 1) as nat) as int;
            if i < digits_count - 1 {
                -bound <= (#[trigger] digits[i]) && (#[trigger] digits[i]) < bound
            } else {
                -bound <= (#[trigger] digits[i]) && (#[trigger] digits[i]) <= bound
            }
        }
}

// Spec functions for radix-16 representation (w=4 specialization)
/// Reconstructs the integer value from a radix-16 representation
/// This is just radix-2^w with w=4
pub open spec fn reconstruct_radix_16(digits: Seq<i8>) -> int {
    reconstruct_radix_2w(digits, 4)
}

/// Predicate describing a valid radix-16 representation with signed digits
/// This is just radix-2^w with w=4
pub open spec fn is_valid_radix_16(digits: &[i8; 64]) -> bool {
    is_valid_radix_2w(digits, 4, 64)
}

/// Simple bounds check for radix-16 digits: all digits in [-8, 8]
/// This is a simpler predicate than is_valid_radix_16 for easier use
pub open spec fn radix_16_digit_bounded(digit: i8) -> bool {
    -8 <= digit && digit <= 8
}

/// All radix-16 digits are bounded by [-8, 8]
pub open spec fn radix_16_all_bounded(digits: &[i8; 64]) -> bool {
    forall|i: int| 0 <= i < 64 ==> radix_16_digit_bounded(#[trigger] digits[i])
}

/// Convert a boolean slice (bits in big-endian order) to a natural number
/// This interprets bits[0] as the most significant bit
/// Used for scalar multiplication where bits are processed MSB first
pub open spec fn bits_be_to_nat(bits: &[bool], len: int) -> nat
    recommends
        0 <= len <= bits.len(),
    decreases len,
{
    if len <= 0 {
        0
    } else {
        let bit_value = if bits[len - 1] {
            1nat
        } else {
            0nat
        };
        bit_value + 2 * bits_be_to_nat(bits, len - 1)
    }
}

// ============================================================================
// Helper specs for batch_invert
// ============================================================================
/// Partial product of scalars from 0 to n-1 (mod group_order)
/// This computes: ∏_{j=0}^{n-1} scalars[j] (mod L)
pub open spec fn partial_product(scalars: Seq<Scalar>, n: int) -> nat
    recommends
        0 <= n <= scalars.len(),
    decreases n,
{
    if n <= 0 {
        1nat
    } else {
        (partial_product(scalars, n - 1) * bytes32_to_nat(&scalars[n - 1].bytes)) % group_order()
    }
}

/// Partial product in Montgomery form (multiplied by R)
/// This represents what acc holds in the first loop: R * ∏_{j=0}^{i-1} inputs[j] (mod L)
pub open spec fn partial_product_montgomery(scalars: Seq<Scalar>, n: int) -> nat
    recommends
        0 <= n <= scalars.len(),
{
    (montgomery_radix() * partial_product(scalars, n)) % group_order()
}

/// Lemma: partial_product equals product_of_scalars when n equals length
pub proof fn lemma_partial_product_full(scalars: Seq<Scalar>)
    ensures
        partial_product(scalars, scalars.len() as int) == product_of_scalars(scalars),
    decreases scalars.len(),
{
    if scalars.len() == 0 {
        // Base case: both are 1
    } else {
        let n = scalars.len() as int;
        let prefix = scalars.subrange(0, n - 1);

        // Inductive step: partial_product(scalars, n-1) == product_of_scalars(prefix)
        lemma_partial_product_full(prefix);

        // Now show partial_product(scalars, n) == product_of_scalars(scalars)
        assert(partial_product(scalars, n) == (partial_product(scalars, n - 1) * bytes32_to_nat(
            &scalars[n - 1].bytes,
        )) % group_order());
        assert(product_of_scalars(scalars) == (product_of_scalars(prefix) * bytes32_to_nat(
            &scalars[n - 1].bytes,
        )) % group_order());

        // Need: partial_product(scalars, n-1) == partial_product(prefix, n-1)
        // This follows because scalars and prefix agree on indices 0..n-1
        lemma_partial_product_prefix_eq(scalars, prefix, n - 1);
    }
}

/// Lemma: partial_product only depends on prefix elements
pub proof fn lemma_partial_product_prefix_eq(scalars1: Seq<Scalar>, scalars2: Seq<Scalar>, n: int)
    requires
        0 <= n <= scalars1.len(),
        0 <= n <= scalars2.len(),
        forall|j: int| 0 <= j < n ==> scalars1[j] == scalars2[j],
    ensures
        partial_product(scalars1, n) == partial_product(scalars2, n),
    decreases n,
{
    if n <= 0 {
        // Base case
    } else {
        lemma_partial_product_prefix_eq(scalars1, scalars2, n - 1);
    }
}

/// Helper lemma: if a ≡ c (mod L) and b ≡ d (mod L), then a*b ≡ c*d (mod L)
pub proof fn lemma_mul_congruence(a: nat, b: nat, c: nat, d: nat, L: nat)
    requires
        L > 0,
        a % L == c % L,
        b % L == d % L,
    ensures
        (a * b) % L == (c * d) % L,
{
    lemma_mul_mod_noop_general(a as int, b as int, L as int);
    lemma_mul_mod_noop_general(c as int, d as int, L as int);
}

pub proof fn lemma_montgomery_mul_partial_product(
    acc_before: nat,
    tmp: nat,
    acc_after: nat,
    scalars: Seq<Scalar>,
    i: int,
)
    requires
        0 <= i < scalars.len(),
        acc_before % group_order() == (montgomery_radix() * partial_product(scalars, i))
            % group_order(),
        tmp % group_order() == (bytes32_to_nat(&scalars[i].bytes) * montgomery_radix())
            % group_order(),
        (acc_after * montgomery_radix()) % group_order() == (acc_before * tmp) % group_order(),
    ensures
        acc_after % group_order() == (montgomery_radix() * partial_product(scalars, i + 1))
            % group_order(),
{
    use crate::lemmas::scalar_lemmas::lemma_cancel_mul_pow2_mod;
    let (L, R, pp_i, s_i) = (
        group_order(),
        montgomery_radix(),
        partial_product(scalars, i),
        bytes32_to_nat(&scalars[i].bytes),
    );
    lemma_mul_congruence(acc_before, tmp, R * pp_i, s_i * R, L);
    assert((R * pp_i) * (s_i * R) == (R * pp_i * s_i) * R) by (nonlinear_arith);
    lemma_cancel_mul_pow2_mod(acc_after, R * pp_i * s_i, R);
    lemma_mul_mod_noop_right(R as int, (pp_i * s_i) as int, L as int);
    assert(R * pp_i * s_i == R * (pp_i * s_i)) by (nonlinear_arith);
}

pub proof fn lemma_backward_loop_acc_invariant(
    acc_before: nat,
    input_val: nat,
    acc_after: nat,
    scalars: Seq<Scalar>,
    i: int,
)
    requires
        0 <= i < scalars.len(),
        (acc_before * partial_product(scalars, i + 1)) % group_order() == 1nat,
        input_val % group_order() == (bytes32_to_nat(&scalars[i].bytes) * montgomery_radix())
            % group_order(),
        (acc_after * montgomery_radix()) % group_order() == (acc_before * input_val)
            % group_order(),
    ensures
        (acc_after * partial_product(scalars, i)) % group_order() == 1nat,
{
    use crate::lemmas::scalar_lemmas::lemma_cancel_mul_pow2_mod;
    let (L, R, pp_i, s_i) = (
        group_order(),
        montgomery_radix(),
        partial_product(scalars, i),
        bytes32_to_nat(&scalars[i].bytes),
    );
    lemma_mul_congruence(acc_before, input_val, acc_before, s_i * R, L);
    assert((acc_before * s_i) * R == acc_before * (s_i * R)) by (nonlinear_arith);
    lemma_cancel_mul_pow2_mod(acc_after, acc_before * s_i, R);
    lemma_mul_congruence(acc_after, pp_i, acc_before * s_i, pp_i, L);
    assert((acc_before * s_i) * pp_i == acc_before * (pp_i * s_i)) by (nonlinear_arith);
    lemma_mul_mod_noop_right(acc_before as int, (pp_i * s_i) as int, L as int);
}

pub proof fn lemma_invert_chain(acc_before: nat, acc_after: nat, final_acc: nat, product: nat)
    requires
        acc_before % group_order() == (montgomery_radix() * product) % group_order(),
        (acc_after * acc_before) % group_order() == (montgomery_radix() * montgomery_radix())
            % group_order(),
        (final_acc * montgomery_radix()) % group_order() == acc_after % group_order(),
        final_acc < group_order(),
    ensures
        (final_acc * product) % group_order() == 1nat % group_order(),
{
    use crate::lemmas::scalar_lemmas::lemma_cancel_mul_pow2_mod;
    let (L, R) = (group_order(), montgomery_radix());
    lemma_mul_congruence(final_acc * R, acc_before, acc_after, acc_before, L);
    lemma_mul_congruence(final_acc * R, acc_before, final_acc * R, R * product, L);
    assert((final_acc * R) * (R * product) == ((final_acc * product) * R) * R) by (nonlinear_arith);
    assert(R * R == 1 * R * R) by (nonlinear_arith);
    lemma_cancel_mul_pow2_mod((final_acc * product) * R, R, R);
    lemma_cancel_mul_pow2_mod(final_acc * product, 1, R);
}

pub proof fn lemma_backward_loop_is_inverse(
    acc_before: nat,
    scratch_val: nat,
    result_m: nat,
    result: nat,
    scalars: Seq<Scalar>,
    i: int,
)
    requires
        0 <= i < scalars.len(),
        (acc_before * partial_product(scalars, i + 1)) % group_order() == 1nat,
        scratch_val % group_order() == (montgomery_radix() * partial_product(scalars, i))
            % group_order(),
        (result_m * montgomery_radix()) % group_order() == (acc_before * scratch_val)
            % group_order(),
        result_m < pow2(256),
        result == result_m,
    ensures
        (result * bytes32_to_nat(&scalars[i].bytes)) % group_order() == 1nat,
{
    use crate::lemmas::scalar_lemmas::lemma_cancel_mul_pow2_mod;
    let (L, R, pp_i, s_i) = (
        group_order(),
        montgomery_radix(),
        partial_product(scalars, i),
        bytes32_to_nat(&scalars[i].bytes),
    );
    lemma_mul_congruence(acc_before, scratch_val, acc_before, R * pp_i, L);
    assert(acc_before * (R * pp_i) == (acc_before * pp_i) * R) by (nonlinear_arith);
    lemma_cancel_mul_pow2_mod(result_m, acc_before * pp_i, R);
    lemma_mul_congruence(result_m, s_i, acc_before * pp_i, s_i, L);
    assert((acc_before * pp_i) * s_i == acc_before * (pp_i * s_i)) by (nonlinear_arith);
    lemma_mul_mod_noop_right(acc_before as int, (pp_i * s_i) as int, L as int);
}

} // verus!
