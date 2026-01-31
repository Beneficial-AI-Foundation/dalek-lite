#[allow(unused_imports)]
use super::core_specs::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::scalar::Scalar52;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// Convert a sequence of limbs to nat using 52-bit radix (Horner form).
/// This is the base recursive function for Scalar52 limb interpretation.
/// Computes: limbs[0] + limbs[1]*2^52 + limbs[2]*2^104 + ...
pub open spec fn seq_to_nat_52(limbs: Seq<nat>) -> nat
    decreases limbs.len(),
{
    if limbs.len() == 0 {
        0
    } else {
        limbs[0] + seq_to_nat_52(limbs.subrange(1, limbs.len() as int)) * pow2(52)
    }
}

pub open spec fn slice128_to_nat(limbs: &[u128]) -> nat {
    seq_to_nat_52(limbs@.map(|i, x| x as nat))
}

pub open spec fn seq_u64_to_nat(limbs: Seq<u64>) -> nat {
    seq_to_nat_52(limbs.map(|i, x| x as nat))
}

/// Convert a slice of u64 limbs to nat using 52-bit radix.
/// This is for low-level lemmas that work with raw arrays.
pub open spec fn limbs52_to_nat(limbs: &[u64]) -> nat {
    seq_to_nat_52(limbs@.map(|i, x| x as nat))
}

/// Convert a Scalar52 to its natural number representation.
/// This is the primary spec function for Scalar52 interpretation.
pub open spec fn scalar52_to_nat(s: &Scalar52) -> nat {
    limbs52_to_nat(&s.limbs)
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

// bytes32_to_nat, bytes_seq_to_nat, and bytes_to_nat_suffix (all generic)
// are now in core_specs.rs. They are imported via `use super::core_specs::*`
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

/// Relaxed bound for sub's first argument: limbs 0-3 bounded, limb 4 can exceed 2^52 by up to b[4].
/// 
/// This is needed for montgomery_reduce where the intermediate result has r4 > 2^52.
/// The sub algorithm still works correctly because:
///   - For limbs 0-3: standard bounded subtraction
///   - For limb 4: a[4] - b[4] < 2^52, so masking doesn't lose bits
/// 
/// See docs/proofs_for_montgomery_reduce/sub_and_bounds_analysis.md for detailed analysis.
pub open spec fn limbs_bounded_for_sub(a: &Scalar52, b: &Scalar52) -> bool {
    &&& forall|i: int| 0 <= i < 4 ==> a.limbs[i] < (1u64 << 52)
    &&& a.limbs[4] < (1u64 << 52) + b.limbs[4]
}

pub open spec fn limb_prod_bounded_u128(limbs1: [u64; 5], limbs2: [u64; 5], k: nat) -> bool {
    forall|i: int, j: int| 0 <= i < 5 && 0 <= j < 5 ==> (limbs1[i] * limbs2[j]) * k <= u128::MAX
}

/// Checks if a Scalar52 is in canonical form:
/// - All limbs are properly bounded (< 2^52)
/// - The value is reduced modulo group order (< L)
///
/// This is the Scalar52 equivalent of is_canonical_scalar for Scalar.
pub open spec fn is_canonical_scalar52(s: &Scalar52) -> bool {
    limbs_bounded(s) && scalar52_to_nat(s) < group_order()
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


// ============================================================================
// FUNCTION-CENTRIC PREDICATES FOR montgomery_reduce
// ============================================================================
// These predicates describe what montgomery_reduce actually needs from its input,
// without reference to how the input was obtained.

/// The limb bounds that montgomery_reduce requires to avoid overflow.
/// These are the bounds produced by mul_internal(bounded, bounded).
///
/// # Motivation
/// montgomery_reduce performs iterative computations where each iteration
/// accumulates products of limbs. To avoid overflow in u128 arithmetic,
/// we need these specific bounds on each input limb.
#[verusfmt::skip]
pub open spec fn montgomery_reduce_input_bounds(limbs: &[u128; 9]) -> bool {
    limbs[0] < pow2(104) &&  // 1 product term
    limbs[1] < pow2(105) &&  // 2 product terms
    limbs[2] < pow2(106) &&  // 3 product terms
    limbs[3] < pow2(107) &&  // 4 product terms
    limbs[4] < pow2(107) &&  // 5 product terms
    limbs[5] < pow2(107) &&  // 4 product terms
    limbs[6] < pow2(106) &&  // 3 product terms
    limbs[7] < pow2(105) &&  // 2 product terms
    limbs[8] < pow2(104)     // 1 product term
}

/// The value bound that ensures r4 < 2^52 in montgomery_reduce.
/// This is weaker than canonical_bound and is satisfied by mul_internal(bounded, bounded).
///
/// # Derivation (see docs/montgomery_reduce_r4_bound_derivation.md)
/// - r4 < 2^52 requires result_raw < 2^260
/// - result_raw = (T + N×L) / R < T/R + L (where N < R)
/// - For result_raw < 2^260: T < R × (R - L) ≈ 2^520
///
/// # Why this matters
/// - canonical_bound (T < R×L ≈ 2^512) is too strong for bounded × bounded products
/// - bounded × bounded can produce T up to 2^520, violating canonical_bound
/// - But r4_safe_bound (T < 2^520) IS satisfied, ensuring sub works correctly
/// - This allows mul to work without requiring canonical inputs
pub open spec fn montgomery_reduce_r4_safe_bound(limbs: &[u128; 9]) -> bool {
    montgomery_reduce_input_bounds(limbs) &&
    slice128_to_nat(limbs) < pow2(520)
}

/// The value bound that montgomery_reduce requires to produce a canonical output.
/// When the total value is < R * L, the intermediate result_raw will be < 2L,
/// which allows sub(result_raw, L) to produce a canonical result.
///
/// # Motivation
/// - result_raw = (input + N*L) / R, where N < R
/// - For result_raw < 2L: we need input/R + L < 2L, i.e., input < R*L
///
/// # Relationship to r4_safe_bound
/// - canonical_bound (T < 2^512) implies r4_safe_bound (T < 2^520)
/// - canonical_bound additionally ensures result < L (canonical)
pub open spec fn montgomery_reduce_canonical_bound(limbs: &[u128; 9]) -> bool {
    montgomery_reduce_input_bounds(limbs) &&
    slice128_to_nat(limbs) < montgomery_radix() * group_order()
}

/// The Montgomery reduction property: result * R ≡ input (mod L)
pub open spec fn montgomery_congruent(result: &Scalar52, limbs: &[u128; 9]) -> bool {
    (scalar52_to_nat(result) * montgomery_radix()) % group_order()
        == slice128_to_nat(limbs) % group_order()
}

// ============================================================================
// NEW: Direct Intermediate-Based Precondition for montgomery_reduce
// ============================================================================
// These specs define the true precondition: the intermediate value is bounded.
// This is a VALUE property, not a computation property.

/// L^{-1} mod R: the multiplicative inverse of group_order() modulo montgomery_radix()
/// This constant satisfies: L * L_INV_MOD_R ≡ 1 (mod R)
/// Where R = 2^260 and L = group_order()
pub open spec fn l_inv_mod_r() -> nat {
    // This is a computed constant: L^{-1} mod 2^260
    // For the actual value, see the Montgomery constant derivation
    // For now, we define it abstractly and prove its property in a lemma
    arbitrary()  // Placeholder - will be given concrete value in lemma
}

/// The Montgomery quotient N for a given T
/// N = (-T * L^{-1}) mod R = (R - (T * L^{-1}) mod R) mod R
/// This is the unique value N ∈ [0, R) such that T + N*L ≡ 0 (mod R)
pub open spec fn montgomery_quotient(t: nat) -> nat {
    let r = montgomery_radix();
    let l_inv = l_inv_mod_r();
    // N = (-T * L^{-1}) mod R
    // Use int arithmetic then cast back to nat (result is always in [0, R))
    ((r as int - ((t * l_inv) % r) as int) % (r as int)) as nat
}

/// The intermediate value in Montgomery reduction
/// intermediate = (T + N*L) / R
/// where N = montgomery_quotient(T)
pub open spec fn montgomery_intermediate(t: nat) -> nat {
    let r = montgomery_radix();
    let l = group_order();
    let n = montgomery_quotient(t);
    (t + n * l) / r
}

/// The lower limbs of L: L % 2^208
/// This is L[0] + L[1]*2^52 + L[2]*2^104 + L[3]*2^156
pub open spec fn lower_limbs_of_l() -> nat {
    group_order() % pow2(208)
}

/// The KEY precondition for montgomery_reduce:
/// The intermediate value must be strictly less than 2^260 + L - lower
/// where lower = L % 2^208 > 0
///
/// This ensures r4 = floor(intermediate / 2^208) < 2^52 + L[4]
/// which is required for sub's relaxed precondition.
///
/// This is a PURE VALUE property of T - it doesn't depend on how T was computed.
pub open spec fn montgomery_safe_input(limbs: &[u128; 9]) -> bool {
    let t = slice128_to_nat(limbs);
    let threshold = pow2(260) + group_order() - lower_limbs_of_l();
    montgomery_intermediate(t) < threshold
}

} // verus!
