# Canonicity Requirement in Montgomery Reduction

This document provides a comprehensive analysis of why `montgomery_reduce` now requires canonical inputs (`canonical_bound`), tracing the requirement from `sub`'s correctness through the entire call chain.

---

## Executive Summary

### Variable Definitions

| Variable | Definition | Value / Representation |
|----------|------------|------------------------|
| **T** | Input to Montgomery reduction | 512-bit integer, stored as `limbs: &[u128; 9]` in radix-2^52 |
| **R** | Montgomery constant | R = 2^260 |
| **L** | Ed25519 group order (prime) | L = 2^252 + 27742317777372353535851937790883648493 |
| **N** | Montgomery quotient | Uniquely determined by T such that R divides (T + N×L) |

### Function Signature

```rust
pub(crate) fn montgomery_reduce(limbs: &[u128; 9]) -> Scalar52
    requires
        // Input limbs must satisfy bounds for overflow-safe computation
        montgomery_reduce_input_bounds(limbs),
        // HAC 14.32's precondition: T < R×L ensures intermediate < 2L
        montgomery_reduce_canonical_bound(limbs),
    ensures
        limbs_bounded(&result),
        montgomery_congruent(&result, limbs),
        is_canonical_scalar52(&result),
```

### Key Requirement

The `montgomery_reduce` function requires `canonical_bound` (T < R×L) as a precondition because:

1. **`sub` requires a strict bound on `r4`**: The `sub` function needs `r4 < 2^52 + L[4]` (strict) for correctness
2. **The strict bound is provable only under canonicity**: We can prove `r4 < 2^52 + L[4]` when `canonical_bound` holds (via HAC 14.32's `intermediate < 2L` guarantee)
3. **This propagates to callers**: `mul`, `montgomery_mul`, `montgomery_square`, etc. now require at least one canonical input

An alternative approach (not requiring canonicity) would be possible if we could prove the strict bound for all inputs satisfying `r4_safe_bound`, empirical evidence suggests the bound always holds but this proof seems to be not easy.

---

## 1. Why `sub` Needs the Strict Bound on `r4`

### 1.0 Context and Variable Definitions

At the end of `montgomery_reduce`, the function calls `sub(&intermediate, &L)` to conditionally subtract L from the intermediate result. The variables in this section are:

| Variable | Definition | Notes |
|----------|------------|-------|
| `intermediate` | A `Scalar52` holding the 5 limbs `[r0, r1, r2, r3, r4]` | The result of Montgomery reduction before final subtraction |
| `r0, r1, r2, r3, r4` | The 5 limbs of `intermediate` in radix-2^52 | Each `ri` is stored in `intermediate.limbs[i]` |
| `L` | Group order constant as `Scalar52` | `L.limbs = [0x0002631a5cf5d3ed, 0x000dea2f79cd6581, 0x000000000014def9, 0, 0x0001000000000000]` |
| `L[i]` | Limb `i` of the group order | Notably, `L[3] = 0` and `L[4] = 2^44` |
| `MASK_52` | Bit mask `(1 << 52) - 1 = 2^52 - 1` | Used for extracting 52-bit limbs |

The value represented by `intermediate` is:
```
intermediate_value = r0 + r1×2^52 + r2×2^104 + r3×2^156 + r4×2^208
```

### 1.1 The Correctness Requirement

The `sub` function performs `intermediate - L` where `intermediate = r0 + r1×2^52 + r2×2^104 + r3×2^156 + r4×2^208`.

**Connection to `sub`'s precondition:**

The `sub` function has the following signature and precondition:

```rust
pub fn sub(a: &Scalar52, b: &Scalar52) -> Scalar52
    requires
        limbs_bounded_for_sub(a, b),  // <-- This is the key precondition
        limbs_bounded(b),
```

The `limbs_bounded_for_sub` spec is defined as:

```rust
pub open spec fn limbs_bounded_for_sub(a: &Scalar52, b: &Scalar52) -> bool {
    &&& forall|i: int| 0 <= i < 4 ==> a.limbs[i] < (1u64 << 52)  // limbs 0-3 bounded
    &&& a.limbs[4] < (1u64 << 52) + b.limbs[4]                    // limb 4 relaxed
}
```

When `montgomery_reduce` calls `sub(&intermediate, &L)`:
- `a = intermediate` with limbs `[r0, r1, r2, r3, r4]`
- `b = L` (the group order)

Substituting into the spec, the limb 4 constraint becomes:

```
a.limbs[4] < (1u64 << 52) + b.limbs[4]
     ↓              ↓            ↓
    r4      <     2^52     +   L[4]
```

Therefore, **`sub` requires `r4 < 2^52 + L[4]`** (STRICT inequality).

**Why strict?** When `r4 = 2^52 + L[4]` (equality case):

```rust
// In sub's first loop, for limb 4:
borrow = r4 - L[4] - borrow_in
       = (2^52 + L[4]) - L[4] - borrow_in
       = 2^52 - borrow_in

// After masking:
result[4] = borrow & MASK_52 = (2^52 - borrow_in) & (2^52 - 1)

// When borrow_in = 0:
result[4] = 2^52 & MASK_52 = 0    // BIT LOSS! Should be 2^52
```

The masking operation `& MASK_52` causes the high bit to be lost when `r4 - L[4] = 2^52`.

### 1.2 The Hypothetical Failure

If `montgomery_reduce` ever produced `r4 = 2^52 + L[4]`, the subsequent `sub` call would fail:

```rust
// HYPOTHETICAL: If montgomery_reduce produced r4 = 2^52 + L[4] = 4521191813414912:
let intermediate = Scalar52 { limbs: [r0, r1, r2, r3, 4521191813414912] };
let result = sub(&intermediate, &L);
// result.limbs[4] would be WRONG due to bit loss
```

**Critical question**: Can `montgomery_reduce` ever produce `r4 = 2^52 + L[4]`?

**Empirical answer**: **NO** — in 500M+ random tests (see `tests/r4_bound_proptest.rs`), no input to `montgomery_reduce` has ever produced `r4` equal to the critical value `2^52 + L[4]`. The maximum observed `r4` is approximately `2^52`, leaving a gap of `~2^44` to the critical value.

**Theoretical status**: We cannot formally prove this never happens (see Section 5), but extensive testing strongly suggests the strict bound always holds.

### 1.3 Reference

- **Test file**: `curve25519-dalek/tests/r4_bound_proptest.rs`
- **Property tests**: 10M random inputs, 5M high-value inputs
- **Exhaustive search**: 500M iterations (ignored by default due to runtime)

---

## 2. How `montgomery_reduce` Proves the Strict Bound

### 2.1 The Two Approaches

**Approach A: Require canonicity (CURRENT)**

When `canonical_bound` holds (T < R×L ≈ 2^512), HAC Algorithm 14.32 guarantees:
- `intermediate < 2L`
- This implies `r4 < 2^45` (much tighter than needed!)

**Approach B: Prove from code (NOT YET IMPLEMENTED)**

The strict bound `r4 < 2^52 + L[4]` should hold for all inputs satisfying `r4_safe_bound`, but proving this requires showing `lower >= L_low ≈ 2^125`, which the current specs don't capture.

### 2.2 The Canonical Path

Under `canonical_bound`:

```
T < R × L = 2^260 × L ≈ 2^512

intermediate = (T + N×L) / R
            < (R×L + R×L) / R    (since N < R)
            = 2L

Therefore: intermediate < 2L
```

From `intermediate < 2L` and `L < 2^253`:

```
r4 = intermediate / 2^208
   < 2L / 2^208
   < 2 × 2^253 / 2^208
   = 2^46
   < 2^52 + L[4]  ✓
```

Actually, `lemma_r4_bound_from_canonical` proves the tighter bound `r4 < 2^45`.

### 2.3 HAC 14.32 Correspondence

| HAC 14.32 Notation | Dalek Implementation | Spec |
|--------------------|---------------------|------|
| `T < m × R` | T < L × 2^260 | `montgomery_reduce_canonical_bound` |
| `A < 2m` | intermediate < 2L | Derived from above |
| `A - m < m` | result < L | `is_canonical_scalar52` postcondition |

The canonical bound **IS** HAC 14.32's precondition for Montgomery reduction.

---

## 3. Why `mul` Requires a Canonical Input

### 3.1 The Call Chain

```rust
pub fn mul(a: &Scalar52, b: &Scalar52) -> Scalar52 {
    // First reduction: a × b
    let z1 = mul_internal(a, b);          // T = a × b, up to 2^520
    let ab = montgomery_reduce(&z1);       // Needs canonical_bound!
    
    // Second reduction: ab × RR
    let z2 = mul_internal(&ab, &RR);       // T = ab × RR
    let result = montgomery_reduce(&z2);   // RR is canonical, so canonical_bound holds
    
    result
}
```

### 3.2 The Problem with the First Reduction

For `bounded × bounded` multiplication:
- `T = a × b` can be up to `(2^260)² = 2^520`
- `canonical_bound` requires `T < R×L ≈ 2^512`

**If neither input is canonical**, `T` can exceed `R×L`, violating `canonical_bound`.

### 3.3 The Solution

Require at least one canonical input:

```rust
pub fn mul(a: &Scalar52, b: &Scalar52) -> Scalar52
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        is_canonical_scalar52(a) || is_canonical_scalar52(b),  // NEW
```

When one input is canonical (< L ≈ 2^253):
```
T = a × b < 2^260 × 2^253 = 2^513 < R × L  ✓
```

This is proven by `lemma_canonical_product_satisfies_canonical_bound`.

### 3.4 The Second Reduction is Always Safe

```rust
let z2 = mul_internal(&ab, &RR);
```

Since `RR` (the Montgomery constant R² mod L) is canonical (< L), the second reduction always satisfies `canonical_bound`.

---

## 4. The Full Requirement Chain

Because `mul` requires a canonical input, all higher-level operations must also require canonicity:

| Function | New Requirement |
|----------|-----------------|
| `mul(a, b)` | `is_canonical_scalar52(a) \|\| is_canonical_scalar52(b)` |
| `square(self)` | `is_canonical_scalar52(self)` |
| `montgomery_mul(a, b)` | `is_canonical_scalar52(a) \|\| is_canonical_scalar52(b)` |
| `montgomery_square(self)` | `is_canonical_scalar52(self)` |
| `square_multiply(y, n, x)` | `is_canonical_scalar52(y) && is_canonical_scalar52(x)` |
| `montgomery_invert(self)` | `is_canonical_scalar52(self)` |

### 4.1 Callers from the Public API

At the `Scalar` type level (public API), inputs are *assumed* to be canonical based on Scalar's documented **Invariant #2**:

> The integer representing this scalar is less than 2^255 - 19, i.e., it represents a canonical representative of an element of Z/ℓZ.

**Important caveat**: This invariant is **not formally enforced** by Verus specs. The `Mul` trait implementation for `Scalar` contains `assume` statements to assert canonicity:

```rust
// In impl<'b> Mul<&'b Scalar> for &Scalar
assume(scalar52_to_nat(&self_unpacked) < group_order());
assume(scalar52_to_nat(&rhs_unpacked) < group_order());
```

These `assume` statements exist because:
1. The `unpack` function does not have a postcondition guaranteeing canonicity (see below)
2. The current `MulSpecImpl` has `mul_req` returning `true` (no preconditions)

**Note on `SpecImpl` traits**: Verus *does* support preconditions on trait method implementations via `SpecImpl` traits with `*_req` methods. For example, `SubSpecImpl` already uses `sub_req` to require canonicity:

```rust
impl vstd::std_specs::ops::SubSpecImpl<&Scalar> for &Scalar {
    open spec fn sub_req(self, rhs: &Scalar) -> bool {
        is_canonical_scalar(self) && is_canonical_scalar(rhs)
    }
    // ...
}
```

The `MulSpecImpl` could similarly be updated to use `mul_req` to require canonicity instead of using `assume` statements. Currently it's set to `true`:

```rust
impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for &Scalar {
    open spec fn mul_req(self, rhs: &Scalar) -> bool {
        true  // No preconditions - could be changed to require canonicity
    }
    // ...
}
```

This would shift the proof obligation to callers of `Mul`, which may or may not be desirable depending on how the API is used.

**Soundness relies on**: All constructors and operations on `Scalar` maintaining Invariant #2. If a `Scalar` were constructed with a non-canonical value (violating the invariant), the assumes would be unsound.

**Important distinction between `Scalar` and `Scalar52`**:

| Type | Canonicity Requirement | Example |
|------|----------------------|---------|
| `Scalar` (public, bytes) | Invariant #2: value < L | User-facing scalar values |
| `Scalar52` (internal, limbs) | **Not always < L** | The constant `L` itself is a `Scalar52` but `L` is not < L |

The `is_canonical_scalar52` predicate requires `scalar52_to_nat(s) < group_order()`, which the constant `L` does **not** satisfy (since L = L, not L < L). This is intentional — `Scalar52` is an internal representation that can hold values like L for use in arithmetic operations (e.g., `sub(&intermediate, &L)`).

The assumes in the `Mul` trait bridge the gap specifically for values coming from `Scalar` (public type), which are expected to satisfy Invariant #2.

**Why `unpack` cannot guarantee canonicity**: The `unpack` function calls `from_bytes`, which is a *pure byte-to-limb conversion* — it does not reduce the value:

```rust
// from_bytes: pure conversion, no reduction
pub fn from_bytes(bytes: &[u8; 32]) -> Scalar52
    ensures
        bytes32_to_nat(bytes) == scalar52_to_nat(&s),  // Value preserved exactly
        limbs_bounded(&s),

// Contrast with from_bytes_wide: includes reduction
pub fn from_bytes_wide(bytes: &[u8; 64]) -> Scalar52
    ensures
        is_canonical_scalar52(&s),  // Guarantees canonicity via reduction
        scalar52_to_nat(&s) == bytes_seq_to_nat(bytes@) % group_order(),
```

Adding a canonicity postcondition to `unpack` would be **inappropriate** because:
- `unpack` is designed to faithfully convert bytes to limbs without modification
- Canonicity depends on the *input bytes* already representing a value < L
- This is guaranteed by Scalar's Invariant #2, which must be maintained by constructors

The assumes bridge the gap between the type-level invariant (documented but not formally verified) and the function-level spec requirements.

### 4.2 The `unpack` Function and Canonicity (Why Modifying It Is Not Appropriate)

The `unpack` function converts a `Scalar` (byte representation) to `UnpackedScalar` (limb representation):

```rust
pub fn unpack(&self) -> (result: UnpackedScalar)
    ensures
        limbs_bounded(&result),
        limb_prod_bounded_u128(result.limbs, result.limbs, 5),
        scalar52_to_nat(&result) == bytes32_to_nat(&self.bytes),
{ ... }
```

**Current state**: `unpack` does NOT ensure `is_canonical_scalar52(&result)` or `scalar52_to_nat(&result) < group_order()`.

**Why adding canonicity to `unpack` is NOT the right solution**:

1. **`unpack` is a pure conversion**: It calls `from_bytes` which faithfully converts bytes to limbs without reduction. This is by design — `unpack` should not modify or reduce the value.

2. **Canonicity is a property of the input, not the conversion**: Whether the result is canonical depends entirely on whether `self.bytes` already represents a value < L. The `unpack` function cannot "create" canonicity.

3. **Would require proving all constructors maintain Invariant #2**: Even if we wanted to add this postcondition, we'd need to prove `bytes32_to_nat(&self.bytes) < group_order()` for all possible `Scalar` inputs.

**Even if one attempted to add this postcondition**, proving it would require verifying that **all `Scalar` constructors maintain Invariant #2**:

| Constructor | Currently Ensures Canonicity? |
|-------------|------------------------------|
| `from_bytes_mod_order` | ✅ Yes (`is_canonical_scalar(&result)`) |
| `from_bytes_mod_order_wide` | ✅ Yes (`is_canonical_scalar(&result)`) |
| `from_canonical_bytes` | ✅ Yes (validates input, rejects non-canonical) |
| `from_hash` / `from_hash_verus` | ✅ Yes (`is_canonical_scalar(&result)`) |
| Arithmetic ops (`Mul`, `Add`, `Sub`, `Neg`) | ✅ Yes (postconditions ensure canonicity) |
| `invert` | ✅ Yes (`is_canonical_scalar(&result)`) |

**Complication**: The `Scalar` type documentation (in `scalar.rs`, lines 220-230) states that Invariant #2 "sometimes has to be broken":

> This invariant is deliberately broken in the implementation of `EdwardsPoint::{mul_clamped, mul_base_clamped}`, `MontgomeryPoint::{mul_clamped, mul_base_clamped}`, and `BasepointTable::mul_base_clamped`. This is not an issue though... scalar-point multiplication is defined for any choice of `bytes` that satisfies invariant #1. Since clamping guarantees invariant #1 is satisfied, these operations are well defined.

This means a blanket canonicity postcondition on `unpack` would be **unsound** for `Scalar` values used in these clamped multiplication functions.

**Alternative approaches** (not currently implemented):

1. **Ghost field approach**: Add a ghost boolean field to `Scalar` tracking whether it's canonical, and only provide the canonicity postcondition when the ghost field is true

2. **Separate types**: Use different types for canonical vs. potentially non-canonical scalars

3. **Use `MulSpecImpl.mul_req` for canonicity**: Change `mul_req` to require canonical inputs:
   ```rust
   impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for &Scalar {
       open spec fn mul_req(self, rhs: &Scalar) -> bool {
           is_canonical_scalar(self) && is_canonical_scalar(rhs)  // Instead of `true`
       }
   }
   ```
   This would eliminate the `assume` statements in `Mul::mul` by making canonicity a formal precondition. The proof obligation would shift to callers of `*` on `Scalar` values. This is a viable approach since `SubSpecImpl` already uses this pattern with `sub_req`.

**Current approach (chosen)**:

4. **Accept the assumes**: Keep the current design where we assume canonicity based on the documented Invariant #2. This is pragmatic because:
   - The invariant is maintained by all standard constructors (verified above)
   - The clamped multiplication functions that break Invariant #2 don't use `mul` internally — they use scalar-point multiplication which doesn't require canonical scalars
   - Modifying `unpack` would be inappropriate since it's a pure conversion function
   - Using `mul_req` would require verifying all callers of `Scalar` multiplication, which may be extensive

---

## 5. The Alternative: Proving the Strict Bound Without Canonicity

### 5.1 What Would Be Needed

To avoid requiring canonicity, we would need to prove:

```
r4 < 2^52 + L[4]    for ALL inputs satisfying r4_safe_bound
```

This requires showing:

```
lower = r0 + r1×2^52 + r2×2^104 + r3×2^156 >= L_low ≈ 2^125
```

### 5.2 Why This is Difficult

**What the code tells us:**
```
r0 = sum5 & MASK_52    → 0 ≤ r0 < 2^52
r1 = sum6 & MASK_52    → 0 ≤ r1 < 2^52
r2 = sum7 & MASK_52    → 0 ≤ r2 < 2^52
r3 = sum8 & MASK_52    → 0 ≤ r3 < 2^52
```

The masking operation only provides upper bounds, **not lower bounds**.

**What we'd need:**

Either:
- Prove `r3 ≥ 1` (since `r3 × 2^156 > 2^125`)
- Or prove some relationship between r0, r1, r2, r3 that guarantees `lower ≥ L_low`

**The gap:**
```
Code guarantees: lower >= 0
We need:         lower >= L_low ≈ 2^125
Gap:             125 bits of "trust"
```

### 5.3 Mathematical Intuition for Why It Should Hold

The Montgomery reduction computes:
```
intermediate = (T + N×L) / R
```

Where N is **uniquely determined** by T such that `R | (T + N×L)`.

**Key observation**: The structure of L (Ed25519 group order) and the divisibility requirement seem to prevent the "bad" alignment where both:
- `r4 = 2^52 + L[4]` (maximum)
- `lower < L_low` (minimum)

**Structural argument**: For `lower < L_low`, we'd need `r3 = 0` and `r2 < 2^21`. This requires:
```
sum8 ≡ 0 (mod 2^52)    AND    sum7 mod 2^52 < 2^21
```

These constraints on the carry chain appear to be incompatible with valid inputs, but this hasn't been formally proven.

### 5.4 Empirical Evidence

**Extensive testing shows no counterexample:**

| Test | Iterations | Max r4 Observed | Gap to Critical |
|------|------------|-----------------|-----------------|
| Random bounded×bounded | 10,000,000 | ~2^52 | ~2^44 |
| High-value inputs | 5,000,000 | ~2^52 | ~2^44 |
| Exhaustive random | 500,000,000 | ~2^52 | ~2^44 |

**Key finding**: The maximum observed `r4` is approximately `2^52`, but the critical value is `2^52 + 2^44`. The gap of `~2^44` has never been closed in 500M+ tests.

**Reference**: See `tests/r4_bound_proptest.rs` for all test implementations.

### 5.5 Why Proving This in Verus is Hard

1. **No specification captures `lower >= L_low`**: The `part2` postcondition only says `w < 2^52`, not `w >= some_value`

2. **Global property, not local**: The bound comes from the mathematical structure of Montgomery reduction, not from individual code operations

3. **Would require new lemmas**: We'd need to prove that the Montgomery quotient N and the resulting intermediate value have a structure that prevents small `lower` values

4. **Number-theoretic analysis needed**: Showing the constraint alignment is impossible requires analyzing how the Ed25519 group order L interacts with the carry propagation

---

## 6. The Initial Spec and Its Soundness

### 6.1 The Original Two-Tier Approach

Before requiring canonicity, `montgomery_reduce` used conditional postconditions:

```rust
ensures
    montgomery_reduce_r4_safe_bound(limbs) ==> limbs_bounded(&result),
    montgomery_reduce_r4_safe_bound(limbs) ==> montgomery_congruent(&result, limbs),
    montgomery_reduce_canonical_bound(limbs) ==> is_canonical_scalar52(&result),
```

**This spec was sound** because:
- `montgomery_congruent` holds algebraically even when `intermediate >= 2L`
- `limbs_bounded` holds due to masking even when sub's value precondition isn't satisfied

### 6.2 Why We Changed It

The issue was proving `sub`'s precondition:
- `sub` requires `r4 < 2^52 + L[4]` (for `limbs_bounded_for_sub`)
- Under `r4_safe_bound` only, we couldn't prove this bound
- We had to add an `assume` for the strict bound in the non-canonical path

### 6.3 Reference

See `docs/proofs_for_montgomery_reduce/spec_soundness_analysis.md` Section 10 for the complete analysis of why the two-tier approach was algebraically sound (Montgomery congruence holds regardless of `intermediate < 2L`).

---

## 7. Summary

### 7.1 Current Approach: Require Canonicity

**Pros:**
- Clean, provable spec
- Matches HAC 14.32's precondition
- All assumes eliminated for the canonical path

**Cons:**
- Propagates canonicity requirements through call chain
- Slightly more restrictive than strictly necessary

### 7.2 Alternative: Prove Strict Bound for All Inputs

**Pros:**
- Would not require canonicity
- More flexible spec

**Cons:**
- Difficult to prove 
- Empirically true but not formally verified

### 7.3 Risk Assessment

| Aspect | Status |
|--------|--------|
| Code correctness | ✅ Verified under canonicity |
| Strict bound for all inputs | ⚠️ Empirically true, not formally proven |
| Public API callers | ⚠️ Assumed canonical via `assume` statements (based on Invariant #2) |

The current approach relies on **two levels of trust**:
1. **Formally verified**: `montgomery_reduce` and downstream functions are correct when given canonical inputs
2. **Assumed (not verified)**: Public API callers (`Scalar` operations) provide canonical inputs based on Invariant #2

To fully close the verification gap, we would need to either:
- Add `is_canonical_scalar52` as a postcondition to `unpack` (requires proving all `Scalar` constructors maintain canonicity), or
- Prove the strict bound holds for all inputs (see Section 5)

---

## References

- `docs/proofs_for_montgomery_reduce/r4_strict_bound_analysis.md` - Detailed analysis of why strict bound can't be proven from code
- `docs/proofs_for_montgomery_reduce/why_strict_bound_unprovable.md` - Mathematical explanation of the proof gap
- `docs/proofs_for_montgomery_reduce/spec_soundness_analysis.md` - Analysis of the original two-tier spec
- `tests/r4_bound_proptest.rs` - Property tests for the r4 bound
- [HAC Algorithm 14.32](https://cacr.uwaterloo.ca/hac/about/chap14.pdf) - Montgomery reduction algorithm (Handbook of Applied Cryptography, Chapter 14, §14.3.2)
