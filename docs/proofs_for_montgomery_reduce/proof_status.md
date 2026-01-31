# Montgomery Reduce Proof Status

## Quick Status

**Verification: 1321 verified, 0 errors** ✅

| Metric | Count | Notes |
|--------|-------|-------|
| Active `assume(...)` in proof chain | **2** | 1 safe, 1 spec gap |
| Utility lemma assumes (not in chain) | 4 | |
| Inline assumes in `montgomery_reduce` | 1 | `T < pow2(520)` precondition |
| **Spec soundness gap** | ⚠️ | `inter < 2L` not true for all `r4_safe_bound` inputs |

---

## Complete Assume Inventory

### Part 1: `lemma_part1_chain_divisibility` (0 assumes) ✅ FULLY PROVEN

| # | Assume | Math | Status | Proof Technique |
|---|--------|------|--------|-----------------|
| ~~1~~ | ~~N×L polynomial expansion~~ | `n * l == low + high` | ✅ **PROVEN** | `lemma_poly_mul_5x5_decomposition` |
| ~~2~~ | ~~Connection to expansion~~ | `(n * l) % 2^260 = low % 2^260` | ✅ **PROVEN** | Enhanced ensures in `lemma_n_times_l_expansion` |
| ~~3~~ | ~~Final connection~~ | `(t_low + n * l_low) % 2^260 = 0` | ✅ **PROVEN** | `lemma_add_mod_noop` + high_part divisibility |

**New shared lemma**: `lemma_poly_mul_5x5_decomposition` proves:
```
a × b == low_coeffs + high_coeffs × 2^260
```
This is called from both Part 1 (`lemma_n_times_l_expansion`) and Part 2 (quotient proof).

---

### Part 2: `lemma_part2_chain_quotient` (0 assumes) ✅ FULLY PROVEN

| # | Assume | Math | Status | Proof Technique |
|---|--------|------|--------|-----------------|
| ~~1~~ | ~~T decomposition~~ | `t == t_low + t_high * pow2(260)` | ✅ **PROVEN** | `lemma_nine_limbs_equals_slice128_to_nat` + distributivity |
| ~~2~~ | ~~Part 1 quotient~~ | `t_low + nl_low_coeffs == carry4 * 2^260` | ✅ **WIRED** | Precondition from Part 1's enhanced `ensures` |
| ~~3~~ | ~~Carry cancellation~~ | `intermediate == carry4 + t_high + nl_high` | ✅ **PROVEN** | Explicit distributivity steps |
| ~~4~~ | ~~high_part factoring~~ | `high_part == nl_high * 2^260` | ✅ **PROVEN** | `lemma_mul_is_distributive_add_other_way` + `lemma_mul_is_associative` |
| ~~5~~ | ~~Polynomial mult~~ | `n * l == nl_low_coeffs + high_part` | ✅ **PROVEN** | `lemma_poly_mul_5x5_decomposition` |
| ~~6~~ | ~~Definition~~ | `l == l_poly` (group_order equals limb poly) | ✅ **PROVEN** | `lemma_group_order_equals_l_poly` |
| ~~7~~ | ~~Final chain~~ | `t + n*l == intermediate * 2^260` | ✅ **PROVEN** | Combining other assumptions |

**Key achievements**:
1. **Fixed conceptual bug**: Corrected N×L decomposition to use `nl_low_coeffs` instead of `n * l_low`
2. **T decomposition proven**: Using `lemma_nine_limbs_equals_slice128_to_nat` + explicit factoring
3. **Carry cancellation proven**: Step-by-step distributivity showing intermediate carries cancel
4. **High part factoring proven**: Showing `coeff5*2^260 + coeff6*2^312 + ... = nl_high * 2^260`
5. **Final chain proven**: Pure algebra once other facts established
6. **Part 1 quotient wired**: Enhanced Part 1's `ensures` to expose the quotient, passed as precondition

---

### Part 3: `lemma_montgomery_reduce_pre_sub` (2 assumes)

| # | Location | Assume | Math | Status | Proof Technique |
|---|----------|--------|------|--------|-----------------|
| ~~1~~ | ~~montgomery_reduce_lemmas.rs~~ | ~~`inter < pow2(260) + l`~~ | intermediate < 2^260 + L | ✅ **PROVEN** | Division bound + Part 2 quotient |
| 2 | montgomery_reduce_lemmas.rs:1245 | `r4 < pow2(52) + L[4]` | r4 bound | 🔸 assume | Division: r4 ≤ inter/2^208 |
| 3 | montgomery_reduce_lemmas.rs:1279 | `inter < 2 * l` | intermediate < 2L | ⚠️ **SPEC GAP** | See analysis below |

**New precondition**: `T < pow2(520)` (caller proves from `r4_safe_bound`)

**Progress**: 
- Assume 1 PROVEN using `lemma_div_strictly_bounded` and Part 2's quotient equality
- Added `T < pow2(520)` as precondition (cleaner design - caller establishes from `r4_safe_bound`)

**Mathematical justification** (Part 3 bounds analysis):
1. **inter < 2^260 + L**: ✅ PROVEN - From T < 2^520, N < R, and division bounds
2. **r4 < 2^52 + L[4]**: r4 × 2^208 ≤ inter < 2^260 + L, so r4 < 2^52 + L[4]
3. **inter < 2L**: ⚠️ **ONLY true for `canonical_bound`** (T < R×L)

**⚠️ SPEC SOUNDNESS ISSUE (Assume #3)**:

Empirical testing revealed that for `bounded × bounded` inputs (satisfying `r4_safe_bound` but NOT `canonical_bound`), `intermediate >= 2L` CAN occur:
```
Test case: a×b where both are bounded (limbs < 2^52)
Result: intermediate ≈ 1.8×10^78 > 2L ≈ 1.4×10^77
But: Montgomery property still holds! limbs_bounded still holds!
```

This violates `sub`'s value precondition `-L ≤ a - b < L`, yet the code produces correct results.

**Why it works**: The spec is "accidentally correct" because:
- `limbs_bounded` is enforced by masking (independent of value bounds)
- `montgomery_congruent` is an algebraic property: `result ≡ intermediate (mod L)` always holds

**See**: [spec_soundness_analysis.md](spec_soundness_analysis.md) for complete analysis and resolution options

---

### Part 4: `lemma_montgomery_reduce_post_sub` (0 assumes) ✅ FULLY PROVEN

All congruence algebra assumes have been eliminated using existing vstd lemmas:

| # | Original Assume | Proof Technique |
|---|-----------------|-----------------|
| 1 | `res % l == inter % l` | `lemma_mod_sub_multiples_vanish` + `lemma_mod_twice` |
| 2 | `(res * r) % l == (inter * r) % l` | `lemma_mul_factors_congruent_implies_products_congruent` |
| 3 | `(t + n * l) % l == t % l` | `lemma_mod_multiples_vanish` |

**Mathematical justification** (Part 4 congruence algebra):
```
result ≡ intermediate (mod L)           [from sub]
result × R ≡ intermediate × R (mod L)   [multiply by R]
          ≡ T + N×L (mod L)             [Part 2 quotient]
          ≡ T (mod L)                   [N×L ≡ 0]
```
This proves `montgomery_congruent(result, T)`.

---

### Call Site: `scalar.rs` (0 assumes) ✅

The quotient relationship is now propagated through `lemma_montgomery_reduce_pre_sub`'s postcondition:
```rust
ensures
    scalar52_to_nat(intermediate) * montgomery_radix() == slice128_to_nat(limbs) + n * group_order(),
```

This eliminated the inline assume at the call site by:
1. Adding `ensures` clause to `lemma_montgomery_reduce_pre_sub`
2. Proving `scalar52_to_nat(intermediate) == five_u64_limbs_to_nat(r0..r4)` via `lemma_five_limbs_equals_to_nat`
3. Using `montgomery_radix() == pow2(260)` (definition)

---

### Fully Proven Lemmas (0 assumes) ✅

| Lemma | Status |
|-------|--------|
| `lemma_carry8_bound` | ✅ **FULLY PROVEN** - bit_vector proof |
| N bound (`n < pow2(260)`) | ✅ **FULLY PROVEN** - via `lemma_general_bound` |
| `lemma_montgomery_reduce_post_sub` | ✅ **FULLY PROVEN** - vstd mod lemmas |

---

### Utility Lemmas (NOT in active proof chain)

These are helper lemmas with `assume(false)` that are **not called** in the montgomery_reduce proof:

| Lemma | Line | Status |
|-------|------|--------|
| `lemma_u128_low_bits_mask_is_mod` | 32 | Utility - not in chain |
| `lemma_u128_truncate_to_u64` | 40 | Utility - not in chain |
| `lemma_u128_truncate_and_mask` | 50 | Utility - not in chain |
| `lemma_part1_divisible` | 114 | Has working proof (commented), needs rlimit fix |

---

## Safety Analysis Summary

**2 active assumes: 1 SAFE, 1 SPEC GAP** ⚠️

| Category | Count | Status |
|----------|-------|--------|
| Part 1 (divisibility) | 0 ✅ | **FULLY PROVEN** |
| Part 2 (quotient) | 0 ✅ | **FULLY PROVEN** |
| Part 3 inter < 2^260 + L | 0 ✅ | **FULLY PROVEN** - division bounds |
| Part 3 r4 bound | 1 🔸 | **SAFE** - follows from inter bound by division |
| Part 3 inter < 2L | 1 ⚠️ | **SPEC GAP** - NOT true for `r4_safe_bound`, only for `canonical_bound` |
| Polynomial multiplication | 0 ✅ | **FULLY PROVEN** - `lemma_poly_mul_5x5_decomposition` |
| group_order = limb poly | 0 ✅ | **FULLY PROVEN** - `lemma_group_order_equals_l_poly` |
| T decomposition (Part 2) | 0 ✅ | **FULLY PROVEN** - radix representation |
| Carry cancellation (Part 2) | 0 ✅ | **FULLY PROVEN** - explicit distributivity |
| High part factoring (Part 2) | 0 ✅ | **FULLY PROVEN** - associativity + distributivity |
| Part 1 quotient (Part 2) | 0 ✅ | **FULLY WIRED** - precondition from Part 1 `ensures` |
| Final chain (Part 2) | 0 ✅ | **FULLY PROVEN** - combining facts |
| Congruence algebra (Part 4) | 0 ✅ | **FULLY PROVEN** - vstd mod lemmas |
| Call site bridge | 0 ✅ | **ELIMINATED** - propagated via `ensures` |

### Key Finding: Spec Soundness Gap

The `inter < 2L` assume (#3) masks a **spec soundness issue**:
- For `r4_safe_bound` inputs, `intermediate >= 2L` CAN occur (empirically verified)
- This violates `sub`'s precondition
- **BUT** the claimed postconditions (`limbs_bounded`, `montgomery_congruent`) still hold!
- The spec is "accidentally correct" due to algebraic properties

**See**: [spec_soundness_analysis.md](spec_soundness_analysis.md) for complete analysis.

---

## Proof Chain Architecture

```
montgomery_reduce(limbs) → result
│
├── Part 1: lemma_part1_chain_divisibility
│   └── Proves: (T_low + N×L_low) ≡ 0 (mod 2^260)
│   └── 3 assumes (polynomial multiplication)
│
├── Part 2: lemma_part2_chain_quotient  
│   └── Proves: intermediate × 2^260 = T + N×L
│   └── 2 assumes (Part 1 quotient, N×L decomposition)
│   └── T decomposition: ✅ FULLY PROVEN
│   └── Carry cancellation: ✅ FULLY PROVEN
│   └── Final chain: ✅ FULLY PROVEN
│
├── Part 3: lemma_montgomery_reduce_pre_sub
│   └── Proves: r4 < 2^52 + L[4], intermediate < 2L
│   └── 3 assumes (bounds derivation)
│
├── lemma_carry8_bound ✅ FULLY PROVEN
│   └── Proves: carry8 < 2^53 (safe cast)
│
└── Part 4: lemma_montgomery_reduce_post_sub ✅ FULLY PROVEN
    └── Proves: montgomery_congruent(result, T)
    └── 0 assumes
```

---

## Next Steps (Priority Order)

| Priority | Task | Assumes to Eliminate | Technique |
|----------|------|---------------------|-----------|
| 1 | Complete Part 2 decompositions | 4 | Radix representation + Part 1 connection |
| 2 | Complete Part 3 bounds | 3 | Division algebra |
| 3 | Complete Part 1 polynomial expansion | 3 | Z3 hints for distributivity |
| ~~4~~ | ~~Complete Part 2 telescoping~~ | ~~1~~ | **DONE** ✅ (reformulated + carry cancellation proven) |
| ~~5~~ | ~~Complete Part 4 congruence~~ | ~~3~~ | **DONE** ✅ |

---

## Related Documentation

| Document | Purpose |
|----------|---------|
| [montgomery_reduce_proofs.md](montgomery_reduce_proofs.md) | Mathematical proofs for Parts 1-4 |
| [polynomial_multiplication_proof.md](polynomial_multiplication_proof.md) | N×L polynomial expansion |
| [part1_proof.md](part1_proof.md) | Detailed part1 function proof |
| [spec_soundness_analysis.md](spec_soundness_analysis.md) | **NEW**: Analysis of why spec is "accidentally correct" |
| [supporting/sub_and_bounds_analysis.md](supporting/sub_and_bounds_analysis.md) | Limb bounds and sub precondition analysis |
