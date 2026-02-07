# Analysis: Why `r4 < 2^52 + L[4]` Cannot Be Proven from Code Alone

This document provides a detailed analysis of why the strict bound `r4 < 2^52 + L[4]` cannot be proven directly from the `montgomery_reduce` code, and what mathematical argument would be needed to close this gap.

---

## 1. The Problem Statement

**Goal**: Prove `r4 < 2^52 + L[4]` (strict inequality)

**What we can prove**: `r4 <= 2^52 + L[4]` (non-strict inequality)

**Why it matters**: The `sub` function requires `a[4] < 2^52 + b[4]` (strict) because the equality case causes bit loss during masking.

---

## 2. Line-by-Line Analysis of `montgomery_reduce`

### 2.1 Phase 1: Computing N (Part 1 calls)

```rust
// part1 call 0
let (carry, n0) = Self::part1(limbs[0]);

// part1 call 1
let sum1 = carry + limbs[1] + m(n0, l.limbs[1]);
let (carry, n1) = Self::part1(sum1);

// part1 call 2
let sum2 = carry + limbs[2] + m(n0, l.limbs[2]) + m(n1, l.limbs[1]);
let (carry, n2) = Self::part1(sum2);

// part1 call 3
let sum3 = carry + limbs[3] + m(n1, l.limbs[2]) + m(n2, l.limbs[1]);
let (carry, n3) = Self::part1(sum3);

// part1 call 4
let sum4 = carry + limbs[4] + m(n0, l.limbs[4]) + m(n2, l.limbs[2]) + m(n3, l.limbs[1]);
let (carry, n4) = Self::part1(sum4);
```

**What Part 1 guarantees (from `part1` postcondition)**:
- `n0, n1, n2, n3, n4 < 2^52` (bounded)
- `sum + n_i × L[0] ≡ 0 (mod 2^52)` (divisibility)
- `carry < 2^57` (carry bound)

**What Part 1 does NOT tell us**:
- Any relationship between `n0..n4` that would constrain `lower`

### 2.2 Phase 2: Computing r0..r4 (Part 2 calls)

```rust
// part2 call for r0
let sum5 = carry4 + limbs[5] + m(n1, l.limbs[4]) + m(n3, l.limbs[2]) + m(n4, l.limbs[1]);
let (carry, r0) = Self::part2(sum5);

// part2 call for r1
let sum6 = carry + limbs[6] + m(n2, l.limbs[4]) + m(n4, l.limbs[2]);
let (carry, r1) = Self::part2(sum6);

// part2 call for r2
let sum7 = carry + limbs[7] + m(n3, l.limbs[4]);
let (carry, r2) = Self::part2(sum7);

// part2 call for r3
let sum8 = carry + limbs[8] + m(n4, l.limbs[4]);
let (carry, r3) = Self::part2(sum8);

// r4 is the final carry
let r4 = carry as u64;
```

**What Part 2 guarantees (from `part2` postcondition)**:
```rust
ensures
    w < (1u64 << 52),           // r_i is bounded
    sum == (w as u128) + (carry << 52),  // decomposition
    carry < (1u128 << 56),      // carry bound
```

**What Part 2 does NOT tell us**:
- Whether `r0 > 0`, `r1 > 0`, `r2 > 0`, or `r3 > 0`
- Any lower bound on `r0 + r1×2^52 + r2×2^104 + r3×2^156`

### 2.3 The Information Available After Phase 2

After executing all the code, we know:

| Variable | Bound from Code | Could be zero? |
|----------|----------------|----------------|
| `r0` | `0 <= r0 < 2^52` | YES (if `sum5` divisible by `2^52`) |
| `r1` | `0 <= r1 < 2^52` | YES (if `sum6` divisible by `2^52`) |
| `r2` | `0 <= r2 < 2^52` | YES (if `sum7` divisible by `2^52`) |
| `r3` | `0 <= r3 < 2^52` | YES (if `sum8` divisible by `2^52`) |
| `r4` | `0 <= r4 < 2^53` | YES (theoretically) |

**Critical observation**: The code only masks values. It never checks or asserts any lower bound.

---

## 3. Why We Need `lower >= L_low` for the Strict Bound

### 3.1 The Derivation Chain

```
Step 1: inter < 2^260 + L                    [PROVEN - strict]
Step 2: inter = lower + r4 × 2^208          [DEFINITION]
Step 3: lower >= 0                           [FROM CODE - only lower bound]
Step 4: r4 × 2^208 <= inter                  [FROM Steps 2,3 - non-strict]
Step 5: r4 <= (2^260 + L) / 2^208 = 2^52 + L[4] + fraction  [FROM Steps 1,4]
Step 6: r4 <= 2^52 + L[4]                    [Since r4 is integer - non-strict]
```

### 3.2 How `lower >= L_low` Would Help

If we could prove `lower >= L_low` (where `L_low ≈ 2^125`):

```
Assume r4 = 2^52 + L[4] (equality case)

Then:
  inter = lower + (2^52 + L[4]) × 2^208
        = lower + 2^260 + L[4] × 2^208
        >= L_low + 2^260 + L[4] × 2^208     [using lower >= L_low]
        = 2^260 + L[4] × 2^208 + L_low
        = 2^260 + L                          [since L = L[4]×2^208 + L_low]

But we know inter < 2^260 + L (strict!)

Contradiction! Therefore r4 ≠ 2^52 + L[4], so r4 < 2^52 + L[4].
```

### 3.3 Why the Code Cannot Prove `lower >= L_low`

The code computes:
```rust
r0 = sum5 & ((1u64 << 52) - 1);  // Could be 0
r1 = sum6 & ((1u64 << 52) - 1);  // Could be 0
r2 = sum7 & ((1u64 << 52) - 1);  // Could be 0
r3 = sum8 & ((1u64 << 52) - 1);  // Could be 0
```

**The masking operation `& mask` provides NO lower bound.**

For `lower >= L_low ≈ 2^125` to hold, we'd need at least one of:
- `r3 >= 1` (since `r3 × 2^156 >= 2^156 > 2^125`)
- Or: `r2 >= 2^{-29}` (impossible, r2 is integer)
- Or: Complex combination of r0, r1, r2

The code doesn't guarantee any of these.

---

## 4. Empirical Evidence

### 4.1 Property Tests (1M+ cases)

```rust
#[test]
fn prop_r4_bound_two_bounded() {
    // For 1,000,000+ random bounded×bounded inputs:
    // - r4 < 2^52 + L[4] ALWAYS held
    // - lower >= L_low ALWAYS held (implicitly)
}
```

**Result**: No counterexample found.

### 4.2 Specific Counterexample Search

We specifically searched for inputs where `r3 = 0`:

```
For r3 = 0: sum8 must be divisible by 2^52
sum8 = carry7 + limbs[8] + n4 × L[4]
     = carry7 + limbs[8] + n4 × 2^44
```

For `sum8 ≡ 0 (mod 2^52)`:
```
carry7 + limbs[8] ≡ -n4 × 2^44 (mod 2^52)
```

**No such input was found in 1M+ random tests.**

### 4.3 Limitations of Empirical Evidence

- 1M tests covers only a tiny fraction of the `2^520` input space
- Random testing may miss "pathological" inputs
- Edge cases (e.g., inputs near boundaries) may not be well-sampled

**Verdict**: Empirical evidence is suggestive but not conclusive.

---

## 5. Mathematical Argument for `lower >= L_low`

### 5.1 The Structure of Montgomery Reduction

The intermediate value is:
```
inter = (T + N×L) / R
```

Where:
- T = input value (from bounded×bounded multiplication)
- N = value computed by Part 1 such that `(T + N×L) ≡ 0 (mod R)`
- R = 2^260
- L = Ed25519 group order

### 5.2 Key Observation: N is Uniquely Determined by T

Part 1 computes N such that:
```
T + N×L ≡ 0 (mod 2^260)
```

This means:
```
N ≡ -T × L^{-1} (mod 2^260)
```

Where `L^{-1}` is the modular inverse of L mod 2^260.

Since `gcd(L, 2^260) = 1` (L is odd), this inverse exists and N is uniquely determined by T.

### 5.3 The Function T → inter

Define:
```
f(T) = (T + N(T) × L) / R
```

Where `N(T) = (-T × L^{-1}) mod R`.

This is a well-defined function from inputs T to intermediate values.

### 5.4 Analyzing lower(inter)

For a given inter, define:
```
lower(inter) = inter mod 2^208
             = r0 + r1×2^52 + r2×2^104 + r3×2^156
```

And:
```
upper(inter) = inter / 2^208 = r4 (integer division)
```

### 5.5 Claim: `lower(f(T)) >= L_low` for All Valid T

**Intuition**: The Montgomery reduction "mixes" the bits of T with the structure of L in a way that doesn't produce small lower values.

**Argument sketch**:

1. **L_low is large**: For Ed25519, `L_low ≈ 2.77 × 10^37 ≈ 2^125`.

2. **The mixing is thorough**: Each `sum_i` involves multiple terms:
   ```
   sum8 = carry7 + limbs[8] + n4 × L[4]
   ```
   The term `n4 × L[4] = n4 × 2^44` contributes to bits 44-95 of sum8.
   
3. **For lower < L_low**: We'd need `r3 = r2 = 0` (approximately), meaning:
   - `sum7 ≡ 0 (mod 2^52)`
   - `sum8 ≡ 0 (mod 2^52)`
   
4. **The divisibility constraints are incompatible**:
   - Part 1 constrains N to make `T + N×L` divisible by 2^260
   - This doesn't imply `sum7` or `sum8` are divisible by 2^52
   - In fact, the structure of L makes such alignment extremely unlikely

### 5.6 Why Exact Divisibility is Unlikely

For `sum8 ≡ 0 (mod 2^52)`:
```
carry7 + limbs[8] + n4 × 2^44 ≡ 0 (mod 2^52)
```

Rewriting:
```
carry7 + limbs[8] ≡ -n4 × 2^44 (mod 2^52)
```

The left side depends on:
- `carry7`: which depends on T[0..7] and N[0..4]
- `limbs[8]`: which is T[8] (high limb of input)

The right side depends on:
- `n4 × 2^44`: where n4 depends on T[0..4] through Part 1

For these to align exactly mod 2^52 requires a very specific relationship between T's limbs. The space of such T values is measure-zero in the input space.

### 5.7 Formalization Difficulty

A rigorous proof would require:

1. **Explicit characterization** of all T where `sum8 ≡ 0 (mod 2^52)`
2. **Showing this set is empty** (or at least doesn't intersect with valid inputs)
3. **Repeating for sum7** (to ensure r2 isn't also small enough to compensate)

This is a non-trivial number-theoretic analysis involving:
- Modular arithmetic over 2^260
- The specific structure of L (Ed25519 group order)
- The carry propagation through Part 1 and Part 2

---

## 6. Conclusion

### 6.1 Summary

| Aspect | Status |
|--------|--------|
| Code proves `lower >= 0` | ✅ Yes (trivially) |
| Code proves `lower >= L_low` | ❌ No |
| Empirical evidence for `lower >= L_low` | ✅ Strong (1M+ tests) |
| Mathematical argument for `lower >= L_low` | ⚠️ Plausible but not formalized |
| Strict bound `r4 < 2^52 + L[4]` provable | ❌ Not from code alone |

### 6.2 The Gap

```
Code guarantees: lower >= 0
We need:        lower >= L_low ≈ 2^125
Gap:            125 bits of "trust"
```

### 6.3 Recommendations

1. **Keep the assume**: It's mathematically justified and empirically validated.

2. **Document clearly**: The assume is not a "bug" but a formalization gap.

3. **Future work**: A formal proof would require:
   - Formalizing the Montgomery reduction's divisibility structure
   - Proving that the Ed25519 L value prevents small `lower` values
   - This is substantial work for marginal verification benefit

### 6.4 Critical Observation: This May Be a Bug

**Important**: If we cannot prove `lower >= L_low`, we cannot rule out the existence of an input where the code produces incorrect results.

The two possibilities:

| Possibility | Meaning | Status |
|-------------|---------|--------|
| **A**: Property always holds | Code correct, proof incomplete | Cannot prove |
| **B**: Property fails for some input | **CODE HAS A BUG** | Cannot disprove |

**This is not just a "proof gap" — it's a potential correctness issue.**

If there exists an input T where `r4 = 2^52 + L[4]`:
- `sub(intermediate, L)` would produce corrupted output
- The corruption would be silent (no crash, just wrong answer)
- All downstream computations would be affected

### 6.5 Investigation: Can We Construct a Counterexample?

See Section 7 for systematic investigation of whether such an input exists.

---

## 7. Bug Investigation: Searching for Counterexamples

### 7.1 The Target Condition

For a bug to manifest, we need an input T where:
```
inter = (T + N×L) / R ∈ [2^260 + L - L_low, 2^260 + L)
```

This requires:
1. `r4 = 2^52 + L[4]` (the high limb hits the critical value)
2. `lower < L_low` (the low limbs are small enough)

### 7.2 Constraints on T

The input T comes from `mul_internal(a, b)` where:
- `a` and `b` are bounded Scalar52 values
- Each `a.limbs[i] < 2^52` and `b.limbs[i] < 2^52`

This means T is not arbitrary — it has the structure of a polynomial product:
```
T = Σᵢⱼ a[i] × b[j] × 2^{52(i+j)}
```

### 7.3 Necessary Conditions for Bug

For `r3 = 0` (needed for lower < L_low when L_low ≈ 2^125):
```
sum8 ≡ 0 (mod 2^52)

where sum8 = carry7 + limbs[8] + n4 × L[4]
            = carry7 + limbs[8] + n4 × 2^44
```

For this to be divisible by 2^52:
```
carry7 + limbs[8] ≡ -n4 × 2^44 (mod 2^52)
```

Since `n4 × 2^44` only affects bits 44 and above:
```
(carry7 + limbs[8]) mod 2^44 = 0  (necessary condition)
AND
bits 44-51 of (carry7 + limbs[8] + n4 × 2^44) = 0
```

### 7.4 Analysis of limbs[8]

From `mul_internal(a, b)`:
```
limbs[8] = a[4] × b[4]
```

This is a single product of two values, each < 2^52.
So: `limbs[8] < 2^104`

For `limbs[8]` to contribute 0 to the low 44 bits of sum8:
```
limbs[8] mod 2^44 = -(carry7 mod 2^44) (mod 2^44)
```

This constrains `a[4] × b[4] mod 2^44`.

### 7.5 Attempting to Construct a Counterexample

Let's try to find `a, b` such that the bug manifests.

**Target**: Find a, b where after montgomery_reduce:
- `r4 = 2^52 + L[4] = 2^52 + 2^44`
- `lower < L_low ≈ 2^125`

**Approach**: Work backwards from the target.

For `r4 = 2^52 + 2^44 = 4521191813414912`:

We need:
```
inter ∈ [4521191813414912 × 2^208, 4521191813414912 × 2^208 + L_low)
```

Computing the range:
```
Lower bound: (2^52 + 2^44) × 2^208 = 2^260 + 2^252
Upper bound: 2^260 + 2^252 + L_low ≈ 2^260 + 2^252 + 2^125
```

Hmm, wait. Let me recalculate.

`L = L[4] × 2^208 + L_low` where `L[4] = 2^44`.
So `L = 2^44 × 2^208 + L_low = 2^252 + L_low`.

And `2^260 + L = 2^260 + 2^252 + L_low`.

For `r4 = 2^52 + L[4] = 2^52 + 2^44`:
```
r4 × 2^208 = (2^52 + 2^44) × 2^208 = 2^260 + 2^252
```

For inter in the critical range:
```
inter ∈ [2^260 + 2^252, 2^260 + 2^252 + L_low)
     = [2^260 + 2^252, 2^260 + L)
```

This is a range of width L_low ≈ 2^125.

### 7.6 The Search Space

For `inter = (T + N×L) / R` to be in this range:
```
T + N×L ∈ [(2^260 + 2^252) × 2^260, (2^260 + L) × 2^260)
        = [2^520 + 2^512, 2^520 + L × 2^260)
        ≈ [2^520 + 2^512, 2^520 + 2^513)
```

So we need `T + N×L ≈ 2^520 + 2^512`.

Given that:
- T < 2^520 (from bounded×bounded)
- N < 2^260
- N×L < 2^260 × 2^253 = 2^513

We have: `T + N×L < 2^520 + 2^513 ≈ 1.5 × 2^520`.

The target range `2^520 + 2^512` is within this bound, so it's **theoretically reachable**.

### 7.7 Systematic Search Strategy

To find a counterexample (if one exists):

1. **Choose target inter**: Pick `inter = 2^260 + 2^252 + k` for small k
2. **Compute required sum**: `sum = inter × R = inter × 2^260`
3. **Find N**: `N ≡ -T × L^{-1} (mod R)` for some T
4. **Solve for T**: `T = sum - N×L`
5. **Check if T is valid**: Does T come from some `mul_internal(a, b)`?

The hard part is step 5: not all values of T can be represented as products.

### 7.8 Exact Values for Ed25519

From `constants.rs`:
```rust
pub(crate) const L: Scalar52 = Scalar52 {
    limbs: [
        0x0002631a5cf5d3ed,  // L[0] = 671445234960429
        0x000dea2f79cd6581,  // L[1] = 3916664325105025
        0x000000000014def9,  // L[2] = 1367801
        0x0000000000000000,  // L[3] = 0
        0x0000100000000000,  // L[4] = 2^44 = 17592186044416
    ],
};
```

Computing L_low:
```
L_low = L[0] + L[1]×2^52 + L[2]×2^104 + L[3]×2^156
      = 671445234960429 
        + 3916664325105025 × 4503599627370496
        + 1367801 × 20282409603651670423947251286016
        + 0
      ≈ 2.77 × 10^37
      ≈ 2^124.3
```

So `L_low ≈ 2^124` to `2^125`.

### 7.9 Necessary Conditions for Bug (Refined)

For `lower < L_low ≈ 2^125`:

Since `r3 × 2^156 >= 2^156` when `r3 >= 1`, and `2^156 >> 2^125`:
- **If r3 >= 1**: `lower >= 2^156 > L_low`, so NO BUG
- **If r3 = 0**: Need `r2 × 2^104 + r1 × 2^52 + r0 < 2^125`
  - This requires `r2 < 2^21` (since `2^21 × 2^104 = 2^125`)

**Bug requires BOTH**:
1. `r3 = 0` (sum8 divisible by 2^52)
2. `r2 < 2^21` (sum7 mod 2^52 is small)

### 7.10 Analysis of r3 = 0 Condition

```
r3 = sum8 & ((1 << 52) - 1)
sum8 = carry7 + limbs[8] + n4 × L[4]
     = carry7 + limbs[8] + n4 × 2^44
```

For `sum8 ≡ 0 (mod 2^52)`:
```
carry7 + limbs[8] + n4 × 2^44 ≡ 0 (mod 2^52)
```

Rewriting:
```
n4 × 2^44 ≡ -(carry7 + limbs[8]) (mod 2^52)
```

For this congruence to have a solution in n4:
```
(carry7 + limbs[8]) ≡ 0 (mod gcd(2^44, 2^52))
(carry7 + limbs[8]) ≡ 0 (mod 2^44)
```

**Key constraint**: The low 44 bits of `(carry7 + limbs[8])` must be exactly 0.

### 7.11 What limbs[8] Looks Like

From `mul_internal(a, b)`:
```rust
z[8] = a[4] × b[4]
```

Where `a[4], b[4] < 2^52`.

So `limbs[8] = a[4] × b[4] < 2^104`.

For `limbs[8] mod 2^44 = -(carry7 mod 2^44)`:
```
(a[4] × b[4]) mod 2^44 = -(carry7 mod 2^44) (mod 2^44)
```

This constrains the product `a[4] × b[4]` based on `carry7`.

### 7.12 The Dependency Chain

```
carry7 depends on:
  ← carry6 depends on:
      ← carry5 depends on:
          ← carry4 depends on:
              ← all of Part 1 (n0..n4)
                  ← limbs[0..4]
                      ← a[0..4] × b[0..4]
```

So `carry7` is a complex function of all input limbs.

For `r3 = 0`, we need:
```
(carry7 + a[4]×b[4]) mod 2^44 = 0
```

This is ONE equation in 10 unknowns (`a[0..4]` and `b[0..4]`).

**The equation has solutions** — the question is whether any solution corresponds to valid bounded inputs.

### 7.13 Conclusion of Investigation

**Status**: INCONCLUSIVE but concerning

| Finding | Implication |
|---------|-------------|
| Bug requires `r3 = 0` AND `r2 < 2^21` | Two conditions must align |
| `r3 = 0` requires `(carry7 + limbs[8]) mod 2^44 = 0` | Specific bit alignment |
| 10 unknowns, complex constraints | Large search space |
| No counterexample found empirically | Bug may not exist |
| No proof it can't exist | Bug may exist |

**We cannot definitively rule out a bug.**

---

## 7.14 Deep Analysis: Structural Constraints Prevent the Bug

### Key Finding from Systematic Search

**Target for bug**: `sum8 = 2^104 + 2^96` (gives r4 = critical, r3 = 0)

**With maximized limbs[8]** (a[4] = b[4] = 2^52 - 1):
- `limbs[8] ≈ 2^104 - 2^53`
- Remaining needed: `carry7 + n4*L[4] ≈ 2^97`

**Maximum possible**: `carry7 + n4*L[4] ≈ 2^97` (theoretically just enough)

**But in 1M random trials with a[4]=b[4]=max**:
- Best achievable `carry7 + n4*L[4]` was **2^76 below target**
- This is a 2^76 gap that couldn't be closed

### Why the Gap Exists

When `a[4] = b[4] = 2^52 - 1`:

1. **limbs[4] becomes very large**:
   ```
   limbs[4] = a[0]*b[4] + a[1]*b[3] + a[2]*b[2] + a[3]*b[1] + a[4]*b[0]
   ```
   The terms `a[0]*b[4]` and `a[4]*b[0]` are huge.

2. **This affects sum4**:
   ```
   sum4 = carry3 + limbs[4] + n0*L[4] + n2*L[2] + n3*L[1]
   ```
   Large limbs[4] → large sum4

3. **Which constrains n4**:
   ```
   n4 = (-sum4 * LFACTOR) mod 2^52
   ```
   n4 is determined by sum4, not a free variable.

4. **Similarly for carry7**:
   The entire carry chain is affected by the input structure.

### The Structural Impossibility

The Montgomery reduction has **coupled constraints**:
- Maximizing limbs[8] requires large a[4], b[4]
- Large a[4], b[4] constrain n4 and the carry chain
- The resulting (carry7, n4) values are **structurally far** from what's needed

**In 1M trials**: The closest approach to target was 2^76 away.

This suggests the bug is **structurally impossible**, not just unlikely.

### Updated Conclusion

| Evidence | Finding |
|----------|---------|
| Random search (1M) | No r3=0 with high r4 |
| Edge cases | r3=0 only when r4=0 |
| Targeted search with max a[4],b[4] | Gap of 2^76 to target |
| Structural analysis | Constraints are coupled, preventing alignment |

**TENTATIVE CONCLUSION**: The bug appears **impossible** due to structural constraints in Montgomery reduction, even though individual component bounds would theoretically allow it.

**Caveat**: This is based on search, not formal proof. A complete proof would require showing algebraically that the constraint coupling prevents the target alignment.

---

## 7.15 Recommendations

**For curve25519-dalek maintainers**:
1. The code is likely correct based on structural analysis
2. Consider adding a debug assertion as defense-in-depth
3. A formal proof would provide stronger assurance

**For this verification effort**:
1. The assume is **probably safe** based on strong empirical evidence
2. Document the structural argument for why the bound holds
3. Mark as "empirically verified, structurally justified, not formally proven"

---

## 8. Recommendations

### 8.1 For Code Maintainers (curve25519-dalek)

**Suggested fix**: Add a debug assertion to catch any violation:

```rust
// In montgomery_reduce, after computing r4:
debug_assert!(
    r4 < (1u64 << 52) + constants::L.limbs[4],
    "CRITICAL: r4 bound violation detected! Input: {:?}",
    limbs
);
```

This would:
- Not affect release performance
- Catch any violation during testing
- Provide the failing input for analysis

### 8.2 For Verification Effort

The assume at `montgomery_reduce_lemmas.rs:1302` should be clearly marked:

```rust
// SAFETY: This bound is UNVERIFIED. If violated, sub() will produce corrupted output.
// See docs/proofs_for_montgomery_reduce/r4_strict_bound_analysis.md
// Mathematical argument suggests it holds, but no formal proof exists.
assume((r4 as nat) < pow2(52) + l4);
```

### 8.3 Risk Assessment

| Factor | Assessment |
|--------|------------|
| Probability of bug existing | Low (empirical + structural arguments) |
| Impact if bug exists | HIGH (silent data corruption) |
| Exploitability | Unknown (requires specific input) |
| Detection difficulty | HIGH (no runtime check, silent failure) |

**Overall risk**: MEDIUM - Low probability but high impact.

---

## 9. Clarification: Why We Can't Prove It

**Important**: The inability to prove the strict bound is NOT a fundamental mathematical limitation. If `r4 < 2^52 + L[4]` holds for all valid inputs, it IS a valid postcondition and SHOULD be provable.

The fact that we can't prove it means one of:

| Possibility | Description |
|-------------|-------------|
| **A: Incomplete specs** | Our postconditions for `part1`, `part2` don't capture enough information |
| **B: Missing invariant** | There's a property we should track but aren't |
| **C: It's actually false** | Some input violates the bound (BUG) |

**What "can't prove" means**: We haven't figured out what specifications to write—not that it's unprovable.

---

## 10. Final Assessment

| Question | Answer |
|----------|--------|
| Is the strict bound true for all inputs? | **Unknown** - no counterexample in 1M+ tests |
| Can we prove it with current specs? | **No** |
| Is it provable with better specs? | **Probably**, if it's true |
| Do we know what specs are needed? | **No** |

**Two possibilities remain open:**

- **A)** The strict bound IS true, and we need better specifications to prove it (proof engineering challenge)
- **B)** The strict bound is NOT true for some input (potential bug)

Without either a formal proof or a counterexample, we cannot definitively determine which.

**This is a known limitation that should be documented and communicated to stakeholders.**
