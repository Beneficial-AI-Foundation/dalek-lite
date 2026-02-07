# Why the Strict Bound Cannot Be Proven from Code

This document explains, step by step, exactly where the difficulty lies in proving `r4 < 2^52 + L[4]` (strict) from the code of `montgomery_reduce`.

---

## 1. The Mathematical Setup

After Montgomery reduction, we have:

```
intermediate = (T + N × L) / 2^260
```

where:
- `T` = input value (from `limbs[0..8]`)
- `N` = quotient computed by Part 1
- `L` = group order
- Division is exact (guaranteed by Part 1's construction)

The intermediate result is represented as:

```
intermediate = r0 + r1×2^52 + r2×2^104 + r3×2^156 + r4×2^208
             = lower + r4×2^208
```

where `lower = r0 + r1×2^52 + r2×2^104 + r3×2^156`.

---

## 2. The Bound We Need

For `sub_for_montgomery` to work correctly, we need:

```
r4 < 2^52 + L[4]    (STRICT inequality)
```

---

## 3. What We Can Prove from Code

### Step 1: Upper bound on intermediate

From the algorithm:
```
intermediate = (T + N × L) / 2^260
```

With bounds:
- `T < 2^520` (from input constraints)
- `N < 2^260` (each n_i < 2^52, so N = Σ n_i × 2^{52i} < 2^260)
- `L < 2^253`

Therefore:
```
T + N × L < 2^520 + 2^260 × 2^253 = 2^520 + 2^513
```

And:
```
intermediate = (T + N × L) / 2^260 < (2^520 + 2^513) / 2^260 = 2^260 + 2^253
```

Actually, the tighter bound (from mathematical analysis) is:
```
intermediate < 2^260 + L
```

This is because the algorithm ensures `intermediate = T×R^{-1} mod L` plus some multiple of L, and the result is in `[0, 2L)`.

### Step 2: Decompose intermediate

```
intermediate = lower + r4 × 2^208
```

Rearranging:
```
r4 × 2^208 = intermediate - lower
r4 = (intermediate - lower) / 2^208
```

### Step 3: Apply the upper bound

```
r4 = (intermediate - lower) / 2^208
   < (2^260 + L - lower) / 2^208
   = (2^260 + L) / 2^208 - lower / 2^208
   = 2^52 + L / 2^208 - lower / 2^208
```

Now, `L / 2^208 = L[4] + L_low / 2^208`, where:
- `L[4] = 2^44` (the high limb of L)
- `L_low = L[0] + L[1]×2^52 + L[2]×2^104` ≈ 2^125

So:
```
r4 < 2^52 + L[4] + L_low / 2^208 - lower / 2^208
   = 2^52 + L[4] + (L_low - lower) / 2^208
```

---

## 4. WHERE THE STRICTNESS IS LOST

### The Critical Question

To prove `r4 < 2^52 + L[4]`, we need:

```
(L_low - lower) / 2^208 <= 0
```

Which requires:

```
lower >= L_low    (approximately 2^125)
```

### What Does the Code Tell Us About `lower`?

From Part 2:
```rust
r0 = sum5 & MASK_52    // r0 = sum5 mod 2^52
r1 = sum6 & MASK_52    // r1 = sum6 mod 2^52
r2 = sum7 & MASK_52    // r2 = sum7 mod 2^52
r3 = sum8 & MASK_52    // r3 = sum8 mod 2^52
```

The code ONLY tells us:
```
0 <= r0 < 2^52
0 <= r1 < 2^52
0 <= r2 < 2^52
0 <= r3 < 2^52
```

Therefore, the ONLY bound on `lower` that we can derive from the code is:
```
lower >= 0
```

This is the **weakest possible lower bound**.

### The Derivation with lower >= 0

With only `lower >= 0`:
```
r4 < 2^52 + L[4] + (L_low - 0) / 2^208
   = 2^52 + L[4] + L_low / 2^208
```

Since `L_low ≈ 2^125` and `2^208 >> 2^125`:
```
L_low / 2^208 < 1
```

So:
```
r4 < 2^52 + L[4] + (something < 1)
```

Since r4 is an integer:
```
r4 <= 2^52 + L[4]    (NON-STRICT)
```

**This is the root cause**: The code doesn't provide any lower bound on `lower` beyond `>= 0`, which only gives us the non-strict inequality.

---

## 5. Visual Summary

```
                    What code tells us          What we'd need for strict bound
                    ------------------          -------------------------------
r0:                 0 <= r0 < 2^52              r0 >= some_value_1  OR
r1:                 0 <= r1 < 2^52              r1 >= some_value_2  OR
r2:                 0 <= r2 < 2^52              r2 >= some_value_3  OR
r3:                 0 <= r3 < 2^52              r3 >= some_value_4

lower:              lower >= 0                  lower >= L_low ≈ 2^125

Result:             r4 <= 2^52 + L[4]           r4 < 2^52 + L[4]
                    (NON-STRICT)                (STRICT)
```

---

## 6. What Would Be Needed for a Formal Proof

To prove the strict bound, we'd need one of:

### Option A: Prove `lower >= L_low`

Show that `r0 + r1×2^52 + r2×2^104 + r3×2^156 >= L_low ≈ 2^125`.

This would require proving something like:
- "r3 is never 0", OR
- "r2 >= 2^21 when r3 = 0", OR  
- Some other structural property

The code doesn't assert or check this. It would need to come from the mathematical structure of Montgomery reduction.

### Option B: Prove `intermediate < 2^260 + L - ε` for some ε > 0

A tighter upper bound on intermediate would also work.

### Option C: Prove the equality case is impossible

Show that `r4 = 2^52 + L[4]` leads to a contradiction.

---

## 7. Why the Code Doesn't Help

The fundamental issue is that Part 2 is just **bit extraction**:

```rust
fn part2(sum: u128) -> (u128, u64) {
    let w = (sum as u64) & MASK_52;   // Extract low 52 bits
    let carry = sum >> 52;             // Shift out low 52 bits
    (carry, w)
}
```

This operation:
- ✓ Gives an upper bound: `w < 2^52`
- ✗ Gives NO lower bound beyond `w >= 0`

The values `r0, r1, r2, r3` could all be 0 if `sum5, sum6, sum7, sum8` were all divisible by `2^52`. The code doesn't prevent this.

---

## 8. The Gap Between Code and Mathematics

| Aspect | What Code Proves | What Math Suggests |
|--------|------------------|-------------------|
| r0, r1, r2, r3 bounds | `>= 0` | Structurally constrained |
| lower bound | `>= 0` | `>= L_low` (empirically) |
| r4 bound | `<= 2^52 + L[4]` | `< 2^52 + L[4]` (empirically) |

The mathematical structure of Montgomery reduction—the way N is chosen to make `T + N×L` divisible by `2^260`—seems to prevent the "bad" alignment where `lower < L_low` and `r4 = 2^52 + L[4]`.

But this is a **global property** of the algorithm, not something visible from local code analysis.

---

## 9. The Real Issue: Incomplete Specifications

**Important clarification**: If the strict bound `r4 < 2^52 + L[4]` is true for all valid inputs, then it IS a valid postcondition and SHOULD be provable. The fact that we can't prove it means one of:

1. **Our specifications are too weak** - The postconditions of `part1`, `part2`, etc. don't capture enough information to derive the strict bound
2. **We're missing an invariant** - There's some property we should track through the computation but aren't
3. **It's actually false** - There exists an input where the bound fails (this would be a bug)

### What "Can't Prove" Really Means

It does NOT mean "mathematically unprovable." It means **we haven't figured out what specifications to write**.

Currently, `part2` has:
```rust
ensures w < pow2(52)  // upper bound only
```

To prove the strict bound, we might need something like:
```rust
ensures 
    w < pow2(52),
    some_relationship(w, sum, previous_values)  // ← MISSING SPEC
```

We haven't identified what `some_relationship` should be.

### The Honest Assessment

| Statement | Status |
|-----------|--------|
| "The strict bound holds for all valid inputs" | **Unknown** - no counterexample found in 1M+ tests |
| "We can prove it with current specs" | No |
| "It's provable with better specs" | Probably, IF it's actually true |
| "We know what specs are needed" | No |

---

## 10. Conclusion

**The strict bound cannot be proven WITH OUR CURRENT SPECIFICATIONS because:**

1. `part2`'s postcondition only gives `r_i >= 0` as a lower bound
2. With `lower >= 0` as the only constraint, the derivation yields `r4 <= 2^52 + L[4]` (non-strict)
3. To get the strict bound, we'd need `lower >= L_low`, which our current specs don't capture

**This is a proof engineering challenge, not a fundamental limitation.**

If the strict bound is true (which empirical testing suggests), then there exist specifications that would let us prove it. We simply haven't found them yet.

**Two possibilities remain open:**

- **A)** The strict bound IS true for all inputs, and we need better specs to prove it
- **B)** The strict bound is NOT true for some input we haven't found (potential bug)

Without either a formal proof or an exhaustive search, we cannot definitively rule out possibility B.
