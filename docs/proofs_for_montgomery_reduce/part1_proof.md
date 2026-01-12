# Mathematical Proof for `part1` Function

## Overview

The `part1` function is a helper for Montgomery reduction. Given a sum, it computes `p` such that `(sum + p * L[0])` is divisible by 2^52, returning the carry.

## Function Body

```rust
fn part1(sum: u128) -> (u128, u64) {
    let mask52: u64 = 0xFFFFFFFFFFFFF;           // 2^52 - 1
    let sum_low52: u64 = (sum as u64) & mask52;  // s = sum mod 2^52
    let product: u128 = (sum_low52 as u128) * (LFACTOR as u128);
    let p: u64 = (product as u64) & mask52;      // p = (s * LFACTOR) mod 2^52
    let total: u128 = sum + (p as u128) * (L[0] as u128);
    let carry: u128 = total >> 52;
    (carry, p)
}
```

## Specification

```rust
requires sum < 2^108
ensures  p < 2^52
ensures  sum + p * L[0] == carry << 52
```

## Constants

| Constant | Value | Notes |
|----------|-------|-------|
| `L[0]` | `0x0002631a5cf5d3ed` | ≈ 2^50 |
| `LFACTOR` | `0x51da312547e1b` | 52 bits |
| `2^52` | `0x10000000000000` | Limb modulus |

---

# Part 1: Mathematical Proof

## Key Property: LFACTOR

LFACTOR is the **negated modular inverse** of L[0] modulo 2^52:

```
LFACTOR * L[0] ≡ -1 (mod 2^52)
```

Equivalently: `(1 + LFACTOR * L[0]) % 2^52 = 0`

This can be verified by direct computation.

## Main Theorem: Divisibility

**Goal**: Prove `(s + p * L[0]) % 2^52 = 0` where:
- `s = sum % 2^52` (low 52 bits of sum)
- `p = (s * LFACTOR) % 2^52`

**Proof**:

```
1. (1 + LFACTOR * L[0]) % 2^52 = 0           [LFACTOR property]

2. s * (1 + LFACTOR * L[0]) % 2^52 = 0       [scale by s: if x ≡ 0, then k*x ≡ 0]

3. s * (1 + LFACTOR * L[0]) = s + s*LFACTOR*L[0]   [distributivity]

4. p * L[0] ≡ s * LFACTOR * L[0] (mod 2^52)  [since p = s*LFACTOR mod 2^52]

5. (s + p * L[0]) % 2^52 = 0                 [combine steps 2-4]  ∎
```

## Extension to Full Sum

**Goal**: If `(s + p*L[0]) % 2^52 = 0`, then `(sum + p*L[0]) % 2^52 = 0`

**Proof**: Since `s = sum % 2^52`, we have `sum ≡ s (mod 2^52)`. Adding `p*L[0]` to both sides preserves the congruence.

## Final Step: Shift Round-Trip

**Goal**: Prove `sum + p*L[0] == carry << 52` where `carry = (sum + p*L[0]) >> 52`

**Proof**: If `x % 2^52 = 0` and `x` fits in u128, then `(x >> 52) << 52 = x`.

---

# Part 2: Verus Implementation

The proof uses **two lemmas** that mirror the mathematical structure.

## Lemma 1: `lemma_part1_divisible`

**Purpose**: Core divisibility proof (steps 1-5 of the math proof).

```rust
proof fn lemma_part1_divisible(s: u64, p: nat)
    requires
        s < pow2(52),
        p == (s * LFACTOR) % pow2(52),
    ensures
        (s + p * L[0]) % pow2(52) == 0
```

**Proof structure**:
1. Assert LFACTOR property: `(1 + LFACTOR * L[0]) % 2^52 = 0` via `by (compute)`
2. Scale by `s`: use `lemma_mul_mod_noop_right`
3. Expand via distributivity: use `lemma_mul_is_distributive_add`
4. Connect `p*L[0]` to `s*LFACTOR*L[0]`: use `lemma_mul_mod_noop_left`
5. Conclude with `lemma_add_mod_noop`

## Lemma 2: `lemma_part1_correctness`

**Purpose**: Main lemma proving the postcondition (includes extension and shift round-trip).

```rust
proof fn lemma_part1_correctness(sum: u128)
    requires sum < 2^108
    ensures  p < 2^52 && sum + p*L[0] == carry << 52
```

**Proof structure**:
1. **p < 2^52**: `by (bit_vector)` (masking bounds the result)
2. **s < 2^52**: `by (bit_vector)` (masking bounds the result)
3. **p == (s * LFACTOR) % 2^52**: `by (bit_vector)` for mask property
4. **(s + p*L[0]) % 2^52 == 0**: Call `lemma_part1_divisible(s, p)`
5. **No overflow**: `by (bit_vector)` for `p*L[0] < 2^102`
6. **Extension**: `s == sum % 2^52` via `by (bit_vector)`, then `lemma_mod_add_eq`
7. **Shift round-trip**: `lemma_u128_right_left_shift_divisible_52`

---

# Supporting Lemmas

| Lemma | Location | Purpose |
|-------|----------|---------|
| `lemma_l_limbs_bounds` | `constants_lemmas.rs` | Bounds on L limbs for overflow checking |
| `lemma_u128_right_left_shift_divisible_52` | `shift_lemmas.rs` | Shift round-trip for divisible values |
| `lemma_mod_add_eq` | `div_mod_lemmas.rs` | `a ≡ b (mod m) ⟹ (a+c) ≡ (b+c) (mod m)` |

---

# Proof Structure Diagram

```
                    MATHEMATICAL                           VERUS
                    ═══════════                           ═════

              LFACTOR * L[0] ≡ -1 (mod 2^52)
                        │
                        ▼
┌─────────────────────────────────────────┐    ┌────────────────────────────────────┐
│  (s + p*L[0]) % 2^52 = 0                │ ←→ │ lemma_part1_divisible(s, p)        │
│  where p = s*LFACTOR mod 2^52           │    │   • by(compute) for LFACTOR        │
│                                         │    │   • vstd mul/mod lemmas            │
└─────────────────────────────────────────┘    └────────────────────────────────────┘
                        │                                     │
                        │                                     │
                        ▼                                     ▼
┌─────────────────────────────────────────┐    ┌────────────────────────────────────┐
│  Extension: sum ≡ s (mod 2^52)          │    │ lemma_part1_correctness(sum)       │
│  Shift: (x >> 52) << 52 = x if x%2^52=0 │    │   • calls lemma_part1_divisible    │
│                                         │    │   • inline extension (bit_vector)  │
│  ∴ sum + p*L[0] == carry << 52         │    │   • shift round-trip               │
└─────────────────────────────────────────┘    └────────────────────────────────────┘
```

---

# Notes

**Original code** used `wrapping_mul` which Verus can't handle in `by (bit_vector)`. The refactored code extracts low 52 bits first, avoiding wrapping semantics.
