# Natural Number Conversion Architecture

This document describes the architecture for converting byte arrays and word arrays (limbs) to natural numbers in the Verus-verified curve25519-dalek codebase.

## Overview

Converting bytes and words to natural numbers (little-endian interpretation) is fundamental throughout the codebase. This document explains:
- Canonical primitives in `core_specs.rs`
- Domain-specific wrappers for field and scalar operations
- The `*_to_nat` naming convention
- Lemma organization

### Two Main Representations

| Representation | Spec Function | Form | Primary Use Case |
|----------------|---------------|------|------------------|
| **Prefix sum** | `bytes_to_nat_prefix` | b₀·2⁰ + b₁·2⁸ + ... | Small fixed-size inputs, `From<uXX>` |
| **Horner form** | `bytes_seq_to_nat` | b₀ + 256·(b₁ + 256·(...)) | Any-length sequences, loop-based processing |

**Design rationale:** The prefix form is simpler for small fixed-size inputs where we know the exact length at compile time. The Horner form works with any-length `Seq<u8>` and is preferred for loop-based processing (e.g., `from_bytes_wide` with 64-byte inputs) where the recursive structure aligns naturally with iteration.

## Naming Convention: `*_to_nat`

All conversion functions follow the `*_to_nat` naming convention:

| Function | Location | Purpose |
|----------|----------|---------|
| **Byte Conversions** | | |
| `bytes32_to_nat` | `core_specs.rs` | 32-byte array → nat (explicit form) |
| `bytes_seq_to_nat` | `core_specs.rs` | Seq<u8> (any length) → nat (Horner form) |
| `bytes_to_nat_prefix` | `core_specs.rs` | First n bytes of sequence → nat |
| `bytes_to_nat_suffix` | `core_specs.rs` | bytes[start..N] with positional weights → nat |
| `bytes32_to_nat_rec` | `core_specs.rs` | Recursive helper for 32-byte |
| **Word Conversions** | | |
| `words_to_nat_gen` | `core_specs.rs` | Generic word array → nat (any radix) |
| `words_to_nat_u64` | `core_specs.rs` | u64 word array → nat (convenience) |
| `word64_from_bytes` | `core_specs.rs` | Extract 64-bit word from byte sequence |
| `word64_from_bytes_partial` | `core_specs.rs` | Extract partial 64-bit word |
| `words64_from_bytes_to_nat` | `core_specs.rs` | Extract multiple 64-bit words → nat |
| **Domain-Specific** | | |
| `fe_to_nat` | `field_specs.rs` | FieldElement51 limbs → nat |
| `u64_5_as_nat` | `field_specs_u64.rs` | 5 limbs × 51-bit radix → nat |
| `five_limbs_to_nat_aux` | `scalar52_specs.rs` | 5 limbs × 52-bit radix → nat |
| `seq_to_nat_52` | `scalar52_specs.rs` | Seq<nat> × 52-bit radix → nat (Horner) |

---

## Part 1: Byte-to-Nat Conversions

### Prefix Sum Form (Primary for small inputs)

```rust
/// Direct-sum form for the first n bytes.
pub open spec fn bytes_to_nat_prefix(bytes: Seq<u8>, n: nat) -> nat
```

- Computes: `b₀·2⁰ + b₁·2⁸ + ... + bₙ₋₁·2^((n-1)·8)`
- **Primary use:** `From<u16>`, `From<u32>`, `From<u64>`, `From<u128>` implementations
- **Advantage:** Direct form, no need for Horner-to-prefix bridge lemmas

### Horner Form (For any-length sequences)

```rust
/// Horner-form conversion (little-endian) for arbitrary-length sequences.
pub open spec fn bytes_seq_to_nat(bytes: Seq<u8>) -> nat
    decreases bytes.len(),
{
    if bytes.len() == 0 { 0 }
    else { (bytes[0] as nat) + 256 * bytes_seq_to_nat(bytes.skip(1)) }
}
```

- **Primary use:** `from_bytes_wide` (64-byte inputs), `from_bytes_mod_order_wide`
- Uses Horner form: `bytes[0] + 256 * (bytes[1] + 256 * (...))`
- Bridge lemma: `lemma_bytes_seq_to_nat_equals_prefix` connects to prefix form

### For 32-byte Arrays

```rust
/// Explicit 32-term expansion for efficient proof unfolding.
pub open spec fn bytes32_to_nat(bytes: &[u8; 32]) -> nat {
    bytes[0] as nat * pow2(0*8) + bytes[1] as nat * pow2(1*8) + ... // all 32 terms
}

/// Recursive version for structural induction proofs.
pub open spec fn bytes32_to_nat_rec(bytes: &[u8; 32], index: nat) -> nat
```

### For 64-byte Arrays

Use `bytes_seq_to_nat(bytes@)` directly. For loop invariants, use:

```rust
/// Generic suffix sum with original positional weights.
pub open spec fn bytes_to_nat_suffix<const N: usize>(bytes: &[u8; N], start: int) -> nat
```

---

## Part 2: Word-to-Nat Conversions

### Generic Word Conversion

```rust
/// THE fully generic primitive - works with any word type via Seq<nat>
pub open spec fn words_to_nat_gen(
    words: Seq<nat>,      // Use arr@.map(|i, x| x as nat) to convert
    num_words: int, 
    bits_per_word: int
) -> nat

/// Convenience wrapper for u64 arrays
pub open spec fn words_to_nat_u64(words: &[u64], num_words: int, bits_per_word: int) -> nat
```

**Usage for different word types:**
```rust
words_to_nat_u64(words, 4, 64)                           // u64 arrays
words_to_nat_gen(words@.map(|i, x| x as nat), 9, 52)     // u128 arrays
words_to_nat_gen(words@.map(|i, x| x as nat), len, 16)   // u16 arrays
```

### Word Extraction from Bytes

```rust
/// Extract a 64-bit word (8 bytes) from any byte sequence
pub open spec fn word64_from_bytes(bytes: Seq<u8>, word_idx: int) -> nat

/// Extract partial 64-bit word (first `upto` bytes of a word)
pub open spec fn word64_from_bytes_partial(bytes: Seq<u8>, word_idx: int, upto: int) -> nat

/// Sum of extracted 64-bit words to nat (first `count` words)
pub open spec fn words64_from_bytes_to_nat(bytes: Seq<u8>, count: int) -> nat
```

**Usage:** Call with `bytes@` to convert fixed-size arrays:
```rust
word64_from_bytes(bytes@, 0)           // First 64-bit word
words64_from_bytes_to_nat(bytes@, 8)   // All 8 words (64-byte array)
```

---

## Part 3: Domain-Specific Limb Functions

### Why Two Radixes?

| Domain | Radix | Reason |
|--------|-------|--------|
| **Field (51-bit)** | 5 × 51 = 255 bits | Matches 2^255 - 19, leaves 13-bit headroom for carries |
| **Scalar (52-bit)** | 5 × 52 = 260 bits | Covers 253-bit group order with room |

### Field Domain (51-bit radix) — `field_specs_u64.rs`

```rust
/// Canonical for FieldElement51 limbs
pub open spec fn u64_5_as_nat(limbs: [u64; 5]) -> nat {
    limbs[0] as nat +
    pow2( 51) * limbs[1] as nat +
    pow2(102) * limbs[2] as nat +
    pow2(153) * limbs[3] as nat +
    pow2(204) * limbs[4] as nat
}
```

**Alias in `field_specs.rs`:**
```rust
/// Intuitive name for field element interpretation
pub open spec fn fe_to_nat(fe: &FieldElement51) -> nat {
    u64_5_as_nat(fe.limbs)
}
```

### Scalar Domain (52-bit radix) — `scalar52_specs.rs`

```rust
/// Base recursive (52-bit radix, Horner form)
pub open spec fn seq_to_nat_52(limbs: Seq<nat>) -> nat

/// Explicit 5-limb for Scalar52
pub open spec fn five_limbs_to_nat_aux(limbs: [u64; 5]) -> nat

/// Explicit 9-limb for intermediate results
pub open spec fn nine_limbs_to_nat_aux(limbs: &[u128; 9]) -> nat

/// Derived wrappers
pub open spec fn to_nat(limbs: &[u64]) -> nat
pub open spec fn slice128_to_nat(limbs: &[u128]) -> nat
```

---

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          CORE SPECS (core_specs.rs)                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  BYTE-TO-NAT:                                                               │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ bytes_to_nat_prefix(Seq, n)     ← PRIMARY for small inputs (2-16B)  │   │
│  │ bytes32_to_nat(&[u8; 32])       ← 32-BYTE (explicit form)           │   │
│  │ bytes_seq_to_nat(Seq<u8>)       ← ANY-LENGTH sequences (Horner)     │   │
│  │ bytes_to_nat_suffix<N>          ← LOOP INVARIANTS (any size)        │   │
│  │ bytes32_to_nat_rec              ← 32-BYTE (recursive helper)        │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  WORD-TO-NAT:                                                               │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ words_to_nat_gen(Seq<nat>, n, bits) ← GENERIC (any radix)           │   │
│  │ words_to_nat_u64(&[u64], ...)       ← u64 convenience               │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  WORD EXTRACTION (bytes → 64-bit words):                                    │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ word64_from_bytes(Seq<u8>, idx)     ← single 64-bit word            │   │
│  │ word64_from_bytes_partial           ← partial 64-bit word           │   │
│  │ words64_from_bytes_to_nat         ← multiple 64-bit words → nat   │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
                    │
        ┌───────────┼───────────────────────┐
        ▼           ▼                       ▼
┌───────────────┐ ┌─────────────────┐ ┌─────────────────────────────────────┐
│ field_specs   │ │ field_specs_u64 │ │ scalar52_specs                    │
│               │ │                 │ │                                     │
│ fe_to_nat     │ │ u64_5_as_nat    │ │ seq_to_nat_52 (52-bit, Horner)      │
│ (alias)       │ │ (51-bit radix)  │ │ five_limbs_to_nat_aux               │
│               │ │                 │ │ nine_limbs_to_nat_aux               │
└───────────────┘ └─────────────────┘ └─────────────────────────────────────┘
                    │
                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           LEMMAS                                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  to_nat_lemmas.rs (common_lemmas/):                                         │
│  BYTE LEMMAS:                         │  WORD LEMMAS:                       │
│  • lemma_from_le_bytes (From<uXX>)    │  • lemma_words_to_nat_upper_bound   │
│  • lemma_bytes32_to_nat_with_trailing │  • lemma_words_to_nat_equals_bytes  │
│  • lemma_prefix_equal_when_bytes_...  │  • lemma_words64_from_bytes_to_nat_ │
│  • lemma_bytes_seq_to_nat_equals_...  │                                     │
│  • lemma_canonical_bytes_equal        │                                     │
│  • lemma_bytes32_to_nat_equals_rec    │                                     │
│                                       │                                     │
│  u64_5_as_nat_lemmas.rs:              │  scalar_lemmas.rs:                  │
│  • lemma_u64_5_as_nat_add/sub/squared │  • lemma_five_limbs_equals_to_nat   │
│  • lemma_u64_5_as_nat_k               │  • lemma_nine_limbs_equals_slice128 │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Domain Usage Summary

| Domain | Import | Usage | Form |
|--------|--------|-------|------|
| Scalar (32-byte) | `core_specs::*` | `bytes32_to_nat(&bytes)` | Explicit sum |
| Any-length sequences | `core_specs::*` | `bytes_seq_to_nat(seq)` | Horner |
| `From<u16/u32/u64/u128>` | `core_specs::*` | `bytes_to_nat_prefix(bytes@, N)` | Prefix sum |
| Field bytes | `core_specs::*` | `bytes32_to_nat(&bytes)` | Explicit sum |
| Field element | `field_specs::*` | `fe_to_nat(&fe)` | Domain-specific |
| Word extraction | `core_specs::*` | `words64_from_bytes_to_nat(bytes@, count)` | Word-based |

**No aliases for bytes!** One canonical `bytes32_to_nat` in `core_specs.rs`.

---

## Key Lemmas

### Byte-to-Nat Lemmas (`common_lemmas/to_nat_lemmas.rs`)

```rust
// Bridge lemmas (prefix form)
lemma_bytes32_to_nat_equals_rec(bytes)          // explicit ↔ recursive (32-byte)
lemma_bytes32_to_nat_with_trailing_zeros(b, n)  // explicit → prefix when zeros at end
lemma_prefix_equal_when_bytes_match(s1, s2, n)  // prefix equal if bytes match

// Bridge lemmas (Horner form - for 64-byte wide inputs)
lemma_bytes_seq_to_nat_equals_prefix(seq)       // Horner ↔ prefix (any length)
lemma_bytes32_to_nat_equals_suffix_64(bytes)    // Horner ↔ suffix (64-byte)

// Conversion helpers
lemma_from_le_bytes(le_seq, bytes, n)           // For From<uXX> implementations

// Injectivity
lemma_canonical_bytes_equal(b1, b2)             // same nat → same bytes
```

**Unused lemmas** (in `unused_to_nat_lemmas.rs`):
```rust
lemma_bytes32_to_nat_equals_horner(bytes)   // No longer needed after simplification
bytes32_to_nat_le_pow2_256(bytes)           // Upper bound (kept for reference)
bytes_seq_to_nat_64_le_pow2_512(bytes)      // Upper bound (kept for reference)
```

### Word-to-Nat Lemmas (`common_lemmas/to_nat_lemmas.rs`)

```rust
// Bounds
lemma_words_to_nat_upper_bound(words, count)

// Bridge: word array ↔ underlying bytes  
lemma_words_to_nat_equals_bytes(words, bytes, count)

// Explicit expansion (for from_bytes_wide)
lemma_words_from_bytes_to_nat_wide(bytes)
```

### Limb Equivalence Lemmas (`scalar_lemmas.rs`)

```rust
lemma_five_limbs_equals_to_nat(limbs)           // explicit ↔ recursive
lemma_nine_limbs_equals_slice128_to_nat(limbs)  // explicit ↔ recursive
```

### Field Element Limb Lemmas (`u64_5_as_nat_lemmas.rs`)

```rust
// Arithmetic on [u64; 5] field element limbs (51-bit radix)
lemma_u64_5_as_nat_add(a, b)       // u64_5_as_nat(a) + u64_5_as_nat(b)
lemma_u64_5_as_nat_sub(a, b)       // u64_5_as_nat(a) - u64_5_as_nat(b)
lemma_u64_5_as_nat_squared(v)      // u64_5_as_nat(v)²
lemma_u64_5_as_nat_k(a, k)         // k * u64_5_as_nat(a)

// Bridge between pow and as_nat representations
lemma_bridge_pow_to_nat_to_spec(...)
```

---

## Design Rationale

### Why explicit `bytes32_to_nat` for 32-byte?

Many proofs unfold `bytes32_to_nat` to reason about individual bytes. Using `bytes_seq_to_nat` would require `reveal_with_fuel(_, 32)` everywhere. The explicit form:
- Provides direct structural visibility for SMT solver
- Avoids `reveal_with_fuel` in most proofs
- Better verification performance

### Key Bridge: `lemma_bytes32_to_nat_with_trailing_zeros`

This lemma is now the primary bridge for connecting `bytes32_to_nat` to smaller inputs:
```rust
// When bytes n..31 are zero:
bytes32_to_nat(bytes) == bytes_to_nat_prefix(bytes@, n)
```

**Used by:** `lemma_from_le_bytes` for `From<u16/u32/u64/u128>` implementations.

For 64-byte inputs, use `lemma_bytes_seq_to_nat_equals_prefix` to bridge Horner ↔ prefix forms.

### Why `Seq<nat>` for `words_to_nat_gen`?

Works with any integer type via `.map(|i, x| x as nat)`. No need for separate `words_to_nat_u128`, etc.

### Why `Seq<u8>` for word extraction?

Unlike `&[u8]` slices, `bytes@` works directly in spec mode without needing `as_slice()`.

### Why domain-specific limb functions?

Different radixes (51 vs 52 bits) are fundamental to field vs scalar operations. Can't be generalized away.

---

## Naming Convention Discussion: `*_to_nat` vs `*_as_nat`

**Current state:** Mixed naming — `u64_5_as_nat` (678 occurrences) vs `bytes32_to_nat` (983 occurrences).

### The Trade-off

| Pattern | Rust Convention | Semantic Fit for Specs |
|---------|-----------------|------------------------|
| `*_as_nat` | `as_*` returns reference/view | ✅ "Interpret as" — matches spec semantics |
| `*_to_nat` | `to_*` returns owned value | ⚠️ "Convert to" — implies runtime transformation |

### Arguments for `*_as_nat`

1. **Semantic accuracy:** Spec functions interpret/view data AS a natural number, not convert TO one
2. **Rust idiom:** `as` in Rust means "view as" (like `as_bytes()`, `x as u64`)
3. **Already dominant:** `u64_5_as_nat` with 678 occurrences already uses this pattern

### Arguments for `*_to_nat`

1. **Strict Rust convention:** `as_*` should return references; we return values
2. **Familiarity:** `to_*` is common in many APIs
3. **Currently more prevalent:** 983 occurrences use `_to_nat`

## Recommendations for New Code

1. **32-byte arrays:** `bytes32_to_nat(&array)` from `core_specs.rs`
2. **Small byte sequences (2-16 bytes):** `bytes_to_nat_prefix(bytes@, N)` — simpler, no Horner needed
3. **64-byte arrays:** `bytes_seq_to_nat(bytes@)` — uses Horner form for `from_bytes_wide`
4. **Loop invariants:** `bytes_to_nat_suffix(bytes, start)`
5. **Word arrays:** `words_to_nat_gen` or `words_to_nat_u64`
6. **Field elements:** `fe_to_nat(&fe)` from `field_specs.rs`
7. **`From<uXX>` implementations:** Use `lemma_from_le_bytes` with `bytes_to_nat_prefix`

---

## Related Files

- `curve25519-dalek/src/specs/core_specs.rs` — All core conversion specs
- `curve25519-dalek/src/specs/field_specs.rs` — Field-specific (`fe_to_nat`, postconditions)
- `curve25519-dalek/src/specs/field_specs_u64.rs` — Field limb functions (51-bit)
- `curve25519-dalek/src/specs/scalar52_specs.rs` — Scalar limb functions (52-bit)
- `curve25519-dalek/src/lemmas/common_lemmas/to_nat_lemmas.rs` — Active byte/word-to-nat lemmas
- `curve25519-dalek/src/lemmas/common_lemmas/unused_to_nat_lemmas.rs` — Deprecated/unused lemmas
- `curve25519-dalek/src/lemmas/scalar_lemmas.rs` — Limb equivalence lemmas

