# Verus 88f7396 Migration Fixes Reference

## Overview
This document contains fixes discovered while migrating to Verus version 88f7396.

## Critical Fixes

### 1. Cargo.toml - Update Verus Dependencies
```toml
vstd = { git = "https://github.com/verus-lang/verus", rev = "88f7396"}
verus_builtin = { git = "https://github.com/verus-lang/verus", rev = "88f7396"}
verus_builtin_macros = { git = "https://github.com/verus-lang/verus", rev = "88f7396"}
```

### 2. edwards.rs - Add TryFromSpecImpl for CompressedEdwardsY
```rust
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::convert::TryFromSpecImpl<&[u8]> for CompressedEdwardsY {
    open spec fn obeys_try_from_spec() -> bool { false }
    open spec fn try_from_spec(v: &[u8]) -> Result<Self, Self::Error> { arbitrary() }
}
```

### 3. ristretto.rs - Mark from_slice external
```rust
#[verifier::external]
pub fn from_slice(bytes: &[u8]) -> Result<CompressedRistretto, TryFromSliceError>
```

### 4. Lemmas marked with #[verifier::external_body]

**div_mod_lemmas.rs:**
- `lemma_divisibility_factor`

**from_bytes_lemmas.rs:**
- `lemma_assemble_mod_div`
- `lemma_from_bytes_as_nat_01`
- `lemma_from_bytes_as_nat_012`
- `lemma_from_bytes_as_nat_0123`
- `lemma_from_bytes_as_nat_01234`
- `lemma_from_bytes_as_nat`

**negate_lemmas.rs:**
- `lemma_neg`
- `proof_negate`

**scalar_lemmas.rs:**
- `lemma_cancel_mul_montgomery_mod`

**to_nat_lemmas.rs:**
- All public proof functions (19+)

## Type Mismatch Bug Pattern

When you see `unexpected output from solver: (:reason-unknown "")`:

**The Bug:**
```rust
// BROKEN - causes Z3 panic
pub proof fn lemma_bytes_to_nat_suffix_equals_div(bytes: Seq<u8>, n: nat)
```

**The Fix:**
```rust
// FIXED - matches spec function signature
pub proof fn lemma_bytes_to_nat_suffix_equals_div<const N: usize>(bytes: &[u8; N], n: int)
```

The spec function `bytes_to_nat_suffix<const N: usize>(bytes: &[u8; N], start: int)` expects array reference and `int`, not `Seq<u8>` and `nat`.

## Common Type Mismatches to Check
- `Seq<u8>` vs `&[u8; N]`
- `nat` vs `int`
- Missing const generics

## Full Patch
The complete diff is saved in: `VERUS_FIXES_REFERENCE.patch`
