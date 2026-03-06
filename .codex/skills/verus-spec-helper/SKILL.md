---
name: verus-spec-helper
description: Write, review, and tighten Verus specifications in verified-cryptography Rust codebases (e.g., curve25519-dalek). Use when drafting `spec fn`/`proof fn` specs, strengthening `requires`/`ensures`, connecting exec code to reference mathematical specs, minimizing refactors while preserving clear original-to-refactored correspondence, or managing ghost imports/cfg so `cargo build` and `cargo verus verify` both work.
---

# Verus Spec Helper

## Overview

Write reference-style (math-level) specifications and connect executable Rust code to those specs with tight, readable `requires`/`ensures` — without doing the full proofs yet (use `admit()` where needed).

A specification is formed of:
- `verus! { ... }` blocks wrapping spec and proof code
- `ensures` and `requires` clauses on exec functions
- Abstract `spec fn` definitions used in those clauses
- Making sure the code builds (`cargo build`) and verifies (`cargo verus verify`) with proof bypasses (`admit()`)

## Quick start

1. **Intent first**: what mathematical object/function is this (field arithmetic, group law, encoding/decoding, hash model)?
2. **Reuse existing vocab**: search `curve25519-dalek/src/specs/` and `curve25519-dalek/src/core_assumes.rs` before inventing new spec functions.
3. **Reference spec first**: add math definitions + key properties in `src/specs/*_specs.rs`, then attach exec code to it with `ensures`.
4. **Preserve correspondence**: small refactor blocks, `/* ORIGINAL CODE: ... */` nearby, function order preserved.
5. **Build hygiene**: isolate ghost code inside `verus! { ... }` blocks; avoid import/cfg churn.

## Spec writing goals (what "good" looks like)

- **Declarative** specs: relate inputs/outputs to reference spec functions (don't re-implement the algorithm in `ensures`).
- **Precise domain**: well-formedness, bounds, subgroup/torsion membership, invertibility/nonzero denominators, length constraints.
- **Explicit intended property**: soundness, roundtrip, uniqueness, invariants preserved.
- **Readable doc comments** matching the style of existing `src/specs/*_specs.rs` files.

## Spec function naming convention

| Category | Prefix | When to use | Examples |
|----------|--------|-------------|---------|
| **Exec-correspondence** | `spec_` | Function whose primary role is the `ensures` target of an exec function | `spec_lizard_encode`, `spec_elligator_ristretto_flavor`, `spec_fe51_from_bytes` |
| **Pure math** | (none) | Mathematical definitions, pipeline intermediates, predicates — no direct exec counterpart | `lizard_fe_bytes`, `lizard_r`, `lizard_preimage`, `edwards_add`, `field_mul` |
| **Validity predicates** | `is_` | Boolean well-formedness / membership tests | `is_well_formed_edwards_point`, `is_on_edwards_curve`, `is_square` |
| **Axioms (admitted)** | `axiom_` | Proof functions with `admit()` body | `axiom_elligator_injective` |
| **Lemmas (proved)** | `lemma_` | Fully proved proof functions | `lemma_lizard_decode_sound`, `lemma_lizard_roundtrip`, `lemma_from_u8_32_as_nat` |

## Spec function visibility rules

| Kind | When to use | Examples |
|------|-------------|---------|
| `open spec fn` | Default. Body visible everywhere. | `edwards_add`, `field_mul`, `lizard_r`, `spec_lizard_encode` |
| `closed spec fn` | Accesses `pub(crate)` fields, or uses `choose` that shouldn't expand | `edwards_x/y/z/t`, `spec_lizard_decode` |
| `uninterp spec fn` | External/opaque behavior with no formal definition | `spec_sha256`, `spec_sha512`, `is_uniform_bytes` |

When using `uninterp`, always pair with admitted axioms that state essential properties.

## Preconditions: `recommends` vs `requires`

| Clause | Meaning | Where used |
|--------|---------|------------|
| `requires` | Strict: violation = verification error | `proof fn`, `#[verifier::external_body]` exec fns |
| `recommends` | Soft: spec returns arbitrary value outside precondition | `spec fn` with optional well-definedness |

## Exec-to-spec bridging

Put exec correctness in one or two "load-bearing" postconditions. Keep algorithmic details out:

```rust
pub fn foo(x: Foo) -> (out: Bar)
    requires is_well_formed_foo(x),
    ensures out@ == spec_foo(x@),
{
    /* ORIGINAL CODE: original_impl(x) */
    let result = verus_friendly_impl(x);
    proof { assert(out@ == spec_foo(x@)) by { admit() }; }
    result
}
```

### Proof bypass patterns

| Pattern | When to use |
|---------|-------------|
| `proof { admit(); }` | Defer entire function proof |
| `assert(...) by { admit() };` | Defer specific bridging assertion |
| `proof { assume(false); }` | Postpone loop body or complex block |
| `// PROOF BYPASS` comment | Always annotate admits — bare tag, no explanation |

Style: use just `// PROOF BYPASS` (no trailing explanation). The `assert(...)` it precedes
is self-documenting. Consolidate multiple asserts into a single `match` when they share
the same discriminant (mirrors the `ensures` structure).

### `external_body` patterns

| Pattern | When to use |
|---------|-------------|
| `#[verifier::external_body]` | Trusted functions: constants, iterators, external crates |
| `#[cfg_attr(verus_keep_ghost, verifier::external_body)]` | Generic/trait APIs; provide verified variant alongside |

## Correspondence rules (minimize refactors)

- Put the refactored/Verus-friendly version immediately after the original, one function at a time.
- If repetition appears in `ensures`, extract a small helper `spec fn`.

### When to add `/* ORIGINAL CODE: ... */` comments

Add an ORIGINAL CODE comment **only when the line was actually changed**.
Lines that are identical to the original get no comment — the absence of a
comment signals "unchanged".

```rust
// Changed: iterator → index loop, fe_j → fes[j]
/* ORIGINAL CODE: for (j, fe_j) in fes.iter().enumerate() { */
for j in 0..8 {
    // Unchanged — no comment needed
    let mut ok = Choice::from((mask >> j) & 1);
    // Changed: fe_j binding replaced by direct indexing
    /* ORIGINAL CODE: let buf2 = fe_j.as_bytes(); */
    let buf2 = fes[j].as_bytes();
```

Keep comments to ~1 line showing the original expression.  Avoid pasting
multi-line blocks — just show the changed expression.

### Common refactors that need tracking

| Original | Verus-friendly | Why |
|----------|---------------|-----|
| `Default::default()` | `[0u8; N]` | Verus doesn't support `Default` trait |
| `for (i, x) in v.iter().enumerate()` | `for i in 0..v.len()` | Verus doesn't support iterators |
| `fe_j` (iterator binding) | `fes[j]` (direct indexing) | Consequence of iterator removal |
| `-x` (field element) | `negate_field(&x)` | Operator overloading unsupported |
| `a \| b` (Choice) | `choice_or(a, b)` | Operator overloading unsupported |
| `ok &= h.ct_eq(&buf2)` | `ok = choice_and(ok, ct_eq_bytes32(&h, &buf2))` | Compound assign + method unsupported |
| `u8::conditional_select(...)` | `select_u8(...)` | Trait method → wrapper |
| `dst[8..24].copy_from_slice(src)` | `write_bytes32_8_to_24(&mut dst, src)` | Slice range unsupported by Verus |
| `D::digest(...)` (generic) | `sha256_hash_bytes(...)` (concrete) | Generic `Digest` trait unsupported |
| `n_found += ok.unwrap_u8()` | `let add: u32 = ok.unwrap_u8() as u32; n_found = n_found + add;` | Split for overflow proof |
| Compound expression | Split with intermediate `let` | Needed to insert proof blocks |

## Doc comment conventions

### Module-level docs

Use `//!` (inner doc comments) with structured sections:

```rust
//! Specifications for <topic>.
//!
//! ## Mathematical objects and notation
//! - domain objects, fields, representations
//!
//! ## <Pipeline / Algorithm summary>
//! brief composition chain or key formulas
//!
//! ## What we specify here
//! - specs provided and deferred work
//!
//! ## References
//! - papers, RFCs, links to exec code
```

### Function-level docs

- `///` consistently. First line: brief mathematical description.
- Body: numbered steps for algorithms, math formulas, RFC references.
- Don't cross-reference exec function names in spec docs.
- Don't describe exec algorithm strategy — keep it mathematical.

Example:

```rust
/// The 32-byte digest `b(m)` — first stage of the Lizard pipeline.
///
/// ```text
/// m ──► [b(m)] ──► r(m) ──► P(m)
///        ^^^^
/// ```
///
/// 1. `digest = SHA256(m)` (32 bytes)
/// 2. Overwrite `digest[8..24]` with `m`  — embeds the recoverable payload
/// 3. `b[0] &= 254` (clear low bit), `b[31] &= 63` (clear two high bits)
```

### Inline body comments

Terse mathematical annotations, not narration:

```rust
let digest = spec_sha256(data);                         // SHA-256(m), 32 bytes
let s = s.update(0, s[0] & 254u8);                     // clear sign bit
```

### Section separators

```rust
// =============================================================================
// Section Title
// =============================================================================
```

### Proof function naming

`axiom_` prefix for `admit()` bodies; `lemma_` for fully proved.
See naming convention table above for full prefix rules.

## Proof techniques

### `reveal` + `choose` for `closed spec fn`

When a `closed spec fn` uses `choose`, revealing it exposes the body to the SMT solver.
The solver can then exploit the `choose` axiom: if `exists|x| P(x)` then `P(choose|x| P(x))`.

If the predicate `P` includes a uniqueness clause (`forall|y| Q(y) ==> y == x`), the solver
can conclude `choose == known_value` when you assert the known value satisfies the predicate.

**Pattern — soundness** (choose satisfies its predicate):
```rust
pub proof fn lemma_decode_sound(point: (nat, nat), data: Seq<u8>)
    ensures
        spec_decode(point) == Some(data) ==> spec_encode(data) == point,
{
    reveal(spec_decode);
    // Solver sees: data = choose|d| is_preimage(d, point) && ...
    // choose axiom: is_preimage(data, point), i.e. encode(data) == point
}
```

**Pattern — roundtrip** (uniqueness forces choose to return the known value):
```rust
pub proof fn lemma_roundtrip(data: Seq<u8>)
    requires data.len() == 16,
    ensures
        has_unique_preimage(spec_encode(data))
            ==> spec_decode(spec_encode(data)) == Some(data),
{
    reveal(spec_decode);
    assert(is_preimage(data, spec_encode(data)));
    // Solver: data satisfies predicate, uniqueness clause forces choose == data
}
```

**Promoting axiom → lemma**: when an `axiom_` (with `admit()`) turns out to be provable
via `reveal` or other techniques, rename to `lemma_` and replace `admit()` with the proof.

**Proof reuse across duplicate functions**: when a wrapper/variant does the same exec steps
as an already-proved function, copy the proof block rather than using `admit()`.
Example: `encode_253_bits` wraps the same logic as `from_uniform_bytes_single_elligator`,
so the same `lemma_from_u8_32_as_nat` + `lemma_as_nat_32_mod_255` proof applies directly.

### Conditional `ensures` with `==>`

When a property depends on a structural possibility (e.g., collision-freedom),
make the `ensures` conditional rather than assuming it always holds:

```rust
ensures
    has_unique_preimage(spec_encode(data))
        ==> spec_decode(spec_encode(data)) == Some(data),
```

This is stronger than requiring `has_unique_preimage` as a precondition: the lemma
is universally quantified, and the caller decides when the antecedent holds.

### Compositional pipeline typing

Make function signatures compose directly — the output type of step N should be the
input type of step N+1:

```rust
pub open spec fn fe_bytes(data: Seq<u8>) -> [u8; 32] { ... }
pub open spec fn r(fe_bytes: &[u8; 32]) -> nat { ... }
pub open spec fn encode(data: Seq<u8>) -> (nat, nat) {
    elligator(r(&fe_bytes(data)))   // direct composition, no conversion
}
```

## Ghost/import hygiene

- `use vstd::prelude::*;` goes **outside** `verus!` blocks at file top.
- Spec-only imports: guard with `#[cfg(verus_keep_ghost)]`.
- Prefer wildcard imports over specific named imports for spec modules.
- Always `#[allow(unused_imports)]` on spec imports.

## Requires/ensures checklist

See `references/checklist.md` for the full checklist.

### Preconditions

- Representation bounds + type invariants
- Curve membership / curve equation
- Subgroup/torsion assumptions
- Nonzero/invertible elements
- Valid encodings, permitted top bits
- Array lengths, indices in range
- Feature guards

### Postconditions

- Result matches reference spec operation
- Invariants preserved (well-formed, bounded, on-curve, in subgroup)
- Encoding/decoding: soundness, roundtrip, uniqueness
- Length/shape constraints
- Avoid procedural ensures that restate the implementation
- Annotate postcondition groups inline with short comments:
  ```rust
  ensures
      match result {
          Some(p) =>
              // Well-formedness
              is_well_formed_edwards_point(p.0)
              && is_in_even_subgroup(p.0)
              // Correctness
              && edwards_point_as_affine(p.0) == spec_fn(...),
          None => ...,
      },
  ```

## Validation

1. **Rust build**: `cargo build -p curve25519-dalek`
2. **Verus verify**: `cargo verus verify -p curve25519-dalek`
3. **Targeted verify**: `cargo verus verify -p curve25519-dalek -- --verify-module <module>`
4. **Error extraction**: `cargo verus verify -p curve25519-dalek 2>&1 | grep -E "^error|verification results:|^   --> |failed this" | head -30`

## Resources

- `references/workflow.md`: spec authoring workflow (reference spec -> exec linkage -> review pass).
- `references/patterns.md`: templates for reference specs, exec/spec bridging, repetition removal, trigger hygiene.
- `references/checklist.md`: detailed requires/ensures checklist.

## Repo anchors (curve25519-dalek)

- Spec modules: `curve25519-dalek/src/specs/` (see `mod.rs` for full list)
- External modeling/axioms: `curve25519-dalek/src/core_assumes.rs`
- Reference spec style: `curve25519-dalek/src/specs/edwards_specs.rs`, `montgomery_specs.rs`
- New module example: `curve25519-dalek/src/specs/lizard_specs.rs`
- Exec-spec bridging: `curve25519-dalek/src/lizard/lizard_ristretto.rs`, `curve25519-dalek/src/ristretto.rs`
