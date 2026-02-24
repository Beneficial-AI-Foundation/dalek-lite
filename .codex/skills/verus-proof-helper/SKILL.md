---
name: verus-proof-helper
description: Help complete and debug Verus proofs in verified-cryptography Rust codebases (e.g., curve25519-dalek). Use when replacing `admit()`/`assume(...)`, proving byte/nat conversions + bounds, bit-vector facts, modular arithmetic, writing loop invariants, strengthening specs, or handling Verus `rlimit`/timeout issues via opaque specs + targeted `reveal`.
---

# Verus Proof Helper

## Quick start

- Identify the exact goal (postcondition/lemma) and list remaining `admit()`/`assume(...)`.
- Search for existing lemmas before writing new ones (`references/lemma-reference.md`).
- Sketch the proof with the "moving `assume(false)`" technique; verify after each replacement (`references/workflow.md`).
- Apply targeted tactics (`bit_vector`, `nonlinear_arith`, `calc!`, induction, decomposition) (`references/techniques.md`).
- If Verus is stuck (`rlimit`, quantifier instantiation, mode errors), apply the fixes in `references/common-issues.md`.
- Finish by simplifying assertions and writing a short wrap-up (`references/quality-bar.md`).

## Crypto codebases: common tips

- Cache exec-only calls (e.g., `invert()`) into locals; don't call exec fns inside `proof {}` blocks (`references/patterns.md`).
- Preserve executable code as much as possible; when refactoring is needed for verification, keep it targeted and record the original snippet with `/* ORIGINAL CODE: ... */` (or `// ORIGINAL CODE:`) near the change.
- When specs give only "representation-level" facts (e.g., limb equality), explicitly lift them to semantic equality (field value / struct equality) (`references/patterns.md`).
- If direct equality is awkward/unsupported, compare canonical encodings (bytes/limbs) using existing helper APIs and reason about their specs (`references/patterns.md`).
- Don't duplicate equality work: if `==` is already specified via canonical bytes or `ct_eq`, branch on `==` and then use its `ensures` to bridge to the spec fact you need (`references/patterns.md`, `references/common-issues.md`).
- **rlimit fix priority:** scope lemma calls in `assert(...) by {}` > explicit triggers > bundled predicates > opaque+reveal > bump rlimit (last resort). See techniques #15-17.
- If you hit rarer tool limitations (e.g., `by (compute)` stability), see `references/common-issues.md`.
- If the repo uses `verusfmt`, run it on touched files before final verification/commit (`references/workflow.md`).

## Type invariants and `use_type_invariant`

**Mode rules for `use_type_invariant`:**
- Works inside `proof { }` blocks on **exec-level variables** (exec -> proof mode promotion).
- Does **NOT** work in standalone `proof fn` -- parameters default to spec mode, not proof/tracked.
- Does **NOT** work inside `assert(...) by { ... }` -- captured variables become spec mode.
- To use on an `exec const`, bind it to a local at exec level first, then reference it in `proof { }`.

**`exec const` vs `spec fn`:**
`exec const` values cannot be referenced in `spec fn` bodies (mode error). When you need the same value in spec mode, create a separate `spec fn` with duplicated literals and an `ensures` clause on the exec const to bridge the two worlds.

### Type invariant + existential (`choose`) interaction

**Problem:** When a spec predicate uses `exists|point: EdwardsPoint| ...`, calling `choose` yields a spec-mode witness. You **cannot** call `use_type_invariant` on spec-mode values, so type invariant properties (limb bounds, sum_of_limbs_bounded, etc.) are not available on the chosen witness.

**Solution -- strengthen the existential to include type invariant properties:**
```rust
pub open spec fn is_valid_affine_niels_point(niels: AffineNielsPoint) -> bool {
    exists|point: EdwardsPoint|
        is_valid_edwards_point(point)
        && edwards_point_limbs_bounded(point)
        && sum_of_limbs_bounded(&edwards_y(point), &edwards_x(point), u64::MAX)
        && #[trigger] affine_niels_corresponds_to_edwards(niels, point)
}
```
Now when you `choose` a witness satisfying this existential, the limb bounds and sum bounds are directly available without needing `use_type_invariant`.

**Visibility constraint in `pub open spec fn`:** Bodies of `pub open spec fn` must be well-formed everywhere. You **cannot** access `pub(crate)` fields directly (e.g., `point.Y`, `point.X`). Use public closed spec accessors instead:
```rust
// BAD: "disallowed: field expression for an opaque datatype"
sum_of_limbs_bounded(&point.Y, &point.X, u64::MAX)

// GOOD: use public accessors
sum_of_limbs_bounded(&edwards_y(point), &edwards_x(point), u64::MAX)
```

**Bridge asserts for reference-based predicates:** When the type invariant uses direct field access (`&self.Y`) but the strengthened existential uses accessors (`&edwards_y(point)`), the solver may not connect them automatically. Add explicit bridge asserts:
```rust
proof {
    use_type_invariant(*self);
    assert(edwards_y(*self) == self.Y);  // bridge
    assert(edwards_x(*self) == self.X);  // bridge
    assert(sum_of_limbs_bounded(&self.Y, &self.X, u64::MAX));
    assert(sum_of_limbs_bounded(&edwards_y(*self), &edwards_x(*self), u64::MAX));
}
```

**Updating `choose` call sites:** After strengthening the existential, update all `choose` calls to match the new conjuncts. Then replace any calls to the removed bridge lemma with `lemma_unfold_edwards(witness)` + bridge asserts as needed.

## Where to put helper lemmas

Put new lemmas in the right module: **generic field algebra** (any d) -> `field_lemmas/field_algebra_lemmas.rs`; **Ed25519 curve structure** -> `edwards_lemmas/curve_equation_lemmas.rs`; **decompression / Montgomery->Edwards** -> `edwards_lemmas/decompress_lemmas.rs`. Prefer calling field lemmas directly at call sites; avoid thin wrappers and redundant "connection" lemmas. See `references/lemma-reference.md` for the full table and guidelines.

## Reference map

- `references/workflow.md`: step-by-step workflow + verification commands
- `references/lemma-reference.md`: where to put new lemmas + where to look + common lemma names/patterns
- `references/techniques.md`: proof tactics and patterns (including opaque + `reveal`)
- `references/common-issues.md`: common Verus error messages and fixes
- `references/patterns.md`: worked mini-patterns from "compress" proof work
- `references/quality-bar.md`: success criteria and end-of-session summary checklist
