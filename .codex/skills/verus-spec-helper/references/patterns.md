# Spec patterns (templates to reuse)

## Axiom docstring pattern

Every `axiom_` function doc comment must include:
1. **One-line math statement** — the identity/property in math notation
2. **Spec-to-math name mapping** — `spec_fn_name() = symbol = formula`
3. **Reference pin** — paper/section/URL
4. **Gap note** — what remains unproved (if applicable)
5. **Runtime validation** — `Runtime validation: \`test_name\` in file.rs`

## Spec independence

Doc comments should be readable without exec function names:
- BAD: "Mathematical output of `Foo::bar_method`"
- GOOD: "Elligator inverse on the Jacobi quartic: (s, t) → (success, r₀)"
- Include explicit formulas: `y = (1 − S²) / (1 + S²)`

## Reference spec module skeleton

- Co-locate math definitions in `src/specs/<topic>_specs.rs`.
- Start with module-level docs: objects, notation, intended theorems, and any external references.
- Prefer *small* spec helpers that can be reused in `ensures`.

Minimal skeleton:

```rust
use vstd::prelude::*;
verus! {
// Domain objects: nat/Seq-based, not exec structs.
pub open spec fn spec_op(x: nat, y: nat) -> nat { /* math definition */ }

pub open spec fn is_valid_x(x: nat) -> bool { /* invariants */ }
}
```

## Exec ↔ spec bridging

- Put exec correctness in one or two “load-bearing” postconditions.
- Keep algorithmic details out of the postconditions.

```rust
pub fn foo(x: Foo) -> (out: Bar)
    requires
        is_well_formed_foo(x),
    ensures
        out@ == spec_foo(x@),
{
    /* ORIGINAL CODE: ... */
    ...
}
```

## Uninterpreted spec + admitted axiom

Use when you need a spec handle before you can (or want to) define/verify it.

```rust
verus! {
pub uninterp spec fn spec_hash(input: Seq<u8>) -> Seq<u8>;

pub proof fn axiom_hash_len(input: Seq<u8>)
    ensures spec_hash(input).len() == 32
{ admit(); }
}
```

## Reduce repetition in `ensures`

- Prefer helper spec functions or quantified facts over copy/paste.

Example: “cosets”/tables/spec arrays:

```rust
ensures
    forall|i: int| 0 <= i < 4 ==> #[trigger] result[i]@ == spec_add(base@, spec_torsion(i as nat)),
```

If Verus needs help instantiating, add triggers on the main applications (e.g., `result[i]@`, `spec_add(...)`).

## Trigger hygiene

- Add explicit triggers only when needed; keep them on the *main function applications*.
- Avoid “trigger notes” comments; if you changed a trigger, reflect it directly in `#![trigger ...]`.
- Don’t mix `#![auto]` with lots of manual triggers in the same area; pick one approach per cluster.

## Modeling external code (e.g., `Digest`)

- Prefer modeling cryptographic primitives in `core_assumes.rs` (uninterp `spec_*` + admitted axioms).
- Put the real exec call in a wrapper `fn` with an `ensures` clause relating it to the spec model.
