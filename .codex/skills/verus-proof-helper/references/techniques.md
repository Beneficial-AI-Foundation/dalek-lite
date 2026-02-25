# Proof techniques

## 1) Bit-vector reasoning (`by (bit_vector)`)

Use for:

- shifts/masks (`>>`, `&`, `|`, `^`)
- connecting bit ops to arithmetic facts (e.g., `% 2`)

```rust
assert(byte < 128 ==> (byte >> 7) == 0) by (bit_vector);
assert((byte & 1 == 1) == (byte % 2 == 1)) by (bit_vector);

assert(byte_after == byte_before + (sign_bit << 7)) by (bit_vector)
    requires
        (byte_before >> 7) == 0,
        sign_bit == 0 || sign_bit == 1;
```

## 2) Nonlinear arithmetic (`by (nonlinear_arith)`)

Use for multiplication/division inequalities and transitivity chains.

```rust
assert((byte_after as nat) * pow2(248) >= 128 * pow2(248)) by (nonlinear_arith)
    requires byte_after >= 128;
```

## 3) Decomposition

Use for byte-array / sequence proofs:

- `lemma_decomposition_prefix_rec` to split prefix/suffix
- `lemma_u8_32_as_nat_equals_rec` to connect definitions

## 4) Proof by contradiction

```rust
assert(x < bound) by {
    if x >= bound {
        // derive contradiction using lemmas / bounds
        assert(false);
    }
};
```

## 5) Case analysis

```rust
assert(property) by {
    if condition {
        // true case
    } else {
        // false case
    }
};
```

## 6) `calc!` blocks for equality chains

Use `calc!` to make step-by-step transformations explicit and debuggable.

```rust
calc! {
    (==)
    edwards_scalar_mul(edwards_scalar_mul(point, a), pow2(k));
    (==) { /* apply a lemma */ }
    { let half = edwards_scalar_mul(edwards_scalar_mul(point, a), pow2(k-1));
      edwards_double(half.0, half.1) };
    (==) { /* use IH */ }
    edwards_scalar_mul(point, a * pow2(k));
}
```

## 7) Induction with `decreases`

```rust
pub proof fn lemma_edwards_scalar_mul_mul_pow2(point: (nat, nat), a: nat, k: nat)
    ensures
        edwards_scalar_mul(edwards_scalar_mul(point, a), pow2(k))
            == edwards_scalar_mul(point, a * pow2(k)),
    decreases k,
{
    if k == 0 {
        assert(pow2(0) == 1) by { lemma2_to64(); }
        reveal_with_fuel(edwards_scalar_mul, 1);
    } else {
        let km1 = (k - 1) as nat;
        lemma_edwards_scalar_mul_mul_pow2(point, a, km1);
        // connect IH to goal via asserts or calc!
    }
}
```

## 8) Compositional reasoning (use postconditions)

Track what helpers guarantee and compose those facts via invariants or small lemmas, instead of re-proving internals.

## 9) Specialized lemmas over general ones

If the general lemma is hard (e.g., full group-law composition), introduce a specialized lemma for your common case (often pow2/doubling), then delete unused general lemmas once the specialized version is sufficient.

## 10) Loop invariants for correctness (not just bounds)

Use invariants to track the mathematical meaning of the loop state and “work done so far”.

```rust
for i in 0..32
    invariant
        0 <= i <= 32,
        edwards_point_as_affine(P) == edwards_scalar_mul(basepoint, pow256(i)),
        forall|j: int|
            #![trigger table.0[j as int]]
            0 <= j < i ==> is_valid_lookup_table_affine_coords(
                table.0[j as int].0,
                edwards_scalar_mul(basepoint, pow256(j as nat)),
                8,
            ),
{
    // ...
}
```

## 11) Strengthen specifications (when needed)

If the proof cannot be completed with the current `requires`/`ensures`, strengthen:

1. Preconditions (most common)
2. Helper postconditions (less common; do only if the helper is under your control)

When changing specs, update all implementations and fix downstream callers.

## 12) Prefer by-value lemma parameters

By-value proof lemma parameters are often easier to call and avoid borrowing friction.

```rust
pub proof fn lemma_foo(x: [i8; 64])
    requires is_valid(&x),
    ensures property(&x),
{ }
```

## 13) Extract common loop-proof logic

If multiple loops share 10–20 lines of proof scaffolding (index math, table selection, reveals), factor it into a helper lemma with a clean contract.

## 14) Avoid SMT blowups (`rlimit`): opaque specs + targeted `reveal`

Use when loop invariants or recursive/quantifier-heavy specs cause `rlimit` timeouts:

- Mark expensive `spec fn` as `#[verifier::opaque]`.
- Keep the opaque predicate in the loop invariant.
- `reveal(...)` only inside small helper lemmas/proof blocks where you need specific conjuncts.

Avoid making *simple* specs opaque; it adds boilerplate and can make SMT harder.

## 15) Assert-by scoping to control rlimit

The most effective technique for fixing `rlimit` timeouts without bumping limits. Wrap every
lemma call inside an `assert(...) by { ... }` block that states the **exact conclusion** the
lemma provides. This confines the lemma's postcondition facts to the inner scope, preventing
Z3 from using them as triggers elsewhere in the proof.

**Before (unscoped — facts leak into Z3's global context):**
```rust
proof {
    lemma_neg_of_signed_scalar_mul(base, neg_digit as int);
    axiom_edwards_add_associative(d0, d1, c0, c1, t0, t1);
}
```

**After (scoped — facts confined to assert-by blocks):**
```rust
proof {
    assert(term == edwards_neg(projective_niels_point_as_affine_edwards(R_j))) by {
        lemma_neg_of_signed_scalar_mul(base, neg_digit as int);
    }
    assert(completed_point_as_affine_edwards(t) == {
        let col_next = straus_column_sum(pts, nafs, i as int, (j + 1) as int);
        edwards_add(d0, d1, col_next.0, col_next.1)
    }) by {
        axiom_edwards_add_associative(d0, d1, c0, c1, t0, t1);
    }
}
```

**Key rules:**
- The assert target should be the **fact you actually need** for the loop invariant or next step
- Multiple lemmas that contribute to one fact can share one assert-by block
- `use_type_invariant(x)` does **NOT** work inside assert-by blocks (mode error); keep it unscoped
- `lemma_unfold_edwards(x)` is a common rlimit offender; always scope it

**When to apply:** Any time you see an rlimit failure, look for unscoped lemma calls in the
failing loop/function body. Scoping them is almost always sufficient — avoid bumping `rlimit`
unless the proof is genuinely complex.

## 16) Explicit triggers over `#![auto]`

Replace `#![auto]` on quantified invariants with explicit `#[trigger]` annotations to control
Z3 quantifier instantiation. `#![auto]` lets Verus choose triggers, which can cause excessive
matching in large proof contexts.

**Before (auto triggers — Z3 may over-instantiate):**
```rust
forall|j: int|
    #![auto]
    i <= j < n ==> is_inverse(&original_inputs[j], &inputs[j]),
forall|j: int|
    #![auto]
    0 <= j < n ==> scalar52_as_nat(&scratch[j]) % group_order() == ...,
```

**After (explicit triggers — controlled instantiation):**
```rust
forall|j: int|
    i <= j < n ==> is_inverse(&#[trigger] original_inputs[j], &inputs[j]),
forall|j: int|
    0 <= j < n ==> scalar52_as_nat(&#[trigger] scratch[j]) % group_order() == ...,
```

**Guidelines:**
- Pick a trigger that uniquely identifies the quantified variable (usually an array index like `arr[j]`)
- Prefer triggers on the **least-common** collection to minimize spurious matches
- Each quantified invariant should have exactly one trigger group
- If the same `forall` needs multiple trigger sets, use `#![trigger f(j)] #![trigger g(j)]`

## 17) Bundled validity predicates for loop invariants

When a loop has 10+ invariants from preparation phases, bundle them into a single spec
predicate. This reduces the number of facts Z3 must track per iteration and makes invariants
readable.

```rust
pub open spec fn pippenger_input_valid(
    scalars_points: Seq<(Scalar, ProjectiveNielsPoint)>,
    pts_affine: Seq<(nat, nat)>,
    digits_seqs: Seq<Seq<i8>>,
    w: nat,
    digits_count: nat,
) -> bool {
    &&& scalars_points.len() == pts_affine.len()
    &&& scalars_points.len() == digits_seqs.len()
    &&& 4 <= w <= 8
    &&& forall|k: int| 0 <= k < pts_affine.len() ==>
            (#[trigger] pts_affine[k]).0 < p() && pts_affine[k].1 < p()
    &&& forall|k: int| 0 <= k < digits_seqs.len() ==>
            is_valid_radix_2w_digits(#[trigger] digits_seqs[k], w, digits_count)
    // ... more conjuncts
}
```

**Usage in loop invariant:**
```rust
while digit_index > 0
    invariant
        pippenger_input_valid(scalars_points@, pts_affine, digits_seqs, w as nat, dc),
        // ... only the changing invariants listed separately
```

**Key benefit:** Z3 treats the bundled predicate as a single fact. Individual conjuncts are
only exposed when a lemma's precondition explicitly requires them, or when you assert a
specific conjunct.

## 18) Unified loop structure (start from identity)

When an algorithm has a "first iteration" special case followed by a loop (common in Horner
evaluation), prefer a single unified loop starting from the identity element. This avoids
duplicating proof obligations.

**Instead of:**
```rust
// Process first column separately
let mut total = process_column(dc - 1);
// Loop for remaining columns
while digit_index > 0 {
    total = total.mul_by_pow_2(w) + process_column(digit_index - 1);
}
```

**Prefer:**
```rust
let mut total = EdwardsPoint::identity();
proof { lemma_pippenger_horner_base(pts, digs, w, dc); }
let mut digit_index = digits_count;
while digit_index > 0
    invariant
        edwards_point_as_affine(total) == pippenger_horner(pts, digs, digit_index as int, w, dc),
{
    digit_index -= 1;
    let shifted = total.mul_by_pow_2(w);
    let column = /* inline column processing */;
    total = &shifted + &column;
    proof { lemma_pippenger_horner_step(...); }
}
```

The identity-based approach needs one base-case lemma (`H(dc) = O`) but avoids duplicating
the column processing code and its proof obligations.
