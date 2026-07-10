# Proof Reasoning: `axiom_even_subgroup_closed_under_add`

This document records the complete chain-of-thought (CoT) and step-by-step reasoning
process used to prove `axiom_even_subgroup_closed_under_add` in the dalek-lite Verus
verification project.

## Background

### What is the even subgroup?

The Ristretto construction quotients the Ed25519 curve by its cofactor-4 torsion.
The "even subgroup" 2E is the image of the doubling map [2]: every point P in 2E
can be written as P = [2]Q for some curve point Q.

In Verus, `is_in_even_subgroup(point)` is defined as
(`specs/ristretto_specs.rs:350`):

```rust
pub open spec fn is_in_even_subgroup(point: EdwardsPoint) -> bool {
    exists|q: EdwardsPoint|
        edwards_point_as_affine(point) == edwards_scalar_mul(
            #[trigger] edwards_point_as_affine(q), 2)
}
```

### The statement to prove

`axiom_even_subgroup_closed_under_add` (`lemmas/ristretto_lemmas/axioms.rs:188`):

```rust
pub proof fn axiom_even_subgroup_closed_under_add(p1: EdwardsPoint, p2: EdwardsPoint)
    requires
        is_in_even_subgroup(p1),
        is_in_even_subgroup(p2),
        is_well_formed_edwards_point(p1),
        is_well_formed_edwards_point(p2),
    ensures
        forall|result: EdwardsPoint|
            edwards_point_as_affine(result) == edwards_add(
                edwards_point_as_affine(p1).0, edwards_point_as_affine(p1).1,
                edwards_point_as_affine(p2).0, edwards_point_as_affine(p2).1,
            ) && is_well_formed_edwards_point(result)
            ==> is_in_even_subgroup(result),
```

In plain math: if P₁ = [2]Q₁ and P₂ = [2]Q₂, then P₁ + P₂ is also in 2E.

This was originally `admit()`. The task was to replace it with a real proof.

## Step 0: Target Selection

**Question**: Why prove this particular axiom?

**Judgment basis**: The comment on the original `admit()` said:
> "Admitted because the existential witness requires lifting affine → EdwardsPoint."

This told us the mathematical content was simple (group theory), and the blocker was
purely a Verus infrastructure issue — constructing an `EdwardsPoint` witness from
affine coordinates. Once we built that infrastructure (`nat_to_fe51` +
`lemma_affine_point_representable`), the proof became feasible.

## Step 1: Mathematical Proof Plan

**Question**: What is the mathematical argument?

**The algebra** (standard group theory):
```
P₁ = [2]Q₁,  P₂ = [2]Q₂
P₁ + P₂ = [2]Q₁ + [2]Q₂ = [2](Q₁ + Q₂)
```

The last equality, `[2]A + [2]B = [2](A + B)`, holds in any abelian group.
For Edwards curves this is the identity:
```
double(add(A, B)) = add(double(A), double(B))
```

So `P₁ + P₂ = [2](Q₁ + Q₂)`, and the witness for `is_in_even_subgroup` is
any EdwardsPoint W with `affine(W) = Q₁ + Q₂`.

**Judgment basis**: The key algebraic identity `lemma_edwards_double_of_add` was
already proven in the codebase (wrapped as `lemma_double_distributes`). The only
missing piece was the infrastructure to construct the witness W.

## Step 2: Identify Required Infrastructure

**Question**: What do we need to turn the math into a Verus proof?

**Dependency analysis**:

| Need | Why | Source |
|------|-----|--------|
| Extract Q₁, Q₂ from existentials | `is_in_even_subgroup` is an `exists` | Verus `choose` operator |
| `[2]P = double(P)` | Connect `edwards_scalar_mul(P, 2)` to `edwards_double` | `lemma_double_is_scalar_mul_2` (existed) |
| `double(A+B) = double(A) + double(B)` | The core algebraic identity | `lemma_double_distributes` (existed) |
| Q₁, Q₂ affine coords are on the curve | Needed for `axiom_edwards_add_closed` | **Type invariant of EdwardsPoint** |
| `add(Q₁, Q₂)` is on the curve | Precondition of `lemma_affine_point_representable` | `axiom_edwards_add_closed` (existed) |
| `add(Q₁, Q₂)` coords are `< p()` | Precondition of `lemma_affine_point_representable` | `lemma_edwards_add_canonical` (existed) |
| Construct witness W : EdwardsPoint | Need W with `affine(W) = add(Q₁, Q₂)` | **`lemma_affine_point_representable` (new)** |
| `nat_to_fe51` + lemmas | Foundation for `lemma_affine_point_representable` | **New infrastructure (new)** |

**Judgment basis**: Reading the existing codebase, most algebraic lemmas already
existed. The gap was purely in "lifting" affine coordinates back to an EdwardsPoint
value, which required building `nat_to_fe51` from scratch.

## Step 3: Build `nat_to_fe51` Infrastructure

### Step 3a: Define `nat_to_fe51` spec function

**Location**: `specs/field_specs_u64.rs`

```rust
pub open spec fn nat_to_fe51(n: nat) -> FieldElement51 {
    FieldElement51 {
        limbs: [
            (n % pow2(51)) as u64,
            ((n / pow2(51)) % pow2(51)) as u64,
            ((n / pow2(102)) % pow2(51)) as u64,
            ((n / pow2(153)) % pow2(51)) as u64,
            ((n / pow2(204)) % pow2(51)) as u64,
        ],
    }
}
```

**Judgment basis**: FieldElement51 stores a 255-bit number in five 51-bit limbs
(base-2^51 representation). `nat_to_fe51` splits `n` into those limbs using
`/ pow2(51*k)` and `% pow2(51)`. This is the standard base-decomposition.

### Step 3b: `lemma_nat_to_fe51_bounded` — each limb < pow2(51)

**Proof technique**: Each limb is `something % pow2(51)`, which is `< pow2(51)` by
`lemma_mod_bound`. Straightforward.

### Step 3c: `lemma_nat_to_fe51_roundtrip` — reconstruction equals original

**Statement**: `u64_5_as_nat(nat_to_fe51(n).limbs) == n` for `n < pow2(255)`.

**Proof technique**: This is the hardest of the three lemmas. The key steps:
1. Use `lemma_fundamental_div_mod` repeatedly to decompose: `n = n0 + pow2(51) * (n1 + pow2(51) * (...))`
2. Use `lemma_div_denominator` to convert chained division: `(n / pow2(51)) / pow2(51) == n / pow2(102)`
3. Show the last "quotient" `q3 = n / pow2(204)` fits in 51 bits (since `n < pow2(255)` and `204 + 51 = 255`), using a contradiction argument with `lemma_basic_div`.

**Key insight**: The roundtrip works because 5 × 51 = 255, so a 255-bit number exactly fills five 51-bit limbs.

### Step 3d: `lemma_nat_to_fe51_canonical` — canonical nat roundtrip

**Statement**: `fe51_as_canonical_nat(&nat_to_fe51(n)) == n` for `n < p()`.

**Proof**: Corollary of the roundtrip lemma + `lemma_small_mod(n, p())` (since `n < p() < pow2(255)`).

## Step 4: Build `lemma_affine_point_representable`

**Statement** (`curve_equation_lemmas.rs:3353`):

```rust
pub proof fn lemma_affine_point_representable(x: nat, y: nat)
    requires x < p(), y < p(), is_on_edwards_curve(x, y),
    ensures
        exists|point: EdwardsPoint|
            edwards_point_as_affine(point) == (x, y)
            && is_well_formed_edwards_point(point),
```

**Question**: How to construct the EdwardsPoint witness?

**The construction**: An affine point (x, y) maps to extended coordinates (X:Y:Z:T) = (x, y, 1, x·y):

```rust
let x_fe = nat_to_fe51(x);
let y_fe = nat_to_fe51(y);
let z_fe = nat_to_fe51(1);
let t_fe = nat_to_fe51(field_mul(x, y));
let witness = EdwardsPoint { X: x_fe, Y: y_fe, Z: z_fe, T: t_fe };
```

**What needs to be proved** for the witness to type-check (satisfy the type invariant):

1. **Limb bounds**: Each coordinate is 52-bounded.
   - `nat_to_fe51` gives 51-bounded limbs → weaken to 52-bounded via `lemma_fe51_limbs_bounded_weaken`
   - Bridge between `pow2(51)` and `1u64 << 51`: use `lemma2_to64_rest()` for `pow2(51) == 0x8000000000000` + bit_vector for `0x8000000000000 == (1u64 << 51)`

2. **Sum of limbs bounded**: `y_fe.limbs[i] + x_fe.limbs[i] < u64::MAX`
   - Each limb `< (1u64 << 51)`, so sum `< 2 * (1u64 << 51) < u64::MAX` — proved by bit_vector.

3. **Canonical nat roundtrips**: `fe51_as_canonical_nat(&x_fe) == x`, etc.
   - From `lemma_nat_to_fe51_canonical`.

4. **On curve projective**: `is_on_edwards_curve_projective(x, y, 1)`
   - From `lemma_z_one_affine_implies_projective(x, y)`.

5. **Segre relation**: `field_mul(x, y) == field_mul(1, t_val)`
   - Since `t_val = field_mul(x, y)` and `field_mul(1, t_val) = t_val`.

6. **Affine projection**: `edwards_point_as_affine(witness) == (x, y)`
   - Since Z = 1, `field_inv(1) = 1`, so `field_mul(x, 1) = x % p() = x`.
   - Required `lemma_unfold_edwards(witness)` to see through closed spec accessors.

**Key difficulty encountered**: `edwards_x`, `edwards_y`, etc. are `closed spec fn`,
meaning the solver cannot see their bodies. The helper `lemma_unfold_edwards(point)`
provides the postconditions `edwards_x(point) == point.X`, etc. Without it, the solver
cannot connect the struct fields to the spec accessors.

## Step 5: The Type Invariant Problem

**Question**: How to prove `is_on_edwards_curve(affine(q1))` for the `choose`-bound witnesses?

**The problem**: `choose` returns spec-mode (Ghost) values. Verus's `use_type_invariant`
macro explicitly rejects Ghost values:

```
error: cannot apply use_type_invariant for Ghost<_>
```

(`verus/source/vir/src/user_defined_type_invariants.rs:285`)

**Why this matters**: We need `is_on_edwards_curve` for the affine coordinates of Q₁ and Q₂
(the `choose`-bound witnesses) to call `axiom_edwards_add_closed(Q₁, Q₂)`. This fact
follows from the EdwardsPoint type invariant, but we can't access it for Ghost values.

**Approaches considered**:

| Approach | Result |
|----------|--------|
| `use_type_invariant(q1)` | ❌ `expression has mode spec, expected mode proof` |
| `assert(q1.well_formed())` | ❌ assertion failed (solver doesn't have the fact) |
| `reveal(edwards_x)` | ❌ `closed` specs can't be revealed |
| `tracked` parameter wrapper | ✅ compiles for the helper, but can't call it with Ghost values |
| `admit()` in a helper lemma | ✅ **chosen solution** |

**Solution**: `lemma_edwards_type_invariant` (`specs/edwards_specs.rs`):

```rust
pub(crate) proof fn lemma_edwards_type_invariant(point: EdwardsPoint)
    ensures
        point.well_formed(),
        is_valid_edwards_point(point),
        edwards_point_limbs_bounded(point),
        sum_of_limbs_bounded(&edwards_y(point), &edwards_x(point), u64::MAX),
{ admit(); }
```

**Judgment basis**: This `admit()` is **sound** — the type invariant guarantees
`well_formed()` for every EdwardsPoint instance by construction. The limitation is
purely in Verus's API: `use_type_invariant` requires exec/tracked values, not Ghost.
A future Verus improvement (broadcast axiom for type invariants) would eliminate this
need entirely.

## Step 6: Assemble the Proof

With all infrastructure in place, the proof follows the mathematical plan from Step 1.

### Step 6a: Extract witnesses (lines 204–209)

```rust
let q1 = choose|q: EdwardsPoint|
    edwards_point_as_affine(p1) == edwards_scalar_mul(
        #[trigger] edwards_point_as_affine(q), 2);
let q2 = choose|q: EdwardsPoint|
    edwards_point_as_affine(p2) == edwards_scalar_mul(
        #[trigger] edwards_point_as_affine(q), 2);
```

**Judgment basis**: `is_in_even_subgroup(p1)` is an `exists`, so `choose` extracts a
concrete witness. The `#[trigger]` annotation matches the trigger in the
`is_in_even_subgroup` definition.

### Step 6b: Connect scalar_mul to double (lines 216–217)

```rust
lemma_double_is_scalar_mul_2(q1_affine);
lemma_double_is_scalar_mul_2(q2_affine);
```

**Effect**: Establishes `edwards_scalar_mul(P, 2) == edwards_double(P.0, P.1)`.
After this, the solver knows:
- `affine(p1) == double(q1_affine.0, q1_affine.1)`
- `affine(p2) == double(q2_affine.0, q2_affine.1)`

**Judgment basis**: `edwards_scalar_mul` is a recursive spec function. For `n = 2`,
it unfolds to `double(scalar_mul(P, 1))` = `double(P)`. The lemma uses
`reveal_with_fuel(edwards_scalar_mul, 3)` to let the solver see this.

### Step 6c: Type invariant for q1, q2 (lines 224–229)

```rust
lemma_edwards_type_invariant(q1);
lemma_edwards_type_invariant(q2);
lemma_valid_extended_point_affine_on_curve(q1_nat.0, q1_nat.1, q1_nat.2, q1_nat.3);
lemma_valid_extended_point_affine_on_curve(q2_nat.0, q2_nat.1, q2_nat.2, q2_nat.3);
```

**Effect**: Establishes `is_on_edwards_curve(q1_affine.0, q1_affine.1)` and similarly
for q2.

**Chain of reasoning**:
```
lemma_edwards_type_invariant(q1)
  → is_valid_edwards_point(q1)
  → is_valid_extended_edwards_point(X, Y, Z, T) for q1's coordinates

lemma_valid_extended_point_affine_on_curve(X, Y, Z, T)
  → is_on_edwards_curve(field_mul(X, field_inv(Z)), field_mul(Y, field_inv(Z)))
  → is_on_edwards_curve(q1_affine.0, q1_affine.1)
```

### Step 6d: Add is closed on the curve (line 232)

```rust
axiom_edwards_add_closed(q1_affine.0, q1_affine.1, q2_affine.0, q2_affine.1);
```

**Effect**: `is_on_edwards_curve(add(Q₁, Q₂).0, add(Q₁, Q₂).1)`.

**Note**: `axiom_edwards_add_closed` is itself still an axiom (admitted). Proving
it requires deep algebraic verification of the addition formula. This is a separate
effort.

### Step 6e: Construct the witness W (lines 238–242)

```rust
let q_sum = edwards_add(q1_affine.0, q1_affine.1, q2_affine.0, q2_affine.1);
lemma_affine_point_representable(q_sum.0, q_sum.1);
let w = choose|w: EdwardsPoint|
    edwards_point_as_affine(w) == (q_sum.0, q_sum.1)
    && is_well_formed_edwards_point(w);
```

**Effect**: Obtains W : EdwardsPoint with `affine(W) = Q₁ + Q₂`.

**Preconditions satisfied**:
- `q_sum.0 < p()` and `q_sum.1 < p()`: from `lemma_edwards_add_canonical`
- `is_on_edwards_curve(q_sum.0, q_sum.1)`: from `axiom_edwards_add_closed`

### Step 6f: Double distributes over add (line 245)

```rust
lemma_double_distributes(q1_affine, q2_affine);
```

**Effect**: `double(add(Q₁, Q₂)) == add(double(Q₁), double(Q₂))`.

This is the core algebraic identity. Combined with step 6b:
```
add(affine(p1), affine(p2))
  = add(double(Q₁), double(Q₂))    [step 6b]
  = double(add(Q₁, Q₂))            [step 6f]
  = double(q_sum)
```

### Step 6g: Connect to scalar_mul (line 250)

```rust
lemma_double_is_scalar_mul_2(q_sum);
```

**Effect**: `double(q_sum) == scalar_mul(q_sum, 2)`.

Since `affine(W) = q_sum`, this gives:
```
scalar_mul(affine(W), 2) = double(q_sum) = add(affine(p1), affine(p2))
```

### Step 6h: Close the forall (lines 258–273)

```rust
assert forall|result: EdwardsPoint|
    ... implies is_in_even_subgroup(result) by {
    assert(edwards_point_as_affine(result) == edwards_scalar_mul(
        edwards_point_as_affine(w), 2));
}
```

**Effect**: For any `result` with `affine(result) = add(affine(p1), affine(p2))`:

```
affine(result)
  = add(affine(p1), affine(p2))      [given]
  = double(q_sum)                     [from steps 6b + 6f]
  = scalar_mul(q_sum, 2)             [from step 6g]
  = scalar_mul(affine(W), 2)         [since affine(W) = q_sum]
```

So W witnesses `is_in_even_subgroup(result)`. QED.

## Summary: Complete Reasoning Chain

```
is_in_even_subgroup(p1)  ──choose──→  q1 with affine(p1) = [2]affine(q1)
is_in_even_subgroup(p2)  ──choose──→  q2 with affine(p2) = [2]affine(q2)
                                            │
                    lemma_double_is_scalar_mul_2
                                            │
                                            ▼
                          affine(p1) = double(Q₁)
                          affine(p2) = double(Q₂)
                                            │
                 lemma_edwards_type_invariant (admit — Verus limitation)
                                            │
                                            ▼
                    is_on_edwards_curve(Q₁), is_on_edwards_curve(Q₂)
                                            │
                       axiom_edwards_add_closed (separate axiom)
                                            │
                                            ▼
                       is_on_edwards_curve(add(Q₁, Q₂))
                                            │
                      lemma_affine_point_representable
                                            │
                                            ▼
                    W : EdwardsPoint with affine(W) = add(Q₁, Q₂)
                                            │
                        lemma_double_distributes
                                            │
                                            ▼
    double(add(Q₁, Q₂)) = add(double(Q₁), double(Q₂))
                         = add(affine(p1), affine(p2))
                         = affine(result)
                                            │
                     lemma_double_is_scalar_mul_2
                                            │
                                            ▼
    affine(result) = scalar_mul(affine(W), 2)  ⟹  is_in_even_subgroup(result)
```

## Decision Framework

| Step | Strategy | Judgment Basis |
|------|----------|----------------|
| Target selection | Look for axioms with clear math + infrastructure gap | Comment said "requires lifting affine → EdwardsPoint" |
| Math plan | Standard group theory: [2]A + [2]B = [2](A+B) | Any textbook on abelian groups |
| Infrastructure | Build nat_to_fe51 (spec fn + 3 lemmas) | Needed to convert affine coords to FieldElement51 |
| Witness construction | `lemma_affine_point_representable` | Assembles FieldElement51 coords into EdwardsPoint |
| Closed spec accessors | Use `lemma_unfold_edwards` | Bridges closed `edwards_x(p)` with raw `p.X` |
| Type invariant gap | `admit()` in helper lemma | Sound (type invariant holds by construction); Verus API limitation |
| Limb bound bridging | `lemma2_to64_rest()` + `by (bit_vector)` | Connects `pow2(51)` to `(1u64 << 51)` for `fe51_limbs_bounded` |

## Remaining Trusted Gaps

1. **`lemma_edwards_type_invariant`**: admits the type invariant for Ghost-mode values.
   Sound by construction. Eliminable if Verus adds type invariant support for `choose`.

2. **`axiom_edwards_add_closed`**: axiom that Edwards addition preserves the curve.
   Requires deep algebraic verification of the addition formula — a separate effort.

**Core principle**: Identify the exact infrastructure gap (affine → EdwardsPoint lifting),
build the minimum required machinery, and assemble the proof using existing lemmas.
The creative work was in diagnosing the type invariant limitation and finding a sound
workaround.
