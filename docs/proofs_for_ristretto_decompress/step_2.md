# Proof of `decompress::step_2` Correctness

This document proves the correctness of the Ristretto decode formula and its
algebraic properties.

## Definitions

**Field.** p = 2^255 − 19. All arithmetic is in GF(p).

**Curve parameter.** d = −121665/121666 mod p (the Ed25519 twist parameter).

**Ristretto decode formula.** Given a canonical nonnegative field element s:

    s²    = s · s
    u1    = 1 − s²
    u2    = 1 + s²
    u2²   = u2 · u2
    u1²   = u1 · u1
    v     = −d · u1² − u2²
    (ok, I) = invsqrt(v · u2²)
    Dx    = I · u2
    Dy    = I · Dx · v
    x_tmp = 2s · Dx
    x     = |x_tmp|           (conditional negate to make nonnegative)
    y     = u1 · Dy
    t     = x · y

where `invsqrt(a)` returns `(ok, I)` such that I is the nonnegative value with
either I²·a ≡ 1 (mod p) (the "square" case, ok = true) or I²·a ≡ √(−1) (mod p)
(the "nonsquare" case, ok = false). When a = 0, it returns (false, 0).

**`is_sqrt_ratio(u, v, r)`**: r²·v ≡ u (mod p).

**`is_sqrt_ratio_times_i(u, v, r)`**: r²·v ≡ √(−1)·u (mod p).

**`spec_ristretto_decode_ok(s)`**: Whether the invsqrt succeeded (square case).

**`spec_ristretto_decode_x(s)`, `spec_ristretto_decode_y(s)`**: The decoded coordinates.

**`is_on_edwards_curve(x, y)`**: −x² + y² ≡ 1 + d·x²·y² (mod p).

**`is_in_even_subgroup(P)`**: ∃Q on the curve such that P = [2]Q.

**References:**
- Hamburg (2015), "Decaf: Eliminating cofactors through point compression" <https://eprint.iacr.org/2015/673>
- <https://ristretto.group/formulas/decoding.html>

## Theorem 1 (Curve Membership)

**Statement.** If `s < p` and `spec_ristretto_decode_ok(s)`, then
`is_on_edwards_curve(spec_ristretto_decode_x(s), spec_ristretto_decode_y(s))`.

**Proof sketch.** Substitute the decode formulas into the curve equation.

Since the invsqrt satisfies I²·v·u2² ∈ {1, √(−1)} (mod p), we can express
Dx² and Dy² in terms of u1, u2, v. The conditional negate to compute x does
not affect x², so the curve equation depends only on:

    x² = (2s·Dx)² = 4s²·Dx²  = 4s²·I²·u2²
    y  = u1·Dy    = u1·I²·Dx·v = u1·I²·u2·v

Working through the algebra (expanding and collecting terms using
u1 = 1 − s², u2 = 1 + s², v = −d·u1² − u2²):

    −x² + y² = −4s²·I²·u2² + u1²·I²·u2²·v² · ... 

The full algebraic verification is a lengthy but straightforward computation
in GF(p). It is validated by the runtime test `test_ristretto_decode_on_curve`
which checks 100 points (identity, basepoint, and 98 multiples).

**Status:** AXIOM (`axiom_ristretto_decode_on_curve`). The algebraic identity
is well-established in Hamburg (2015) but not yet mechanized in Verus.

∎

## Theorem 2 (Mutual Exclusivity of sqrt cases)

**Statement.** For u, v, r ∈ GF(p) with u ≢ 0 (mod p):

    ¬(is_sqrt_ratio(u, v, r) ∧ is_sqrt_ratio_times_i(u, v, r))

That is, r²·v ≡ u and r²·v ≡ i·u cannot both hold (where i = √(−1)).

**Proof.**

Suppose both hold. Then:
- r²·v ≡ u (mod p)
- r²·v ≡ i·u (mod p)

So u ≡ i·u (mod p), which gives (i − 1)·u ≡ 0 (mod p).

Since p is prime and u ≢ 0 (mod p), we must have i ≡ 1 (mod p).

But i² ≡ −1 (mod p) (by definition of √(−1)), so 1² = 1 ≡ −1 (mod p),
giving p | 2. Since p = 2^255 − 19 > 2, this is a contradiction.

**Alternative proof via existing lemma.** Consider two cases:
- If v ≡ 0 (mod p): then r²·v ≡ 0 ≡ u (mod p) contradicts u ≢ 0.
  So `is_sqrt_ratio` is false, and the conjunction is false.
- If v ≢ 0 (mod p): If `is_sqrt_ratio_times_i(u, v, r)` holds, then
  r is a witness for the existential in `lemma_no_square_root_when_times_i`,
  which proves r²·v ≢ u (mod p) and r²·v ≢ −u (mod p). The first
  conclusion is ¬is_sqrt_ratio(u, v, r).

**Status:** PROVEN. `lemma_sqrt_ratio_mutual_exclusion` in `sqrt_ratio_lemmas.rs`
is fully mechanized using `lemma_no_square_root_when_times_i` (also fully proven).
No admits remain.

∎

## Theorem 3 (Invsqrt Uniqueness)

**Statement.** For a ≢ 0 (mod p), there is exactly one r with r < p, r even
(i.e., ¬is_negative(r)), and either is_sqrt_ratio(1, a, r) or
is_sqrt_ratio_times_i(1, a, r).

**Proof.**

**Existence.** Since GF(p)* is cyclic of order p − 1, and p ≡ 5 (mod 8), we have
4 | (p − 1). The element a has a well-defined "fourth-root-of-unity type": the
value w = u·v^7·(u·v^7)^((p−5)/8) satisfies w^((p−1)/4) ∈ {1, −1, i, −i}.
The `sqrt_ratio_i` algorithm constructs r from this, always producing a valid root.

**Uniqueness.** Suppose r₁ and r₂ both satisfy the conditions. By Theorem 2,
each rₖ satisfies exactly one of the two cases (sqrt_ratio or sqrt_ratio_times_i),
and they must satisfy the same case (otherwise one gives r₁²·a ≡ 1 and the other
r₂²·a ≡ i, which leads to (r₁/r₂)² ≡ 1/i, impossible since 1/i = −i is not a square).

So r₁²·a ≡ r₂²·a (mod p), giving r₁² ≡ r₂² (mod p) (since a ≢ 0), so
(r₁ − r₂)(r₁ + r₂) ≡ 0 (mod p). Since p is prime, either r₁ ≡ r₂ or r₁ ≡ −r₂ (mod p).

If r₁ ≡ −r₂ (mod p) with r₁ ≠ r₂, then one of {r₁, r₂} is even and the other
is odd (since r and p − r have opposite parity for odd p). But both are required
to be even (nonnegative), contradiction.

Therefore r₁ = r₂.

Uniqueness is fully mechanized (`lemma_invsqrt_unique`) via
`lemma_no_square_root_when_times_i` (mixed cases) and `lemma_nonneg_square_root_unique`
(same cases). The relation property is also fully proven (`lemma_nat_invsqrt_satisfies_relation`).

∎

## Theorem 4 (Even Subgroup Membership)

**Statement.** When `invsqrt` succeeds with `ok = true` (the square case:
I²·v·u2² ≡ 1 (mod p)), the decoded point (x, y) lies in the even subgroup
2E = {[2]Q : Q ∈ E(GF(p))}.

**Proof sketch.** This is the core theorem of the Ristretto/Decaf construction.

The proof relies on the Jacobi quartic isogeny. Ed25519 has cofactor h = 8,
and its group E(GF(p)) ≅ ℤ/8 × ℤ/ℓ where ℓ is a large prime. The even
subgroup 2E has index 2 in E and equals the prime-order subgroup ℤ/ℓ union
the 4-torsion subgroup.

The Ristretto construction maps the Jacobi quartic J to E via a 2-isogeny φ.
Points decoded by the Ristretto formula are in the image of φ, which is exactly 2E.

More precisely:
- The decode formula computes a point on J from the field element s
- The map φ: J → E sends this to an Edwards point
- Image(φ) = 2E (standard property of 2-isogenies on curves with cofactor 8)

When `ok = true`, the `is_sqrt_ratio` condition ensures the point is in the
principal branch of the decoding (the actual square root, not the nonsquare case),
which corresponds to a valid point on J.

**Status:** AXIOM (`axiom_ristretto_decode_in_even_subgroup`). Validated by
runtime test checking [L]P = identity for 50 decoded points.

**References:**
- Hamburg (2015), Section 3: "The isogeny φ maps the Jacobi quartic to the
  twisted Edwards curve, and its image is exactly 2E."
- <https://ristretto.group/details/isogenies.html>

∎

## Theorem 5 (Failure Correctness)

**Statement.** The three checks `!ok || is_negative(t) || y == 0` correctly
reject all byte strings that are not valid Ristretto encodings.

**Proof.**

A valid Ristretto encoding requires (after the step_1 checks pass):
1. The decode succeeds: `ok = true` (v·u2² has a square root, not just i times one)
2. The T coordinate is nonnegative: `¬is_negative(t)` where t = x·y
3. The Y coordinate is nonzero: `y ≠ 0`

These correspond exactly to the conditions in the Ristretto specification
([RISTRETTO], §5.2):

- **ok check**: Rejects encodings where v·u2² is not a quadratic residue
  (only an i-times-residue). These correspond to points not in the Ristretto
  group (they would lie in a different coset).

- **t negativity check**: The Ristretto encoding is canonical only when t is
  nonnegative. A negative t indicates the encoding represents the same point
  as a different (canonical) encoding, so it must be rejected to ensure
  uniqueness.

- **y = 0 check**: When y = 0, the point is a low-order torsion point
  (either the identity or a 2-torsion point). The Ristretto spec explicitly
  rejects y = 0 to exclude certain degenerate encodings.

The function returns `None` when any check fails, matching the spec's behavior
of returning `None` when `!ok_spec || is_negative(t) || y == 0`.

**Status:** PROVEN. The correspondence between exec checks and spec conditions
is established by step_2's postconditions connecting each `Choice` flag to its
spec-level predicate.

∎

## Theorem 6 (Spec Alignment)

**Statement.** The exec-level intermediate values match `spec_ristretto_decode_inner(s)`.

**Proof.** Each field operation in step_2 (square, add, sub, mul, neg, invsqrt)
has a postcondition connecting `fe51_as_canonical_nat` of its result to the
corresponding spec-level field operation. The proof establishes a chain of equalities:

    fe51_as_canonical_nat(ss)  == field_square(s_nat)
    fe51_as_canonical_nat(u1)  == field_sub(1, field_square(s_nat))
    fe51_as_canonical_nat(u2)  == field_add(1, field_square(s_nat))
    ...
    fe51_as_canonical_nat(x)   == spec_ristretto_decode_x(s_nat)
    fe51_as_canonical_nat(y)   == spec_ristretto_decode_y(s_nat)
    choice_is_true(ok)         == spec_ristretto_decode_ok(s_nat)

For `square` operations, the bridge `lemma_square_matches_field_square` connects
the exec `pow(raw, 2)` postcondition to the spec `field_square(canonical)`.

For the `invsqrt` result, `lemma_decode_invsqrt_facts` (which calls
`lemma_invsqrt_matches_spec` → `lemma_invsqrt_unique` and
`lemma_sqrt_ratio_mutual_exclusion`) bridges the exec I to `nat_invsqrt(v_u2_sqr)`
and establishes mutual exclusivity in a single helper call.

**Status:** PROVEN (using `lemma_invsqrt_unique` via `lemma_decode_invsqrt_facts`).

∎

## step_2 Postcondition Summary

| Postcondition | Proved via |
|---------------|------------|
| Z = 1 | By construction (FieldElement::ONE) |
| T = X·Y | By construction (mul postcondition) |
| ok ⟹ is_well_formed_edwards_point | axiom_ristretto_decode_on_curve(s) + type invariant |
| ok ⟹ is_in_even_subgroup | axiom_ristretto_decode_in_even_subgroup(s, point) |
| t_is_negative matches is_negative(T) | lemma_is_negative_equals_parity |
| y_is_zero matches (Y == 0) | lemma_is_zero_iff_canonical_nat_zero |
| ok matches spec_ristretto_decode_ok | lemma_decode_invsqrt_facts (lemma_invsqrt_unique + mutual exclusivity) |
| X matches spec_ristretto_decode_x | Field operation postconditions chain |
| Y matches spec_ristretto_decode_y | Field operation postconditions chain |

## Degenerate Case (v·u2² = 0)

When `v·u2² ≡ 0 (mod p)`, `invsqrt` returns `(false, 0)`. This means:
- I = 0, so Dx = 0, Dy = 0, x = 0, y = 0

The point (0, 0, 1) does NOT satisfy the Edwards curve equation (substituting
gives 0 = 1, which is false).

**Resolution (implemented):** The code uses `EdwardsPoint::identity()` on the
`!ok` path instead of constructing an invalid `EdwardsPoint { X: x, Y: y, Z: one, T: t }`:

```rust
let point = if choice_into(ok) {
    EdwardsPoint { X: x, Y: y, Z: one, T: t }
} else {
    EdwardsPoint::identity()
};
```

Since `ok = false` on this path, the identity point is immediately discarded
by the caller (decompress returns `None`). The identity (0, 1, 1, 0) is a
valid on-curve point, so no unsound assume is needed for the type invariant.
