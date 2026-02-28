# Proof of `decompress` Correctness

This document proves the top-level correctness of `CompressedRistretto::decompress`.
It delegates to [step_1.md](step_1.md) and [step_2.md](step_2.md) for sub-proofs.

## Definitions

**Field.** Let p = 2^255 − 19. All arithmetic below is in GF(p) unless stated otherwise.

**Edwards curve.** Ed25519 is the twisted Edwards curve
−x² + y² = 1 + d·x²·y²
where d = −121665/121666 mod p.

**Extended coordinates.** A point is represented as (X : Y : Z : T) with Z ≠ 0,
x = X/Z, y = Y/Z, and T = X·Y/Z (the Segre invariant Z·T = X·Y).

**Ristretto encoding.** A 32-byte string encodes a Ristretto point via a field
element s ∈ GF(p). The encoding is valid when:
1. The bytes are canonical: interpreting them as a little-endian integer gives s < p.
2. s is nonnegative: s mod 2 = 0 (the canonical representative has even parity).
3. The Ristretto decode formula (see [step_2.md](step_2.md)) succeeds.

**References:**
- Hamburg (2015), "Decaf: Eliminating cofactors through point compression" <https://eprint.iacr.org/2015/673>
- Hamburg (2019), "Ristretto" <https://eprint.iacr.org/2020/1400>
- <https://ristretto.group/formulas/decoding.html>

## Spec Functions

The spec function `spec_ristretto_decompress(bytes) → Option<(nat,nat,nat,nat)>`
models decompression, returning raw (x, y, 1, t) coordinates or `None` on failure.
It delegates coordinate computation to `spec_ristretto_decode_inner(s)`, which is
factored into `spec_ristretto_decode_v_u2_sqr(s)` (the invsqrt input) and
`spec_ristretto_decode_xy(s, big_i)` (coordinate computation given the invsqrt result).

## Theorem (Decompress Correctness)

**Statement.** `decompress(self) → result` satisfies:

1. `result.is_none() ⟺ spec_ristretto_decompress(self.0).is_none()`
2. `result.is_some() ⟹ spec_edwards_point(result.unwrap().0) == spec_ristretto_decompress(self.0).unwrap()`
3. `result.is_some() ⟹ is_well_formed_edwards_point(result.unwrap().0)`
4. `result.is_some() ⟹ is_in_even_subgroup(result.unwrap().0)`

## Proof

The function proceeds in two stages.

### Stage 1: Validation (step_1)

Call `step_1(self)` which returns `(s_encoding_is_canonical, s_is_negative, s)`.

By [Theorem (Canonical Round-trip)](step_1.md) and [Theorem (Sign Check)](step_1.md):
- `s_encoding_is_canonical` is true iff `as_bytes(s) == self.0` iff `u8_32_as_nat(self.0) < p`.
- `s_is_negative` is true iff `is_negative(field_element_from_bytes(self.0))`.
- `fe51_as_canonical_nat(s) == field_element_from_bytes(self.0)`.

**Early rejection.** If `!s_encoding_is_canonical || s_is_negative`, the spec says
`spec_ristretto_decompress(self.0) == None`.
The function returns `None`, satisfying all 4 postconditions trivially.

### Stage 2: Decode (step_2)

When validation passes, we have:
- `u8_32_as_nat(self.0) < p` (canonical)
- `!is_negative(s_nat)` where `s_nat = fe51_as_canonical_nat(s) = field_element_from_bytes(self.0)`

Call `step_2(s)` which returns `(ok, t_is_negative, y_is_zero, res)`.

By [step_2 postconditions](step_2.md):
- `ok ⟺ spec_ristretto_decode_ok(s_nat)`
- Coordinates of `res` match `spec_ristretto_decode_x(s_nat)`, `spec_ristretto_decode_y(s_nat)`
- `t_is_negative == is_negative(t)` and `y_is_zero == (y == 0)` where t = x·y
- `ok ⟹ is_well_formed_edwards_point(res.0)` and `ok ⟹ is_in_even_subgroup(res.0)`

### Failure branch

If `!ok || t_is_negative || y_is_zero`, the spec's inner condition
`!ok_spec || is_negative(t) || y == 0` holds, so the spec returns `None`.
The function returns `None`, satisfying postconditions 1–4.

### Success branch

If `ok && !t_is_negative && !y_is_zero`:
- `ok_spec && !is_negative(t) && y != 0` holds
- The function returns `Some(res)`

**Postconditions 1–2** (coordinate-level): The exec coordinates match the spec
coordinates from `spec_ristretto_decompress`, which returns
`Some((x, y, 1, t))`. Since `res` has these coordinates by step_2's postconditions,
postconditions 1–2 follow directly.

**Postcondition 3** (well-formed): From step_2, `ok ⟹ is_well_formed_edwards_point(res.0)`.

**Postcondition 4** (even subgroup): From step_2, `ok ⟹ is_in_even_subgroup(res.0)`.

## Axiom Dependencies

| Axiom | Used for | Justified by |
|-------|----------|--------------|
| `axiom_ristretto_decode_on_curve(s)` | Postcondition 3 (via step_2) | Hamburg 2015; tested on 100 points |
| `axiom_ristretto_decode_in_even_subgroup(s, point)` | Postcondition 4 (via step_2) | Hamburg 2015/2019; tested on 50 points |
| `lemma_invsqrt_unique` | Spec alignment (via step_2) | Fully proven; GF(p) sign structure; tested on 190+ elements |
| `axiom_sqrt_m1_squared` | Mutual exclusivity (transitive) | p ≡ 5 (mod 8) |

Both decode axioms take only `s: nat` (and `point` for the subgroup axiom) as parameters,
using `spec_ristretto_decode_ok(s)` as precondition and `spec_ristretto_decode_x/y(s)`
in their ensures clauses.
