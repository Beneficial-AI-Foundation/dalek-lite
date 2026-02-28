# Verus Proof Mapping for `ristretto::decompress`

This document maps each theorem from the mathematical proofs
([decompress.md](decompress.md), [step_1.md](step_1.md), [step_2.md](step_2.md))
to the corresponding Verus code, identifying all gaps.

## Legend

| Status | Meaning |
|--------|---------|
| PROVEN | Fully mechanized in Verus, no admits/assumes |
| AXIOM (admit) | Uses `admit()`, named with `axiom_` prefix |
| AXIOM (assume) | Uses `assume(...)`, named with `axiom_` prefix |

---

## decompress.md -- Top-level Orchestration

| Math Statement | Verus Location | Status | Test | Notes |
|---|---|---|---|---|
| Decompress correctness (all 4 postconditions) | `ristretto.rs` `CompressedRistretto::decompress` | PROVEN (modulo axioms below) | — | Top-level function verified |
| Postconditions 1-2: coordinate-level spec alignment | `ristretto.rs` decompress proof blocks | PROVEN | — | Direct from step_2 postconditions |
| Postcondition 3: well-formed Edwards point | `ristretto.rs` decompress ensures | PROVEN (via step_2 + axiom) | — | Depends on `axiom_ristretto_decode_on_curve` |
| Postcondition 4: even subgroup | `ristretto.rs` decompress ensures | PROVEN (via step_2 + axiom) | — | Depends on `axiom_ristretto_decode_in_even_subgroup` |
| Early rejection (non-canonical or negative) | `ristretto.rs` decompress early return | PROVEN | — | Uses `lemma_canonical_check_backward` |

---

## step_1.md -- Canonical Encoding and Sign Check

| Math Statement | Verus Location | Status | Test | Notes |
|---|---|---|---|---|
| Theorem (Canonical Round-trip) | `ristretto.rs` step_1 proof block | PROVEN | — | Uses `lemma_as_bytes_equals_spec_fe51_to_bytes`, `lemma_seq_eq_implies_array_eq` |
| Theorem (Sign Check) | `ristretto.rs` step_1 proof block | PROVEN | — | Uses `lemma_is_negative_equals_parity` |
| step_1 postcondition 1: 51-bit limbs | `from_bytes` postcondition | PROVEN | — | — |
| step_1 postcondition 2: value = field_element_from_bytes | `ristretto.rs` step_1 proof block | PROVEN | — | Modular arithmetic chain |
| step_1 postcondition 3: canonical iff round-trips | `ristretto.rs` step_1 proof block | PROVEN | — | Bidirectional via lemma |
| step_1 postcondition 4: sign matches spec | `ristretto.rs` step_1 proof block | PROVEN | — | — |
| step_1 postcondition 5: canonical implies < p | `ristretto.rs` step_1 proof block | PROVEN | — | — |

**All step_1 proofs are fully mechanized. No axioms needed.**

---

## step_2.md -- Decode Formula and Algebraic Properties

| Math Statement | Verus Location | Status | Test | Notes |
|---|---|---|---|---|
| Theorem 1 (Curve Membership) | `ristretto_specs.rs` `axiom_ristretto_decode_on_curve(s)` | AXIOM (admit) | `test_ristretto_decode_on_curve` (100 points) | Hamburg 2015; requires `spec_ristretto_decode_ok(s)` |
| Theorem 2 (Mutual Exclusivity) | `sqrt_ratio_lemmas.rs` `lemma_sqrt_ratio_mutual_exclusion` | PROVEN | — | Uses `lemma_no_square_root_when_times_i` (also fully proven) |
| Theorem 3 (Invsqrt Uniqueness) | `sqrt_ratio_lemmas.rs` `lemma_invsqrt_unique` | PROVEN | — | Uses lemma_no_square_root_when_times_i + lemma_nonneg_square_root_unique + lemma_nat_invsqrt_satisfies_relation |
| Theorem 4 (Even Subgroup) | `ristretto_specs.rs` `axiom_ristretto_decode_in_even_subgroup(s, point)` | AXIOM (admit) | `test_ristretto_decode_in_even_subgroup` (50+ points, diverse inputs) | Hamburg 2015/2019; Jacobi quartic isogeny |
| Theorem 5 (Failure Correctness) | `ristretto.rs` step_2 proof blocks | PROVEN | — | Direct from step_2 postconditions |
| Theorem 6 (Spec Alignment) | `ristretto.rs` step_2 proof blocks | PROVEN | — | Uses lemma_invsqrt_unique, mutual exclusion |

### step_2 Lemma Chain

| Lemma | File | Status | Used by |
|---|---|---|---|
| `lemma_decode_invsqrt_facts` | `ristretto.rs` | PROVEN (calls lemma_invsqrt_matches_spec + mutual exclusion) | step_2 spec alignment |
| `lemma_invsqrt_matches_spec` | `ristretto.rs` | PROVEN (calls lemma_invsqrt_unique) | invsqrt bridging |
| `lemma_sqrt_ratio_mutual_exclusion` | `sqrt_ratio_lemmas.rs` | PROVEN | step_2 ok↔is_sqrt_ratio |
| `lemma_is_negative_equals_parity` | `as_bytes_lemmas.rs` | PROVEN | step_2 t_is_negative |
| `lemma_is_zero_iff_canonical_nat_zero` | `batch_invert_lemmas.rs` | PROVEN | step_2 y_is_zero |
| `lemma_square_matches_field_square` | `field_algebra_lemmas.rs` | PROVEN | step_2 square bridging |
| `lemma_one_field_element_value` | `constants_lemmas.rs` | PROVEN | step_2 ONE = 1 |
| `lemma_z_one_affine_implies_projective` | `curve_equation_lemmas.rs` | PROVEN | step_2 Z=1 bridge |
| `lemma_field_mul_one_left` | `field_algebra_lemmas.rs` | PROVEN | step_2 Segre relation |

---

## Transitive Axiom Dependencies

| Axiom | File | Status | Test | Used by (in decompress chain) |
|---|---|---|---|---|
| `lemma_sqrt_m1_limbs_bounded` | `sqrt_m1_lemmas.rs` | **PROVEN** (concrete limb checks) | `test_sqrt_m1_limbs_bounded` | sqrt_ratio_i |
| `axiom_sqrt_m1_squared` | `sqrt_m1_lemmas.rs` | AXIOM (admit) | `test_sqrt_m1_limbs_bounded` (sanity) | mutual exclusion, sqrt_ratio_correctness |
| `axiom_sqrt_m1_not_square` | `sqrt_m1_lemmas.rs` | AXIOM (admit) | `test_sqrt_m1_not_square` (Euler's criterion) | lemma_no_square_root_when_times_i |
| `axiom_neg_sqrt_m1_not_square` | `sqrt_m1_lemmas.rs` | AXIOM (admit) | `test_sqrt_m1_not_square` (Euler's criterion) | lemma_no_square_root_when_times_i |
| `axiom_minus_one_field_element_value` | `constants_lemmas.rs` | AXIOM (admit) | `test_minus_one_field_element_value` | field algebra |
| `axiom_p_is_prime` | `primality_specs.rs` | AXIOM (admit) | `test_p_is_prime` (Miller-Rabin, 9 witnesses + Fermat) | field algebra, sqrt_ratio proofs |

---

## Other Assumes in Decompress Scope

| Location | Type | Impact | Resolution |
|---|---|---|---|
| `ristretto.rs` `from_slice` | `assume(...)` bytes tracking through `.map()` | Not in decompress path | Verus limitation; document |
| `ristretto_specs.rs` `axiom_spec_ristretto_roundtrip` | `assume(...)` x2 | Not used by decompress | **Removed** (along with `spec_ristretto_decompress`) |

---

## Removed Axioms / Specs

| Item | Reason | Date |
|---|---|---|
| `axiom_ristretto_point_from_coords` | Unsound: `spec_edwards_point` maps through `fe51_as_canonical_nat` which is not injective on limb representations. Coordinate-level postconditions (via `spec_ristretto_decompress`) provide all security guarantees. | 2026-02-25 |
| `spec_ristretto_decompress` | Removed: used `choose\|p: RistrettoPoint\|` which is fragile; not used by decompress proof. Only `spec_ristretto_decompress` is needed. | 2026-02-26 |
| `axiom_spec_ristretto_roundtrip` | Removed: only consumer of `spec_ristretto_decompress`. | 2026-02-26 |
| `is_ristretto_decode_output` | Removed: redundant predicate that duplicated `spec_ristretto_decode_inner`. Axioms simplified to use `spec_ristretto_decode_ok/x/y` directly. | 2026-02-26 |

---

## Remaining Action Items

1. ~~**ADD TEST** for `axiom_sqrt_m1_not_square` and `axiom_neg_sqrt_m1_not_square`~~ DONE: `test_sqrt_m1_not_square` (Euler's criterion)
2. ~~**ADD TEST** for `axiom_minus_one_field_element_value`~~ Already existed: `test_minus_one_field_element_value`
3. ~~**TRY PROVING** `axiom_sqrt_m1_limbs_bounded` via concrete computation~~ DONE: Renamed to `lemma_sqrt_m1_limbs_bounded`, proven via concrete limb value assertions + bit_vector
4. **TRY PROVING** `axiom_sqrt_m1_squared` via concrete computation — NOT FEASIBLE: requires 252-bit multiplication beyond SMT solver capacity. Runtime test validates.
5. ~~**EXPAND** `test_ristretto_decode_on_curve` with edge cases~~ DONE: small even s values, s=1, 50 hash-derived inputs
6. **STRENGTHEN** `test_ristretto_decode_in_even_subgroup` with more diverse inputs
7. ~~**NARROW** `axiom_ristretto_decode_on_curve` precondition~~ DONE: Axiom simplified to `axiom_ristretto_decode_on_curve(s)` with `spec_ristretto_decode_ok(s)` precondition.
8. ~~**SIMPLIFY** axiom interfaces~~ DONE: Removed `is_ristretto_decode_output` predicate. Both decode axioms now use `spec_ristretto_decode_*` helpers directly. Extracted `lemma_decode_invsqrt_facts` to deduplicate proof.
