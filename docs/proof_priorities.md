# Proof Priorities

This document records a recommended priority order for the remaining unproved items in the Verus verification of `dalek-lite`.

The goal is not just to count down `admit()` calls, but to reduce the trusted base as quickly as possible while preserving a practical path for contributors.

## How To Read This

Priority is based on two factors:

- Trust impact: how much the item affects the overall soundness story
- Proof leverage: how many downstream proofs or modules depend on it

As a rule of thumb:

- `P0` means "high-value foundation work"
- `P1` means "important next-wave proof work"
- `P2` means "useful, but lower leverage or more isolated"

## Current Snapshot

As of the latest certification entry, the repository reports 502 verified functions out of 580 total.

The remaining trusted gaps cluster into four groups:

1. Edwards group law and scalar-multiplication algebra
2. Montgomery and Edwards/Montgomery bridge facts
3. Ristretto and Elligator correctness facts
4. Trusted modeling assumptions for constants, hashing, and probability

## Recommended Order

## P0: Highest-Leverage Foundational Algebra

These are the most important proof obligations to reduce the mathematical trusted base for core group operations.

### 1. Edwards group law

Files:

- [curve_equation_lemmas.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lemmas/edwards_lemmas/curve_equation_lemmas.rs#L770)
- [curve_equation_lemmas.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lemmas/edwards_lemmas/curve_equation_lemmas.rs#L2858)

Items:

- `axiom_edwards_add_associative`
- `axiom_edwards_add_complete`

Why first:

- These are central group-law assumptions for Edwards arithmetic.
- Many higher-level scalar multiplication proofs rely on them directly.
- Reducing trust here improves the soundness story for `edwards`, `straus`, `pippenger`, and Ristretto code at once.

Suggested approach:

- Prove completeness first if possible, because it is a local algebraic statement about the concrete addition formula.
- Then use completeness plus existing commutativity/canonicalization lemmas to attack associativity.

Current status:

- `axiom_edwards_add_complete` is still trusted, but its main hidden prerequisite has now been surfaced explicitly as `axiom_edwards_d_not_square` in [constants_lemmas.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lemmas/edwards_lemmas/constants_lemmas.rs).
- In code, `axiom_edwards_add_complete` has now been split into two smaller trusted obligations in [curve_equation_lemmas.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lemmas/edwards_lemmas/curve_equation_lemmas.rs): `axiom_edwards_add_denominators_nonzero` and `axiom_edwards_add_closed`.
- Runtime tests now check three concrete sanity properties for the current trusted story:
  `EDWARDS_D` is non-square by Euler's criterion, the Edwards-addition denominators stay nonzero for small multiples of the basepoint, and the affine Edwards-addition formula stays on the curve for the same sample set.
- This does not replace the Verus proof, but it narrows the remaining trusted gap: the hard missing step is now the number-theoretic fact that `EDWARDS_D` is a non-square in `GF(p)`, together with the local algebra that turns that fact into denominator non-vanishing. The closure half is now isolated and can potentially be discharged separately via completed/projective addition correctness.

### 2. Edwards scalar multiplication linearity

Files:

- [curve_equation_lemmas.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lemmas/edwards_lemmas/curve_equation_lemmas.rs#L1315)
- [curve_equation_lemmas.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lemmas/edwards_lemmas/curve_equation_lemmas.rs#L3225)

Items:

- `axiom_edwards_scalar_mul_signed_additive`
- `axiom_edwards_scalar_mul_distributive`

Why second:

- These are foundational for variable-base multiplication, Straus, Pippenger, and several batching arguments.
- Once the Edwards group law is mechanized, these become much more approachable.
- A full proof here removes a large amount of downstream algebraic trust.

Suggested approach:

- Treat these as follow-on work after Edwards associativity.
- Reuse the existing recursive structure of `edwards_scalar_mul` instead of proving them from scratch in one shot.

## P1: High-Value Bridge Proofs

These matter a lot for cross-model correctness, but they are best tackled after the Edwards algebra core is stronger.

### 3. Montgomery projective formulas and group facts

Files:

- [montgomery_curve_lemmas.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lemmas/montgomery_curve_lemmas.rs#L43)
- [montgomery_curve_lemmas.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lemmas/montgomery_curve_lemmas.rs#L134)
- [montgomery_curve_lemmas.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lemmas/montgomery_curve_lemmas.rs#L252)

Items:

- `axiom_montgomery_add_associative`
- `axiom_xdbl_projective_correct`
- `axiom_xadd_projective_correct`

Why this tier:

- These are core to the Montgomery ladder story.
- They matter for X25519-style reasoning, but are somewhat more isolated than Edwards group law.
- They likely require substantial projective-coordinate algebra and are easier once field/curve proof libraries are richer.

### 4. Edwards/Montgomery bridge lemmas

Files:

- [montgomery_curve_lemmas.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lemmas/montgomery_curve_lemmas.rs#L1175)
- [montgomery_curve_lemmas.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lemmas/montgomery_curve_lemmas.rs#L1196)
- [montgomery_curve_lemmas.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lemmas/montgomery_curve_lemmas.rs#L1422)

Items:

- `axiom_edwards_to_montgomery_preserves_validity`
- `axiom_montgomery_valid_u_implies_edwards_y_valid`
- `axiom_edwards_to_montgomery_commutes_with_scalar_mul`

Why this tier:

- These are important semantic bridge results, especially for connecting Edwards proofs to Montgomery behavior.
- They depend heavily on the underlying group/algebra facts, so they are not the best first target.

### 5. Concrete number-theoretic bridge facts used by Montgomery/Elligator

Files:

- [montgomery_curve_lemmas.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lemmas/montgomery_curve_lemmas.rs#L732)
- [primality_specs.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/specs/primality_specs.rs#L26)
- [sqrt_m1_lemmas.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lemmas/field_lemmas/sqrt_m1_lemmas.rs#L85)
- [field_specs.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/specs/field_specs.rs#L639)

Items:

- `axiom_486660_not_quadratic_residue`
- `axiom_2_times_486661_not_qr`
- `axiom_p_is_prime`
- `axiom_group_order_is_prime`
- `axiom_sqrt_m1_squared`
- `axiom_sqrt_m1_not_square`
- `axiom_neg_sqrt_m1_not_square`
- `axiom_invsqrt_factors_over_square`

Why this tier:

- These are mathematically important, but many are concrete arithmetic facts about constants.
- Some may remain trusted for a while without undermining the structure of most functional proofs.
- They are good candidates for later replacement by computation-heavy lemmas or external certificates.

## P2: Ristretto and Lizard Deep Algebra

These are important for completeness, but many are larger proof projects with narrower contributor overlap.

### 6. Ristretto decode and Elligator correctness

Files:

- [axioms.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lemmas/ristretto_lemmas/axioms.rs#L26)

Items:

- `axiom_ristretto_decode_on_curve`
- `axiom_ristretto_decode_in_even_subgroup`
- `axiom_ristretto_cross_mul_iff_equivalent`
- `axiom_elligator_on_curve`
- `axiom_elligator_nonzero_intermediates`
- `axiom_elligator_in_even_subgroup`
- `axiom_even_subgroup_closed_under_add`
- `axiom_invsqrt_a_minus_d`

Why this tier:

- These are very important for full Ristretto soundness.
- They are also deeper, more specialized, and often depend on earlier Edwards and field-algebra work.
- They are better approached after more of the base algebra is discharged.

### 7. Lizard proof bypasses

Files:

- [jacobi_quartic.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lizard/jacobi_quartic.rs#L43)
- [lizard_ristretto.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lizard/lizard_ristretto.rs#L197)
- [lizard_ristretto.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lizard/lizard_ristretto.rs#L288)
- [lizard_ristretto.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lizard/lizard_ristretto.rs#L434)
- [lizard_ristretto.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/lizard/lizard_ristretto.rs#L515)

Items:

- `JacobiPoint::elligator_inv` proof bypass
- `lizard_decode_verus` proof bypass
- `decode_253_bits` proof bypass
- `elligator_ristretto_flavor_inverse` proof bypass
- `to_jacobi_quartic_ristretto` proof bypass

Why this tier:

- These are significant, but they sit behind a feature and build on hard Ristretto/Elligator facts.
- They should not be the first place to spend proof effort if the goal is global trust reduction.

## P3: Trusted Modeling Assumptions

These should be documented and reduced over time, but they are usually lower priority than mechanizing core algebra.

### 8. Constant-table assumptions

Files:

- [edwards_specs.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/specs/edwards_specs.rs#L159)
- [window_specs.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/specs/window_specs.rs#L205)

Items:

- `axiom_ed25519_basepoint_table_valid`
- `axiom_affine_odd_multiples_of_basepoint_valid`

Why lower:

- These are trusted constant-table facts, not broad algebraic principles.
- They are often easier to justify by generation scripts or concrete checks than by symbolic proof.

### 9. Hash/external-body assumptions

Files:

- [core_assumes.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/core_assumes.rs#L286)

Items:

- `axiom_hash_is_canonical`
- `axiom_sha512_output_length`
- `axiom_sha256_output_length`

Why lower:

- These mostly arise from external modeling boundaries.
- They matter, but reducing them rarely unlocks large proof chains elsewhere.

### 10. Probability axioms

Files:

- [proba_specs.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/specs/proba_specs.rs#L119)

Items:

- `axiom_uniform_bytes_split`
- `axiom_from_bytes_uniform`
- `axiom_from_bytes_independent`
- `axiom_uniform_elligator`
- `axiom_uniform_elligator_independent`
- `axiom_uniform_elligator_sum`
- `axiom_uniform_point_add`
- `axiom_uniform_mod_reduction`

Why lower:

- These are closer to a probabilistic cryptography model than to the core functional correctness story.
- They are valuable, but they should not block progress on the deterministic algebraic core.

## Quick Start Recommendations

If the goal is to reduce trusted assumptions with the best return on effort, the recommended order is:

1. `axiom_edwards_add_complete`
2. `axiom_edwards_add_associative`
3. `axiom_edwards_scalar_mul_signed_additive`
4. `axiom_edwards_scalar_mul_distributive`
5. `axiom_xdbl_projective_correct`
6. `axiom_xadd_projective_correct`
7. Edwards/Montgomery bridge lemmas
8. Ristretto decode and Elligator axioms

If the goal is instead to improve contributor onboarding with smaller tasks, good starter targets are:

1. ~~`lemma_u128_shl_is_mul`~~ — **Done.** Proved via induction mirroring the vstd u64 technique. Also unblocked `lemma_u128_shift_is_pow2`, `lemma_u128_shl_by_sum`, `lemma_u128_shl_le`, `lemma_u128_left_right_shift`, `lemma_u128_right_left_shift`, and `lemma_u128_right_left_shift_divisible`.
2. Constant-table axioms in [edwards_specs.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/specs/edwards_specs.rs#L159) and [window_specs.rs](/Users/ajiao/dalek-lite/curve25519-dalek/src/specs/window_specs.rs#L205)
3. Concrete arithmetic facts such as `axiom_486660_not_quadratic_residue`

## Notes

- This is a planning document, not a proof artifact.
- Some items may remain intentionally trusted if the cost of full mechanization is higher than the trust reduction gained.
- The companion background document for references and rationale is [axiom_references.md](/Users/ajiao/dalek-lite/docs/axiom_references.md#L1).
