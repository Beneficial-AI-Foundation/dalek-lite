# Proof of `decompress::step_1` Correctness

This document proves the correctness of the validation step in Ristretto decompression.

## Definitions

**Field.** p = 2^255 − 19. Elements of GF(p) are represented as 5 limbs of 51 bits
each (the `FieldElement51` type). The "canonical" representative of a field element
is the unique integer in [0, p).

**`from_bytes(b)`**: Interprets 32 bytes `b` as a 255-bit little-endian integer
(the high bit of byte 31 is ignored) and loads it into 51-bit limbs. The resulting
field element has `fe51_as_nat(result) == u8_32_as_nat(b) % 2^255`. Since all limbs
are masked to 51 bits, `fe51_limbs_bounded(result, 51)`.

**`as_bytes(fe)`**: Reduces the limb representation to canonical form (mod p),
then packs the canonical representative into 32 little-endian bytes. The result
satisfies `u8_32_as_nat(result) == fe51_as_canonical_nat(fe)`.

**`is_negative(n)`**: Returns true iff the canonical representative of n is odd,
i.e., `(n mod p) mod 2 == 1`. In the byte encoding, this is equivalent to the
low bit of byte 0 being set.

**`field_element_from_bytes(b)`**: The spec-level function that maps bytes to a
canonical field element: `field_element_from_bytes(b) = (u8_32_as_nat(b) % 2^255) % p`.

## Theorem (Canonical Round-trip)

**Statement.** For a field element `s = from_bytes(b)`:

    as_bytes(s) == b   ⟺   u8_32_as_nat(b) < p

**Proof.**

(⟹) Suppose `as_bytes(s) == b`. Then:
- `u8_32_as_nat(b) == u8_32_as_nat(as_bytes(s)) == fe51_as_canonical_nat(s)`
- `fe51_as_canonical_nat(s) = fe51_as_nat(s) % p = (u8_32_as_nat(b) % 2^255) % p`
- Since the canonical representative is in [0, p), we have `u8_32_as_nat(b) < p`
  (if `u8_32_as_nat(b) ≥ p` then `as_bytes` would produce a different, smaller value).

(⟸) Suppose `u8_32_as_nat(b) < p`. Then `u8_32_as_nat(b) < 2^255` (since p < 2^255), so:
- `fe51_as_nat(s) = u8_32_as_nat(b) % 2^255 = u8_32_as_nat(b)`
- `fe51_as_canonical_nat(s) = u8_32_as_nat(b) % p = u8_32_as_nat(b)` (since < p)
- `as_bytes(s)` encodes `u8_32_as_nat(b)` in little-endian, which equals `b`
  (since canonical little-endian encoding is unique for values < 2^256).

∎

## Theorem (Sign Check)

**Statement.** For `s = from_bytes(b)`:

    is_negative(s) == is_negative(field_element_from_bytes(b))

That is, the exec-level sign check on `s` matches the spec-level sign of the
decoded field element.

**Proof.**

The `is_negative` function checks whether `as_bytes(s)[0] & 1 == 1`.

Step 1: By `lemma_is_negative_equals_parity`:

    (as_bytes(s)[0] & 1 == 1)  ⟺  (fe51_as_canonical_nat(s) % 2 == 1)

This follows because the low bit of the little-endian encoding equals the
parity of the encoded value.

Step 2: Connect canonical nat to spec:

    fe51_as_canonical_nat(s) = (u8_32_as_nat(b) % 2^255) % p = field_element_from_bytes(b)

Step 3: By definition, `is_negative(n) = (n % p) % 2 == 1`. Since
`field_element_from_bytes(b) < p`, we have
`field_element_from_bytes(b) % p = field_element_from_bytes(b)`, so:

    is_negative(field_element_from_bytes(b)) = (field_element_from_bytes(b) % 2 == 1)
                                              = (fe51_as_canonical_nat(s) % 2 == 1)

which equals the exec check.

∎

## Theorem (step_1 Postconditions)

**Statement.** `step_1(repr)` returns `(s_encoding_is_canonical, s_is_negative, s)` satisfying:

1. `fe51_limbs_bounded(s, 51)` — limbs are 51-bit bounded (from `from_bytes`)
2. `fe51_as_canonical_nat(s) == field_element_from_bytes(repr.0)` — value matches spec
3. `s_encoding_is_canonical ⟺ (spec_fe51_as_bytes(s) == repr.0)` — canonical iff round-trips
4. `s_is_negative == is_negative(field_element_from_bytes(repr.0))` — sign matches spec
5. `s_encoding_is_canonical ⟹ u8_32_as_nat(repr.0) < p` — canonical implies < p

**Proof.**

1. Direct from `from_bytes` postcondition: all limbs are masked to 51 bits.

2. `fe51_as_canonical_nat(s) = fe51_as_nat(s) % p = (u8_32_as_nat(repr.0) % 2^255) % p = field_element_from_bytes(repr.0)`.

3. The exec code computes `s_bytes_check = as_bytes(s)` and compares with `repr.0`
   using constant-time equality. By Theorem (Canonical Round-trip), this succeeds iff
   `u8_32_as_nat(repr.0) < p`, which is equivalent to `spec_fe51_as_bytes(s) == repr.0@`
   via `lemma_as_bytes_equals_spec_fe51_to_bytes` and `lemma_seq_eq_implies_array_eq`.

4. By Theorem (Sign Check).

5. By the forward direction of Theorem (Canonical Round-trip).

∎

## Lemma Dependencies

| Lemma | Purpose | Status |
|-------|---------|--------|
| `lemma_as_bytes_equals_spec_fe51_to_bytes` | Connects exec `as_bytes` to spec | PROVEN |
| `lemma_is_negative_equals_parity` | Low bit = parity | PROVEN |
| `lemma_seq_eq_implies_array_eq` | Sequence equality → array equality | PROVEN |
| `lemma_canonical_check_backward` | Canonical bytes → spec alignment | PROVEN |
| `from_bytes` postcondition | 51-bit limbs, value = input % 2^255 | PROVEN |
| `as_bytes` postcondition | Canonical encoding, value = canonical nat | PROVEN |

All lemmas used in step_1 are fully proven. No axioms are needed for this step.
