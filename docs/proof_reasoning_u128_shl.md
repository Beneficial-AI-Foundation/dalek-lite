# Proof Reasoning: `lemma_u128_shl_is_mul`

This document records the detailed step-by-step reasoning process used to prove `lemma_u128_shl_is_mul` in the dalek-lite Verus verification project. The goal is to capture not just the final proof, but the judgment basis behind every decision.

## Background

The function `lemma_u128_shl_is_mul` in `curve25519-dalek/src/lemmas/common_lemmas/shift_lemmas.rs` states:

```rust
pub broadcast proof fn lemma_u128_shl_is_mul(x: u128, shift: u128)
    requires
        0 <= shift < 128,
        x * pow2(shift as nat) <= u128::MAX,
    ensures
        #[trigger] (x << shift) == x * pow2(shift as nat),
    decreases shift,
{
    assume(false);  // <-- the trusted gap to eliminate
}
```

It was originally trusted via `assume(false)`. The task was to replace this with a real proof.

## Step 0: Target Selection

**Question**: Which `admit()`/`assume(false)` should we prove first?

**Process**: Scanned all ~50 remaining trusted gaps and classified them by difficulty:

| Category | Example | Difficulty | Why |
|----------|---------|------------|-----|
| Big number theory | `axiom_p_is_prime` | Infeasible | Requires 255-bit modular exponentiation, beyond Verus/Z3 capabilities |
| Edwards group law | `axiom_edwards_add_associative` | Very hard | Hundreds of lines of algebraic expansion |
| Hash axioms | `axiom_hash_is_canonical` | Impossible | Uninterpreted external functions, fundamentally unprovable |
| Bit-shift lemmas | `lemma_u128_shl_is_mul` | Easy | vstd already has a proven u64 version with the same structure |

**Judgment basis**: The key criterion was **existence of a template**. The vstd library (Verus standard library) already contains `lemma_u64_shl_is_mul` with a complete proof. Porting a proof from u64 to u128 is mechanical work, not creative mathematics. This made it the lowest-risk, highest-confidence target.

## Step 1: Understand the Statement

**Question**: What exactly needs to be proved?

**Analysis of the signature**:
- `decreases shift` -- the original author already signaled that induction on `shift` is the intended approach
- `x * pow2(shift as nat) <= u128::MAX` -- precondition ensures no overflow
- Goal: `x << shift == x * pow2(shift as nat)` -- left shift equals multiplication by power of 2

**Judgment basis**: The `decreases` clause is a strong hint. In Verus, `decreases` is required for recursive proof functions, meaning the original author designed this to be proved by structural induction on `shift`.

## Step 2: Find and Study the Template

**Question**: Is there an existing proof we can port?

**Action**: Read the vstd source at `~/.cargo/git/checkouts/verus-.../source/vstd/bits.rs`.

**Found**: `lemma_u64_shl_is_mul` with complete proof:

```rust
pub broadcast proof fn lemma_u64_shl_is_mul(x: u64, shift: u64)
    ...
    decreases shift,
{
    if shift == 0 {
        assert(x << 0 == x) by (bit_vector);
        lemma2_to64();  // pow2(0) == 1
    } else {
        assert(x << shift == mul(x << (sub(shift, 1)), 2)) by (bit_vector)
            requires 0 < shift < 64;
        // recursive call + algebraic chain
        ...
    }
}
```

**Judgment basis**: Same mathematical statement, same proof structure, just a different bit width. The proof pattern is: `if base_case { bit_vector } else { bit_vector_recurrence + recursion + algebra }`. Porting from 64 to 128 requires changing the constant `64` to `128` and adjusting types from `u64` to `u128`.

## Step 3: Write the Base Case (`shift == 0`)

```rust
if shift == 0 {
    assert(x << 0 == x) by (bit_vector);
    lemma2_to64();  // provides pow2(0) == 1
}
```

**Judgment basis**:
- `x << 0 == x` is a pure bitwise fact. The `by (bit_vector)` strategy delegates this to Z3's bitvector solver, which handles such equalities trivially.
- We need `pow2(0) == 1` to close the goal `x == x * pow2(0)`. Two approaches were attempted:
  1. **First attempt**: `assert(pow2(0) == 1) by (compute_only)` -- **FAILED** with error `assert_by_compute_only failed to simplify down to true. Instead got: pow2(0) == 1.` This is a known limitation: Verus's `compute_only` strategy doesn't always simplify `pow2`.
  2. **Second attempt**: `lemma2_to64()` -- **SUCCEEDED**. This vstd lemma's postcondition includes `pow2(0) == 1` among other small power-of-2 facts.

**Lesson**: When `by (compute_only)` fails for `pow2`, look for vstd lemmas that establish the same fact as part of their postcondition.

## Step 4: Write the Inductive Step -- Bit-Vector Recurrence

```rust
assert(x << shift == mul(x << ((sub(shift, 1)) as u128), 2)) by (bit_vector)
    requires
        0 < shift < 128,
;
```

**Judgment basis**:
- This states: "shifting left by `n` equals shifting left by `n-1` then multiplying by 2." This is the fundamental recurrence for left shifts.
- Copied directly from the u64 template, changing `64` to `128`.
- The `requires` clause inside `by (bit_vector)` provides the bitvector solver with the necessary range constraints.
- Note the use of `mul` and `sub` (primitive operations) instead of `*` and `-` (spec-level operations). Inside `by (bit_vector)` blocks, only primitive operations are available; spec functions like `pow2` cannot appear.

## Step 5: Satisfy the Recursive Call's Precondition (Hardest Part)

**Question**: To call `lemma_u128_shl_is_mul(x, (shift-1))` recursively, we need its precondition: `x * pow2((shift-1) as nat) <= u128::MAX`. We currently know `x * pow2(shift as nat) <= u128::MAX`. How do we bridge the gap?

**Reasoning chain**:
1. Need: `x * pow2(shift-1) <= u128::MAX`
2. Have: `x * pow2(shift) <= u128::MAX`
3. If `pow2(shift-1) <= pow2(shift)`, then `x * pow2(shift-1) <= x * pow2(shift) <= u128::MAX`
4. `pow2` is strictly increasing, so `pow2(shift-1) < pow2(shift)` when `shift > 0`

**Lemma hunt**: Searched vstd documentation for:
- `lemma_pow2_strictly_increases(a, b)` -- ensures `pow2(a) < pow2(b)` when `a < b`
- `lemma_mul_inequality(a, b, c)` -- ensures `a <= b && c >= 0 ==> a*c <= b*c`
- `lemma_mul_is_commutative(a, b)` -- ensures `a*b == b*a`

**The commutativity issue**: `lemma_mul_inequality` proves `a*c <= b*c` (multiplier on the right), but we need `c*a <= c*b` (multiplier on the left). So we must apply commutativity to rearrange:

```rust
lemma_pow2_strictly_increases((shift - 1) as nat, shift as nat);
// ==> pow2(shift-1) < pow2(shift)

lemma_mul_inequality(
    pow2((shift - 1) as nat) as int,
    pow2(shift as nat) as int,
    x as int,
);
// ==> pow2(shift-1) * x <= pow2(shift) * x

lemma_mul_is_commutative(x as int, pow2((shift - 1) as nat) as int);
lemma_mul_is_commutative(x as int, pow2(shift as nat) as int);
// ==> x * pow2(shift-1) <= x * pow2(shift)
```

**Judgment basis**: This is a standard pattern in Verus proofs -- vstd's arithmetic lemmas often have a specific argument order, and you need commutativity to adapt them to your context. Recognizing this pattern comes from reading existing proofs in the codebase.

## Step 6: Algebraic Chain via `calc!` Macro

After the recursive call establishes `x << (shift-1) == x * pow2(shift-1)`, we need to show:

```
(x << (shift-1)) * 2 == x * pow2(shift)
```

This is a three-step algebraic chain:

```rust
calc!{ (==)
    ((x << (sub(shift, 1) as u128)) * 2);
        {}
    ((x * pow2(sub(shift, 1) as nat)) * 2);       // substitute induction hypothesis
        {
            lemma_mul_is_associative(x as int, pow2(sub(shift, 1) as nat) as int, 2);
        }
    x * ((pow2(sub(shift, 1) as nat)) * 2);       // associativity: (a*b)*c == a*(b*c)
        {
            lemma_pow2_adds((shift - 1) as nat, 1);
            lemma2_to64();                          // pow2(1) == 2
        }
    x * pow2(shift as nat);                        // pow2(n-1) * pow2(1) == pow2(n)
}
```

**Judgment basis for each step**:

1. **Substitution** (step 1 to 2): The induction hypothesis directly rewrites `x << (shift-1)` to `x * pow2(shift-1)`. The empty `{}` block means Verus can see this automatically.

2. **Associativity** (step 2 to 3): `(x * pow2(shift-1)) * 2 == x * (pow2(shift-1) * 2)`. This is `lemma_mul_is_associative` from vstd. Required because we need to group `pow2(shift-1) * 2` together for the next step.

3. **Power-of-2 addition** (step 3 to 4): `pow2(shift-1) * 2 == pow2(shift-1) * pow2(1) == pow2(shift)`. Uses:
   - `lemma_pow2_adds(a, b)` which gives `pow2(a) * pow2(b) == pow2(a+b)`
   - `lemma2_to64()` which gives `pow2(1) == 2`

**Import issue**: The `calc!` macro requires `use vstd::calc;`. This was discovered by trial and error -- the first compilation attempt without this import produced `error: cannot find macro 'calc' in this scope`.

## Step 7: Debugging and Environment Issues

Several non-mathematical issues had to be resolved:

1. **Verus version mismatch**: Local Verus (commit `23dc6e75`) was newer than the project's pinned version (`88f7396`). This caused a panic: `unexpected verus diagnostic item verus::verus_builtin::fin`. Fix: check out the correct Verus commit and rebuild with `vargo build --release`.

2. **Rust toolchain mismatch**: Local Rust 1.93.1 vs required 1.92.0. Fix: `rustup toolchain install 1.92.0` and prefix commands with `RUSTUP_TOOLCHAIN=1.92.0`.

3. **Git authentication**: HTTPS password auth failed for the fork. Fix: switch remote URL to SSH (`git@github.com:jyizheng/dalek-lite.git`).

**Judgment basis**: Always match the exact toolchain versions specified by the project. Verus is particularly sensitive to version mismatches because its internal diagnostics change between commits.

## Summary: Decision Framework

| Step | Strategy | Decision Basis |
|------|----------|----------------|
| Target selection | Find proofs with existing templates | Template existence = low risk, high confidence |
| Read the statement | Look at `decreases`, `requires`, `ensures` | `decreases shift` signals induction structure |
| Find template | Search vstd for same-named lemma at lower bit width | vstd often has u8/u16/u32/u64 versions |
| Base case | `by (bit_vector)` for bitwise facts | Z3's bitvector solver handles concrete bit equalities |
| Recurrence | `by (bit_vector)` with `requires` | "Shift by n = shift by n-1 then times 2" is a bitvector fact |
| Preconditions | Monotonicity + multiplication inequality | `pow2` is increasing, so smaller shift = smaller product |
| Algebra | `calc!` macro + vstd lemmas | Associativity + `pow2` addition property |
| Debugging | Fix one error at a time, commit after each success | Incremental progress preserves working states |

**Core principle**: Don't derive proofs from scratch. Find an existing template, port it mechanically, and debug the gaps. The creative work is in choosing the right template and identifying which vstd lemmas bridge each gap.
