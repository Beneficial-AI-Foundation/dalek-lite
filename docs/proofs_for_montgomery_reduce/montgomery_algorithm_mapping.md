# Montgomery Reduction: Paper to Implementation Mapping

This document maps the original Montgomery REDC algorithm from the 1985 paper to the curve25519-dalek implementation, analyzing correctness and the refinement relationship.

---

## 1. Original Algorithm from Montgomery's 1985 Paper

### 1.1 Basic REDC (Single-Precision)

From Peter L. Montgomery, "Modular Multiplication Without Trial Division", Mathematics of Computation, Vol. 44, No. 170, April 1985.

**Setup:**
- N > 1 (the modulus)
- R > N, coprime to N (the radix, typically a power of 2)
- R⁻¹, N' satisfy: R×R⁻¹ - N×N' = 1 (from extended Euclidean algorithm)
- Equivalently: N×N' ≡ -1 (mod R)

**Algorithm REDC(T):**
```
Input: T with 0 ≤ T < R×N
Output: T×R⁻¹ mod N

function REDC(T):
    m ← (T mod R) × N' mod R        // Step 1: Compute adjustment factor
    t ← (T + m×N) / R               // Step 2: Add multiple of N, divide by R
    if t ≥ N then return t - N      // Step 3: Conditional subtraction
    else return t
```

**Correctness Proof (from paper):**

1. **Division is exact:** 
   - m×N ≡ T×N'×N ≡ -T (mod R)
   - Therefore T + m×N ≡ 0 (mod R), so t = (T + m×N)/R is an integer

2. **Congruence:** 
   - t×R = T + m×N ≡ T (mod N)
   - Therefore t ≡ T×R⁻¹ (mod N)

3. **Bounds:**
   - 0 ≤ m < R
   - 0 ≤ T + m×N < R×N + R×N = 2×R×N
   - Therefore 0 ≤ t < 2×N
   - After conditional subtraction: 0 ≤ result < N

---

### 1.2 Multiprecision REDC (Section 2 of Paper)

For large N and R = bⁿ where b is the machine word size:

```
Input: T = (T_{2n-1} T_{2n-2} ... T_0)_b with 0 ≤ T < R×N
       N = (N_{n-1} N_{n-2} ... N_0)_b
       N' such that N×N' ≡ -1 (mod b)
Output: T×R⁻¹ mod N

function MultiPrecisionREDC(T):
    c ← 0                              // Delayed carry
    for i := 0 to n-1 do
        // Make T divisible by b^{i+1}
        m_i ← T_i × N' mod b
        (d T_{i+n} ... T_i)_b ← (0 T_{i+n} ... T_i)_b + N × m_i
        (c T_{i+n})_b ← c + d + T_{i+n}
    end for
    S ← (c T_{2n-1} ... T_n)_b         // Upper half is the result
    if S ≥ N then return S - N
    else return S
```

**Key insight:** Process one digit at a time. Each iteration:
1. Computes m_i to cancel the lowest unprocessed digit
2. Adds m_i × N to make T divisible by b^{i+1}
3. The division by b^{i+1} is implicit (we just ignore the zeroed digits)

---

## 2. curve25519-dalek Implementation

### 2.1 Parameters

| Parameter | Paper | curve25519-dalek |
|-----------|-------|------------------|
| N (modulus) | Generic | L = 2²⁵² + 27742317777372353535851937790883648493 |
| R (radix) | bⁿ | 2²⁶⁰ = (2⁵²)⁵ |
| b (digit base) | Machine word | 2⁵² (52-bit limbs) |
| n (number of digits) | Generic | 5 |
| N' | N×N' ≡ -1 (mod b) | LFACTOR: L×LFACTOR ≡ -1 (mod 2⁵²) |

**Constants:**
```rust
// L in radix-2^52:
L = [0x0002631a5cf5d3ed,   // L[0]
     0x000dea2f79cd6581,   // L[1]  
     0x000000000014def9,   // L[2]
     0x0000000000000000,   // L[3] = 0 (optimization: skip multiplications)
     0x0000100000000000]   // L[4] = 2^44

LFACTOR = 0x51da312547e1b   // L × LFACTOR ≡ -1 (mod 2^52)
```

### 2.2 Input Format

The input `limbs[0..8]` represents a 9-limb number from `mul_internal(a, b)`:
```
T = Σᵢ limbs[i] × 2^{52i}   for i = 0..8
```

This is the product of two 5-limb numbers, giving up to 9 limbs.

---

## 3. Side-by-Side Algorithm Mapping

### 3.1 Phase 1: Computing the Montgomery Factor

| Paper (MultiPrecisionREDC) | curve25519-dalek |
|---------------------------|------------------|
| `for i := 0 to n-1 do` | 5 iterations (i = 0..4) |
| `m_i ← T_i × N' mod b` | `n_i = (sum × LFACTOR) mod 2^52` |
| Add `m_i × N` to T | Add cross-products `n_j × L[k]` |
| Propagate carry | `carry` passed between iterations |

**Iteration 0:**
```
Paper:                              dalek:
─────────────────────────────────   ─────────────────────────────────
m_0 ← T_0 × N' mod b                let (carry, n0) = part1(limbs[0])
T ← T + m_0 × N                     // part1 computes:
                                    //   n0 = (limbs[0] × LFACTOR) mod 2^52
                                    //   carry = (limbs[0] + n0 × L[0]) >> 52
```

**Iteration 1:**
```
Paper:                              dalek:
─────────────────────────────────   ─────────────────────────────────
m_1 ← T_1 × N' mod b                let sum1 = carry + limbs[1] + m(n0, L[1])
T ← T + m_1 × N × b                 let (carry, n1) = part1(sum1)

Note: T_1 now includes carry and    // sum1 includes:
      contribution from m_0 × N[1]  //   - carry from iteration 0
                                    //   - original limbs[1]  
                                    //   - n0 × L[1] (cross-product)
```

**Iteration 2:**
```
Paper:                              dalek:
─────────────────────────────────   ─────────────────────────────────
m_2 ← T_2 × N' mod b                let sum2 = carry + limbs[2] 
T ← T + m_2 × N × b²                        + m(n0, L[2]) + m(n1, L[1])
                                    let (carry, n2) = part1(sum2)
```

**Iteration 3:**
```
Paper:                              dalek:
─────────────────────────────────   ─────────────────────────────────
m_3 ← T_3 × N' mod b                let sum3 = carry + limbs[3]
T ← T + m_3 × N × b³                        + m(n1, L[2]) + m(n2, L[1])
                                    let (carry, n3) = part1(sum3)
                                    // Note: m(n0, L[3]) skipped since L[3] = 0
```

**Iteration 4:**
```
Paper:                              dalek:
─────────────────────────────────   ─────────────────────────────────
m_4 ← T_4 × N' mod b                let sum4 = carry + limbs[4]
T ← T + m_4 × N × b⁴                        + m(n0, L[4]) + m(n2, L[2]) + m(n3, L[1])
                                    let (carry, n4) = part1(sum4)
                                    // Note: m(n1, L[3]) skipped since L[3] = 0
```

### 3.2 The `part1` Function

```rust
// Paper's operation:
//   m_i ← T_i × N' mod b
//   Update T by adding m_i × N

// dalek's part1(sum):
fn part1(sum: u128) -> (u128, u64) {
    let p = (sum as u64).wrapping_mul(LFACTOR) & MASK_52;  // p = sum × LFACTOR mod 2^52
    let carry = (sum + m(p, L[0])) >> 52;                   // (sum + p×L[0]) / 2^52
    (carry, p)
}
```

**Mathematical equivalence:**
- Paper: m_i makes T divisible by b^{i+1}
- dalek: p makes (sum + p×L[0]) divisible by 2^52, producing exact carry

**Key property:** `p × L[0] ≡ -sum (mod 2^52)` because:
- LFACTOR satisfies L × LFACTOR ≡ -1 (mod 2^52)
- So L[0] × LFACTOR ≡ -1 (mod 2^52)
- Therefore p × L[0] = sum × LFACTOR × L[0] ≡ sum × (-1) ≡ -sum (mod 2^52)

---

### 3.3 Phase 2: Extracting the Result (Division by R)

| Paper | curve25519-dalek |
|-------|------------------|
| `S ← (c T_{2n-1} ... T_n)_b` | Extract upper 5 limbs as `[r0, r1, r2, r3, r4]` |
| (Upper half after n iterations) | (Continue accumulating cross-products) |

**Iteration 5 (first part2):**
```
Paper:                              dalek:
─────────────────────────────────   ─────────────────────────────────
S[0] ← T_5 (with carries)           let sum5 = carry + limbs[5]
                                            + m(n1, L[4]) + m(n3, L[2]) + m(n4, L[1])
                                    let (carry, r0) = part2(sum5)
```

**Iteration 6-8:**
```
// Similar pattern, accumulating remaining cross-products of N × L

sum6 = carry + limbs[6] + m(n2, L[4]) + m(n4, L[2])
(carry, r1) = part2(sum6)

sum7 = carry + limbs[7] + m(n3, L[4])
(carry, r2) = part2(sum7)

sum8 = carry + limbs[8] + m(n4, L[4])
(carry, r3) = part2(sum8)

r4 = carry   // Final carry becomes highest limb
```

### 3.4 The `part2` Function

```rust
fn part2(sum: u128) -> (u128, u64) {
    let w = (sum as u64) & MASK_52;   // Low 52 bits
    let carry = sum >> 52;             // High bits
    (carry, w)
}
```

This is simple digit extraction - no Montgomery-specific logic.

---

### 3.5 Phase 3: Conditional Subtraction

| Paper | curve25519-dalek |
|-------|------------------|
| `if S ≥ N then return S - N` | `sub_for_montgomery(intermediate, L)` |
| `else return S` | Returns intermediate or intermediate - L |

---

## 4. Correctness Analysis

### 4.1 Paper's Correctness Proof

Montgomery's paper provides a brief but complete correctness argument:

**Claim 1: Division is exact**
- Each m_i is chosen so that T becomes divisible by b^{i+1}
- After n iterations, T is divisible by R = bⁿ
- Therefore the division by R yields an integer

**Claim 2: Congruence preserved**
- We only add multiples of N to T
- So T (mod N) is unchanged
- Result = T/R ≡ T × R⁻¹ (mod N)

**Claim 3: Bounds**
- Input: 0 ≤ T < R×N
- After adding all m_i × N: T + Σ(m_i × N × bⁱ) < R×N + R×N = 2×R×N
- After dividing by R: 0 ≤ result < 2×N
- After conditional subtraction: 0 ≤ result < N

### 4.2 Does dalek Correctly Refine the Algorithm?

**Question:** Does the curve25519-dalek implementation correctly implement Montgomery's algorithm?

**Analysis:**

| Aspect | Paper | dalek | Match? |
|--------|-------|-------|--------|
| Compute m_i to cancel low digit | m_i = T_i × N' mod b | n_i = sum × LFACTOR mod 2^52 | ✓ |
| Add m_i × N | Full N×L multiplication | Accumulated cross-products | ✓ |
| Division by R | Take upper half | Part2 extracts upper limbs | ✓ |
| Conditional subtraction | if result ≥ N | sub_for_montgomery | ✓ |

**Cross-product pattern verification:**

The N×L multiplication in radix-2^52 gives:
```
N × L = Σᵢ Σⱼ n_i × L[j] × 2^{52(i+j)}
```

At digit position k, the contribution is: `Σ_{i+j=k} n_i × L[j]`

For k=0: n_0 × L[0]                    ✓ (in part1 call 0)
For k=1: n_0 × L[1] + n_1 × L[0]       ✓ (in part1 call 1)
For k=2: n_0 × L[2] + n_1 × L[1] + n_2 × L[0]  ✓ (in part1 call 2)
... and so on

**Optimization:** L[3] = 0, so terms with L[3] are omitted. This is correct.

**Conclusion:** The dalek implementation is a correct refinement of Montgomery's algorithm.

## 5. References

1. Peter L. Montgomery, "Modular Multiplication Without Trial Division", Mathematics of Computation, Vol. 44, No. 170, April 1985, pp. 519-521.
   - https://www.ams.org/journals/mcom/1985-44-170/S0025-5718-1985-0777282-X/

2. Wikipedia: Montgomery modular multiplication
   - https://en.wikipedia.org/wiki/Montgomery_modular_multiplication

3. Handbook of Applied Cryptography, Chapter 14 (Efficient Implementation)
   - http://cacr.uwaterloo.ca/hac/about/chap14.pdf
