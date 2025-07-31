# Comments extracted from 55 Rust files in curve25519-dalek/src

## src/backend/mod.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

**INTERNALS:** Pluggable implementations for different architectures.

The backend code is split into two parts: a serial backend,
and a vector backend.

The [`serial`] backend contains 32- and 64-bit implementations of
field arithmetic and scalar arithmetic, as well as implementations
of point operations using the mixed-model strategy (passing
between different curve models depending on the operation).

The [`vector`] backend contains implementations of vectorized
field arithmetic, used to implement point operations using a novel
implementation strategy derived from parallel formulas of Hisil,
Wong, Carter, and Dawson.

Because the two strategies give rise to different curve models,
it's not possible to reuse exactly the same scalar multiplication
code (or to write it generically), so both serial and vector
backends contain matching implementations of scalar multiplication
algorithms.  These are intended to be selected by a `#[cfg]`-based
type alias.

The [`vector`] backend is selected by the `simd_backend` cargo
feature; it uses the [`serial`] backend for non-vectorized operations.

Return the number of static points in the precomputation.

Determine if the precomputation is empty.

Perform constant-time, variable-base scalar multiplication.

Compute $aA + bB$ in variable time, where $B$ is the Ed25519 basepoint.

## src/backend/serial/curve_models/mod.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Internal curve representations which are not part of the public API.

### Curve representations

Internally, we use several different models for the curve.  Here
is a sketch of the relationship between the models, following [a
post][smith-moderncrypto]
by Ben Smith on the `moderncrypto` mailing list.  This is also briefly
discussed in section 2.5 of [_Montgomery curves and their
arithmetic_][costello-smith-2017] by Costello and Smith.

Begin with the affine equation for the curve,
$$
-x^2 + y^2 = 1 + dx^2y^2.
$$
Next, pass to the projective closure $\mathbb P^1 \times \mathbb
P^1 $ by setting $x=X/Z$, $y=Y/T.$  Clearing denominators
gives the model
$$
-X^2T^2 + Y^2Z^2 = Z^2T^2 + dX^2Y^2.
$$
In `curve25519-dalek`, this is represented as the `CompletedPoint`
struct.
To map from $\mathbb P^1 \times \mathbb P^1 $, a product of
two lines, to $\mathbb P^3$, we use the [Segre
embedding](https://en.wikipedia.org/wiki/Segre_embedding)
$$
\sigma : ((X:Z),(Y:T)) \mapsto (XY:XT:ZY:ZT).
$$
Using coordinates $ (W_0:W_1:W_2:W_3) $ for $\mathbb P^3$,
the image $\sigma (\mathbb P^1 \times \mathbb P^1) $ is the
surface defined by $ W_0 W_3 = W_1 W_2 $, and under $
\sigma$, the equation above becomes
$$
-W_1^2 + W_2^2 = W_3^2 + dW_0^2,
$$
so that the curve is given by the pair of equations
$$
\begin{aligned}
-W_1^2 + W_2^2 &= W_3^2 + dW_0^2, \\\\  W_0 W_3 &= W_1 W_2.
\end{aligned}
$$
Up to variable naming, this is exactly the "extended" curve model
introduced in [_Twisted Edwards Curves
Revisited_][hisil-wong-carter-dawson-2008] by Hisil, Wong, Carter,
and Dawson.  In `curve25519-dalek`, it is represented as the
`EdwardsPoint` struct.  We can map from $\mathbb P^3 $ to
$\mathbb P^2 $ by sending $ (W_0:W_1:W_2:W_3) $ to $
(W_1:W_2:W_3) $.  Notice that
$$
\frac {W_1} {W_3} = \frac {XT} {ZT} = \frac X Z = x,
$$
and
$$
\frac {W_2} {W_3} = \frac {YZ} {ZT} = \frac Y T = y,
$$
so this is the same as if we had started with the affine model
and passed to $ \mathbb P^2 $ by setting $ x = W_1 / W_3
$, $y = W_2 / W_3 $.
Up to variable naming, this is the projective representation
introduced in [_Twisted Edwards
Curves_][bernstein-birkner-joye-lange-peters-2008] by Bernstein,
Birkner, Joye, Lange, and Peters.  In `curve25519-dalek`, it is
represented by the `ProjectivePoint` struct.

### Passing between curve models

Although the $ \mathbb P^3 $ model provides faster addition
formulas, the $ \mathbb P^2 $ model provides faster doubling
formulas.  Hisil, Wong, Carter, and Dawson therefore suggest mixing
coordinate systems for scalar multiplication, attributing the idea
to [a 1998 paper][cohen-miyaji-ono-1998] of Cohen, Miyagi, and Ono.

Their suggestion is to vary the formulas used by context, using a
$ \mathbb P^2 \rightarrow \mathbb P^2 $ doubling formula when
a doubling is followed
by another doubling, a $ \mathbb P^2 \rightarrow \mathbb P^3 $
doubling formula when a doubling is followed by an addition, and
computing point additions using a $ \mathbb P^3 \times \mathbb P^3
\rightarrow \mathbb P^2 $ formula.

The `ref10` reference implementation of [Ed25519][ed25519], by
Bernstein, Duif, Lange, Schwabe, and Yang, tweaks
this strategy, factoring the addition formulas through the
completion $ \mathbb P^1 \times \mathbb P^1 $, so that the
output of an addition or doubling always lies in $ \mathbb P^1 \times
\mathbb P^1$, and the choice of which formula to use is replaced
by a choice of whether to convert the result to $ \mathbb P^2 $
or $\mathbb P^3 $.  However, this tweak is not described in
their paper, only in their software.

Our naming for the `CompletedPoint` ($\mathbb P^1 \times \mathbb
P^1 $), `ProjectivePoint` ($\mathbb P^2 $), and
`EdwardsPoint` ($\mathbb P^3 $) structs follows the naming in
Adam Langley's [Golang ed25519][agl-ed25519] implementation, which
`curve25519-dalek` was originally derived from.

Finally, to accelerate readditions, we use two cached point formats
in "Niels coordinates", named for Niels Duif,
one for the affine model and one for the $ \mathbb P^3 $ model:

* `AffineNielsPoint`: $ (y+x, y-x, 2dxy) $
* `ProjectiveNielsPoint`: $ (Y+X, Y-X, Z, 2dXY) $

[smith-moderncrypto]: https://moderncrypto.org/mail-archive/curves/2016/000807.html
[costello-smith-2017]: https://eprint.iacr.org/2017/212
[hisil-wong-carter-dawson-2008]: https://www.iacr.org/archive/asiacrypt2008/53500329/53500329.pdf
[bernstein-birkner-joye-lange-peters-2008]: https://eprint.iacr.org/2008/013
[cohen-miyaji-ono-1998]: https://link.springer.com/content/pdf/10.1007%2F3-540-49649-1_6.pdf
[ed25519]: https://eprint.iacr.org/2011/368
[agl-ed25519]: https://github.com/agl/ed25519

### Internal point representations

A `ProjectivePoint` is a point $(X:Y:Z)$ on the $\mathbb
P^2$ model of the curve.
A point $(x,y)$ in the affine model corresponds to
$(x:y:1)$.

More details on the relationships between the different curve models
can be found in the module-level documentation.

A `CompletedPoint` is a point $((X:Z), (Y:T))$ on the $\mathbb
P^1 \times \mathbb P^1 $ model of the curve.
A point (x,y) in the affine model corresponds to $ ((x:1),(y:1))
$.

More details on the relationships between the different curve models
can be found in the module-level documentation.

A pre-computed point in the affine model for the curve, represented as
$(y+x, y-x, 2dxy)$ in "Niels coordinates".

More details on the relationships between the different curve models
can be found in the module-level documentation.
Safe to derive Eq because affine coordinates.

A pre-computed point on the $ \mathbb P^3 $ model for the
curve, represented as $(Y+X, Y-X, Z, 2dXY)$ in "Niels coordinates".

More details on the relationships between the different curve models
can be found in the module-level documentation.

### Constructors

### Validity checks (for debugging, not CT)
Curve equation is    -x^2 + y^2 = 1 + d*x^2*y^2,
homogenized as (-X^2 + Y^2)*Z^2 = Z^4 + d*X^2*Y^2

### Constant-time assignment

### Point conversions
Convert this point from the $ \mathbb P^2 $ model to the
$ \mathbb P^3 $ model.

This costs $3 \mathrm M + 1 \mathrm S$.
Convert this point from the $ \mathbb P^1 \times \mathbb P^1
$ model to the $ \mathbb P^2 $ model.

This costs $3 \mathrm M $.

Convert this point from the $ \mathbb P^1 \times \mathbb P^1
$ model to the $ \mathbb P^3 $ model.

This costs $4 \mathrm M $.

### Doubling
Double this point: return self + self

Double()

### Addition and Subtraction

XXX(hdevalence) These were doc(hidden) so they don't appear in the
public API docs.
However, that prevents them being used with --document-private-items,
so comment out the doc(hidden) for now until this is resolved

upstream rust issue: https://github.com/rust-lang/rust/issues/46380
###[doc(hidden)]

###[doc(hidden)]

###[doc(hidden)]

###[doc(hidden)]

### Negation

### Debug traits

## src/backend/serial/fiat_u32/field.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2018 Isis Lovecruft, Henry de Valence
See LICENSE for licensing information.

Authors:
- Isis Agora Lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Field arithmetic modulo $p = 2^{255} - 19$, using $32$-bit
limbs with $64$-bit products.

This code was originally derived from Adam Langley's Golang ed25519
implementation, and was then rewritten to use unsigned limbs instead
of signed limbs.

This uses the formally-verified field arithmetic generated by the
[fiat-crypto project](https://github.com/mit-plv/fiat-crypto)

A `FieldElement2625` represents an element of the field
$ \mathbb Z / (2^{255} - 19)$.

In the 32-bit implementation, a `FieldElement` is represented in
radix $2^{25.5}$ as ten `u32`s.  This means that a field
element $x$ is represented as
$$
x = \sum_{i=0}^9 x_i 2^{\lceil i \frac {51} 2 \rceil}
= x_0 + x_1 2^{26} + x_2 2^{51} + x_3 2^{77} + \cdots + x_9 2^{230};
$$
the coefficients are alternately bounded by $2^{25}$ and
$2^{26}$.  The limbs are allowed to grow between reductions up
to $2^{25+b}$ or $2^{26+b}$, where $b = 1.75$.

### Note

The `curve25519_dalek::field` module provides a type alias
`curve25519_dalek::field::FieldElement` to either `FieldElement51`
or `FieldElement2625`.

The backend-specific type `FieldElement2625` should not be used
outside of the `curve25519_dalek::field` module.

The scalar $ 0 $.

The scalar $ 1 $.

The scalar $ -1 $.

Invert the sign of this field element

Given `k > 0`, return `self^(2^k)`.

Load a `FieldElement2625` from the low 255 bits of a 256-bit
input.

### Warning

This function does not check that the input used the canonical
representative.  It masks the high bit, but it will happily
decode 2^255 - 18 to 1.  Applications that require a canonical
encoding of every field element should decode, re-encode to
the canonical encoding, and check that the input was
canonical.

Serialize this `FieldElement51` to a 32-byte array.  The
encoding is canonical.

Compute `self^2`.

Compute `2*self^2`.

## src/backend/serial/fiat_u32/mod.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2018 Isis Lovecruft, Henry de Valence
See LICENSE for licensing information.

Authors:
- Isis Agora Lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

The `u32` backend uses `u32`s and a `(u32, u32) -> u64` multiplier.

This code is intended to be portable, but it requires that
multiplication of two $32$-bit values to a $64$-bit result
is constant-time on the target platform.

This uses the formally-verified field arithmetic generated by the
[fiat-crypto project](https://github.com/mit-plv/fiat-crypto)

## src/backend/serial/fiat_u64/field.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2018 Isis Lovecruft, Henry de Valence
See LICENSE for licensing information.

Authors:
- Isis Agora Lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Field arithmetic modulo $p = 2^{255} - 19$, using $64$-bit
limbs with $128$-bit products.

This uses the formally-verified field arithmetic generated by the
[fiat-crypto project](https://github.com/mit-plv/fiat-crypto)

A `FieldElement51` represents an element of the field
$ \mathbb Z / (2^{255} - 19)$.

In the 64-bit implementation, a `FieldElement` is represented in
radix $2^{51}$ as five `u64`s; the coefficients are allowed to
grow up to $2^{54}$ between reductions modulo $p$.

### Note

The `curve25519_dalek::field` module provides a type alias
`curve25519_dalek::field::FieldElement` to either `FieldElement51`
or `FieldElement2625`.

The backend-specific type `FieldElement51` should not be used
outside of the `curve25519_dalek::field` module.

The scalar $ 0 $.

The scalar $ 1 $.

The scalar $ -1 $.

Given 64-bit input limbs, reduce to enforce the bound 2^(51 + epsilon).

Load a `FieldElement51` from the low 255 bits of a 256-bit
input.

### Warning

This function does not check that the input used the canonical
representative.  It masks the high bit, but it will happily
decode 2^255 - 18 to 1.  Applications that require a canonical
encoding of every field element should decode, re-encode to
the canonical encoding, and check that the input was
canonical.


Serialize this `FieldElement51` to a 32-byte array.  The
encoding is canonical.

Given `k > 0`, return `self^(2^k)`.

Returns the square of this field element.

Returns 2 times the square of this field element.

## src/backend/serial/fiat_u64/mod.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2018 Isis Lovecruft, Henry de Valence
See LICENSE for licensing information.

Authors:
- Isis Agora Lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

The `u64` backend uses `u64`s and a `(u64, u64) -> u128` multiplier.

On x86_64, the idiom `(x as u128) * (y as u128)` lowers to `MUL`
instructions taking 64-bit inputs and producing 128-bit outputs.  On
other platforms, this implementation is not recommended.

On Haswell and newer, the BMI2 extension provides `MULX`, and on
Broadwell and newer, the ADX extension provides `ADCX` and `ADOX`
(allowing the CPU to compute two carry chains in parallel).  These
will be used if available.

## src/backend/serial/mod.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Serial implementations of field, scalar, point arithmetic.

When the vector backend is disabled, the crate uses the mixed-model strategy
for implementing point operations and scalar multiplication; see the
[`curve_models`] and [`scalar_mul`] documentation for more information.

When the vector backend is enabled, the field and scalar
implementations are still used for non-vectorized operations.

## src/backend/serial/scalar_mul/mod.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Implementations of various scalar multiplication algorithms.

Note that all of these implementations use serial code for field
arithmetic with the multi-model strategy described in the
`curve_models` module.  The vectorized AVX2 backend has its own
scalar multiplication implementations, since it only uses one
curve model.

## src/backend/serial/scalar_mul/pippenger.rs


This file is part of curve25519-dalek.
Copyright (c) 2019 Oleg Andreev
See LICENSE for licensing information.

Authors:
- Oleg Andreev <oleganza@gmail.com>

Implementation of a variant of Pippenger's algorithm.

Implements a version of Pippenger's algorithm.

The algorithm works as follows:

Let `n` be a number of point-scalar pairs.
Let `w` be a window of bits (6..8, chosen based on `n`, see cost factor).

1. Prepare `2^(w-1) - 1` buckets with indices `[1..2^(w-1))` initialized with identity points.
Bucket 0 is not needed as it would contain points multiplied by 0.
2. Convert scalars to a radix-`2^w` representation with signed digits in `[-2^w/2, 2^w/2]`.
Note: only the last digit may equal `2^w/2`.
3. Starting with the last window, for each point `i=[0..n)` add it to a bucket indexed by
the point's scalar's value in the window.
4. Once all points in a window are sorted into buckets, add buckets by multiplying each
by their index. Efficient way of doing it is to start with the last bucket and compute two sums:
intermediate sum from the last to the first, and the full sum made of all intermediate sums.
5. Shift the resulting sum of buckets by `w` bits by using `w` doublings.
6. Add to the return value.
7. Repeat the loop.

Approximate cost w/o wNAF optimizations (A = addition, D = doubling):

```ascii
cost = (n*A + 2*(2^w/2)*A + w*D + A)*256/w
|          |       |     |   |
|          |       |     |   looping over 256/w windows
|          |       |     adding to the result
sorting points   |       shifting the sum by w bits (to the next window, starting from last window)
one by one       |
into buckets     adding/subtracting all buckets
multiplied by their indexes
using a sum of intermediate sums
```

For large `n`, dominant factor is (n*256/w) additions.
However, if `w` is too big and `n` is not too big, then `(2^w/2)*A` could dominate.
Therefore, the optimal choice of `w` grows slowly as `n` grows.

This algorithm is adapted from section 4 of <https://eprint.iacr.org/2012/549.pdf>.

Digit width in bits. As digit width grows,
number of point additions goes down, but amount of
buckets and bucket additions grows exponentially.

Collect optimized scalars and points in buffers for repeated access
(scanning the whole set per digit position).

Prepare 2^w/2 buckets.
buckets[i] corresponds to a multiplication factor (i+1).
Clear the buckets when processing another digit.

Iterate over pairs of (point, scalar)
and add/sub the point to the corresponding bucket.
Note: if we add support for precomputed lookup tables,
we'll be adding/subtracting point premultiplied by `digits[i]` to buckets[0].

Widen digit so that we don't run into edge cases when w=8.

Add the buckets applying the multiplication factor to each bucket.
The most efficient way to do that is to have a single sum with two running sums:
an intermediate sum from last bucket to the first, and a sum of intermediate sums.

For example, to add buckets 1*A, 2*B, 3*C we need to add these points:
C
C B
C B A   Sum = C + (C+B) + (C+B+A)

Take the high column as an initial value to avoid wasting time doubling the identity element in `fold()`.
Reuse points across different tests

## src/backend/serial/scalar_mul/precomputed_straus.rs


This file is part of curve25519-dalek.
Copyright (c) 2019 Henry de Valence.
See LICENSE for licensing information.

Authors:
- Henry de Valence <hdevalence@hdevalence.ca>

Precomputation for Straus's method.

We could save some doublings by looking for the highest
nonzero NAF coefficient, but since we might have a lot of
them to search, it's not clear it's worthwhile to check.

## src/backend/serial/scalar_mul/straus.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Implementation of the interleaved window method, also known as Straus' method.

Perform multiscalar multiplication by the interleaved window
method, also known as Straus' method (since it was apparently
[first published][solution] by Straus in 1964, as a solution to [a
problem][problem] posted in the American Mathematical Monthly in
1963).

It is easy enough to reinvent, and has been repeatedly.  The basic
idea is that when computing
$$
Q = s_1 P_1 + \cdots + s_n P_n
$$
by means of additions and doublings, the doublings can be shared
across the $ P_i \$.

We implement two versions, a constant-time algorithm using fixed
windows and a variable-time algorithm using sliding windows.  They
are slight variations on the same idea, and are described in more
detail in the respective implementations.

[solution]: https://www.jstor.org/stable/2310929
[problem]: https://www.jstor.org/stable/2312273

Constant-time Straus using a fixed window of size $4$.

Our goal is to compute
$$
Q = s_1 P_1 + \cdots + s_n P_n.
$$

For each point $ P_i $, precompute a lookup table of
$$
P_i, 2P_i, 3P_i, 4P_i, 5P_i, 6P_i, 7P_i, 8P_i.
$$

For each scalar $ s_i $, compute its radix-$2^4$
signed digits $ s_{i,j} $, i.e.,
$$
s_i = s_{i,0} + s_{i,1} 16^1 + ... + s_{i,63} 16^{63},
$$
with $ -8 \leq s_{i,j} < 8 $.  Since $ 0 \leq |s_{i,j}|
\leq 8 $, we can retrieve $ s_{i,j} P_i $ from the
lookup table with a conditional negation: using signed
digits halves the required table size.

Then as in the single-base fixed window case, we have
$$
\begin{aligned}
s_i P_i &= P_i (s_{i,0} +     s_{i,1} 16^1 + \cdots +     s_{i,63} 16^{63})   \\\\
s_i P_i &= P_i s_{i,0} + P_i s_{i,1} 16^1 + \cdots + P_i s_{i,63} 16^{63}     \\\\
s_i P_i &= P_i s_{i,0} + 16(P_i s_{i,1} + 16( \cdots +16P_i s_{i,63})\cdots )
\end{aligned}
$$
so each $ s_i P_i $ can be computed by alternately adding
a precomputed multiple $ P_i s_{i,j} $ of $ P_i $ and
repeatedly doubling.

Now consider the two-dimensional sum
$$
\begin{aligned}
s_1 P_1 &=& P_1 s_{1,0} &+& 16 (P_1 s_{1,1} &+& 16 ( \cdots &+& 16 P_1 s_{1,63}&) \cdots ) \\\\
+     & &      +        & &      +            & &             & &     +            &           \\\\
s_2 P_2 &=& P_2 s_{2,0} &+& 16 (P_2 s_{2,1} &+& 16 ( \cdots &+& 16 P_2 s_{2,63}&) \cdots ) \\\\
+     & &      +        & &      +            & &             & &     +            &           \\\\
\vdots    & &  \vdots       & &   \vdots          & &             & &  \vdots          &           \\\\
+     & &      +        & &      +            & &             & &     +            &           \\\\
s_n P_n &=& P_n s_{n,0} &+& 16 (P_n s_{n,1} &+& 16 ( \cdots &+& 16 P_n s_{n,63}&) \cdots )
\end{aligned}
$$
The sum of the left-hand column is the result $ Q $; by
computing the two-dimensional sum on the right column-wise,
top-to-bottom, then right-to-left, we need to multiply by $
16$ only once per column, sharing the doublings across all
of the input points.

This puts the scalar digits into a heap-allocated Vec.
To ensure that these are erased, pass ownership of the Vec into a
Zeroizing wrapper.
R_i = s_{i,j} * P_i

Q = Q + R_i

Variable-time Straus using a non-adjacent form of width $5$.

This is completely similar to the constant-time code, but we
use a non-adjacent form for the scalar, and do not do table
lookups in constant time.

The non-adjacent form has signed, odd digits.  Using only odd
digits halves the table size (since we only need odd
multiples), or gives fewer additions for the same table size.

## src/backend/serial/scalar_mul/variable_base.rs


Perform constant-time, variable-base scalar multiplication.
Construct a lookup table of [P,2P,3P,4P,5P,6P,7P,8P]

Setting s = scalar, compute

s = s_0 + s_1*16^1 + ... + s_63*16^63,

with `-8 ≤ s_i < 8` for `0 ≤ i < 63` and `-8 ≤ s_63 ≤ 8`.
This decomposition requires s < 2^255, which is guaranteed by Scalar invariant #1.

Compute s*P as

s*P = P*(s_0 +   s_1*16^1 +   s_2*16^2 + ... +   s_63*16^63)
s*P =  P*s_0 + P*s_1*16^1 + P*s_2*16^2 + ... + P*s_63*16^63
s*P = P*s_0 + 16*(P*s_1 + 16*(P*s_2 + 16*( ... + P*s_63)...))

We sum right-to-left.

Unwrap first loop iteration to save computing 16*identity
Now tmp1 = s_63*P in P1xP1 coords
Now tmp1 = s_i*P + 16*(prev) in P1xP1 coords

## src/backend/serial/scalar_mul/vartime_double_base.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Compute $aA + bB$ in variable time, where $B$ is the Ed25519 basepoint.

Find starting index

## src/backend/serial/u32/constants.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

This module contains various constants (such as curve parameters
and useful field elements like `sqrt(-1)`), as well as
lookup tables of pre-computed points.

The value of minus one, equal to `-&FieldElement::ONE`

sqrt(-486664)

Edwards `d` value, equal to `-121665/121666 mod p`.

Edwards `2*d` value, equal to `2*(-121665/121666) mod p`.

One minus edwards `d` value squared, equal to `(1 - (-121665/121666) mod p) pow 2`

Edwards `d` value minus one squared, equal to `(((-121665/121666) mod p) - 1) pow 2`

`= sqrt(a*d - 1)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.

`= 1/sqrt(a-d)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.

Precomputed value of one of the square roots of -1 (mod p)

`APLUS2_OVER_FOUR` is (A+2)/4. (This is used internally within the Montgomery ladder.)

`MONTGOMERY_A` is equal to 486662, which is a constant of the curve equation
for Curve25519 in its Montgomery form. (This is used internally within the
Elligator map.)

`MONTGOMERY_A_NEG` is equal to -486662. (This is used internally within the
Elligator map.)

`L` is the order of base point, i.e. 2^252 +
27742317777372353535851937790883648493

`L` * `LFACTOR` = -1 (mod 2^29)

`R` = R % L where R = 2^261

`RR` = (R^2) % L where R = 2^261

The Ed25519 basepoint, as an `EdwardsPoint`.

This is called `_POINT` to distinguish it from
`ED25519_BASEPOINT_TABLE`, which should be used for scalar
multiplication (it's much faster).

The 8-torsion subgroup $\mathcal E \[8\]$.

In the case of Curve25519, it is cyclic; the $i$-th element of
the array is $[i]P$, where $P$ is a point of order $8$
generating $\mathcal E\[8\]$.

Thus $\mathcal E\[4\]$ is the points indexed by `0,2,4,6`, and
$\mathcal E\[2\]$ is the points indexed by `0,4`.
The Ed25519 basepoint has y = 4/5.  This is called `_POINT` to
distinguish it from `_TABLE`, which should be used for scalar
multiplication (it's much faster).

Inner item used to hide limb constants from cargo doc output.

Table containing precomputed multiples of the Ed25519 basepoint $B = (x, 4/5)$.

Inner constant, used to avoid filling the docs with precomputed points.

Odd multiples of the basepoint `[B, 3B, 5B, 7B, 9B, 11B, 13B, 15B, ..., 127B]`.

## src/backend/serial/u32/field.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Field arithmetic modulo $p = 2^{255} - 19$, using $32$-bit
limbs with $64$-bit products.

This code was originally derived from Adam Langley's Golang ed25519
implementation, and was then rewritten to use unsigned limbs instead
of signed limbs.

A `FieldElement2625` represents an element of the field
$ \mathbb Z / (2^{255} - 19)$.

In the 32-bit implementation, a `FieldElement` is represented in
radix $2^{25.5}$ as ten `u32`s.  This means that a field
element $x$ is represented as
$$
x = \sum_{i=0}^9 x_i 2^{\lceil i \frac {51} 2 \rceil}
= x_0 + x_1 2^{26} + x_2 2^{51} + x_3 2^{77} + \cdots + x_9 2^{230};
$$
the coefficients are alternately bounded by $2^{25}$ and
$2^{26}$.  The limbs are allowed to grow between reductions up
to $2^{25+b}$ or $2^{26+b}$, where $b = 1.75$.

### Note

The `curve25519_dalek::field` module provides a type alias
`curve25519_dalek::field::FieldElement` to either `FieldElement51`
or `FieldElement2625`.

The backend-specific type `FieldElement2625` should not be used
outside of the `curve25519_dalek::field` module.
See comment in FieldElement51::Sub

Compute a - b as ((a + 2^4 * p) - b) to avoid underflow.
Helper function to multiply two 32-bit integers with 64 bits
of output.

Alias self, _rhs for more readable formulas

We assume that the input limbs x[i], y[i] are bounded by:

x[i], y[i] < 2^(26 + b) if i even
x[i], y[i] < 2^(25 + b) if i odd

where b is a (real) parameter representing the excess bits of
the limbs.  We track the bitsizes of all variables through
the computation and solve at the end for the allowable
headroom bitsize b (which determines how many additions we
can perform between reductions or multiplications).

What happens when we multiply x[i] with y[j] and place the
result into the (i+j)-th limb?

x[i]      represents the value x[i]*2^ceil(i*51/2)
y[j]      represents the value y[j]*2^ceil(j*51/2)
z[i+j]    represents the value z[i+j]*2^ceil((i+j)*51/2)
x[i]*y[j] represents the value x[i]*y[i]*2^(ceil(i*51/2)+ceil(j*51/2))

Since the radix is already accounted for, the result placed
into the (i+j)-th limb should be

x[i]*y[i]*2^(ceil(i*51/2)+ceil(j*51/2) - ceil((i+j)*51/2)).

The value of ceil(i*51/2)+ceil(j*51/2) - ceil((i+j)*51/2) is
1 when both i and j are odd, and 0 otherwise.  So we add

x[i]*y[j] if either i or j is even
2*x[i]*y[j] if i and j are both odd

by using precomputed multiples of x[i] for odd i:

How big is the contribution to z[i+j] from x[i], y[j]?

Using the bounds above, we get:

i even, j even:   x[i]*y[j] <   2^(26+b)*2^(26+b) = 2*2^(51+2*b)
i  odd, j even:   x[i]*y[j] <   2^(25+b)*2^(26+b) = 1*2^(51+2*b)
i even, j  odd:   x[i]*y[j] <   2^(26+b)*2^(25+b) = 1*2^(51+2*b)
i  odd, j  odd: 2*x[i]*y[j] < 2*2^(25+b)*2^(25+b) = 1*2^(51+2*b)

We perform inline reduction mod p by replacing 2^255 by 19
(since 2^255 - 19 = 0 mod p).  This adds a factor of 19, so
we get the bounds (z0 is the biggest one, but calculated for
posterity here in case finer estimation is needed later):

z0 < ( 2 + 1*19 + 2*19 + 1*19 + 2*19 + 1*19 + 2*19 + 1*19 + 2*19 + 1*19 )*2^(51 + 2b) = 249*2^(51 + 2*b)
z1 < ( 1 +  1   + 1*19 + 1*19 + 1*19 + 1*19 + 1*19 + 1*19 + 1*19 + 1*19 )*2^(51 + 2b) = 154*2^(51 + 2*b)
z2 < ( 2 +  1   +  2   + 1*19 + 2*19 + 1*19 + 2*19 + 1*19 + 2*19 + 1*19 )*2^(51 + 2b) = 195*2^(51 + 2*b)
z3 < ( 1 +  1   +  1   +  1   + 1*19 + 1*19 + 1*19 + 1*19 + 1*19 + 1*19 )*2^(51 + 2b) = 118*2^(51 + 2*b)
z4 < ( 2 +  1   +  2   +  1   +  2   + 1*19 + 2*19 + 1*19 + 2*19 + 1*19 )*2^(51 + 2b) = 141*2^(51 + 2*b)
z5 < ( 1 +  1   +  1   +  1   +  1   +  1   + 1*19 + 1*19 + 1*19 + 1*19 )*2^(51 + 2b) =  82*2^(51 + 2*b)
z6 < ( 2 +  1   +  2   +  1   +  2   +  1   +  2   + 1*19 + 2*19 + 1*19 )*2^(51 + 2b) =  87*2^(51 + 2*b)
z7 < ( 1 +  1   +  1   +  1   +  1   +  1   +  1   +  1   + 1*19 + 1*19 )*2^(51 + 2b) =  46*2^(51 + 2*b)
z6 < ( 2 +  1   +  2   +  1   +  2   +  1   +  2   +  1   +  2   + 1*19 )*2^(51 + 2b) =  33*2^(51 + 2*b)
z7 < ( 1 +  1   +  1   +  1   +  1   +  1   +  1   +  1   +  1   +  1   )*2^(51 + 2b) =  10*2^(51 + 2*b)

So z[0] fits into a u64 if 51 + 2*b + lg(249) < 64
if b < 2.5.

The scalar $ 0 $.

The scalar $ 1 $.

The scalar $ -1 $.

Invert the sign of this field element

Compute -b as ((2^4 * p) - b) to avoid underflow.

Given `k > 0`, return `self^(2^k)`.

Given unreduced coefficients `z[0], ..., z[9]` of any size,
carry and reduce them mod p to obtain a `FieldElement2625`
whose coefficients have excess `b < 0.007`.

In other words, each coefficient of the result is bounded by
either `2^(25 + 0.007)` or `2^(26 + 0.007)`, as appropriate.

Carry the value from limb i = 0..8 to limb i+1
Even limbs have 26 bits
Odd limbs have 25 bits

Perform two halves of the carry chain in parallel.
Since z[3] < 2^64, c < 2^(64-25) = 2^39,
so    z[4] < 2^26 + 2^39 < 2^39.0002

Now z[4] < 2^26
and z[5] < 2^25 + 2^13.0002 < 2^25.0004 (good enough)

Last carry has a multiplication by 19:

Since z[9] < 2^64, c < 2^(64-25) = 2^39,
so z[0] + 19*c < 2^26 + 2^43.248 < 2^43.249.

Now z[1] < 2^25 - 2^(43.249 - 26)
< 2^25.007 (good enough)
and we're done.

Load a `FieldElement51` from the low 255 bits of a 256-bit
input.

### Warning

This function does not check that the input used the canonical
representative.  It masks the high bit, but it will happily
decode 2^255 - 18 to 1.  Applications that require a canonical
encoding of every field element should decode, re-encode to
the canonical encoding, and check that the input was
canonical.

Serialize this `FieldElement51` to a 32-byte array.  The
encoding is canonical.
Reduce the value represented by `in` to the range [0,2*p)

XXX this cast is annoying

Let h be the value to encode.

Write h = pq + r with 0 <= r < p.  We want to compute r = h mod p.

Since h < 2*p, q = 0 or 1, with q = 0 when h < p and q = 1 when h >= p.

Notice that h >= p <==> h + 19 >= p + 19 <==> h + 19 >= 2^255.
Therefore q can be computed as the carry bit of h + 19.

Now we can compute r as r = h - pq = r - (2^255-19)q = r + 19q - 2^255q

Now carry the result to compute r + 19q...

... but instead of carrying the value
(h[9] >> 25) = q*2^255 into another limb,
discard it, subtracting the value from h.

Check that high bit is cleared
Optimized version of multiplication for the case of squaring.
Pre- and post- conditions identical to multiplication function.

Helper function to multiply two 32-bit integers with 64 bits
of output.

This block is rearranged so that instead of doing a 32-bit multiplication by 38, we do a
64-bit multiplication by 2 on the results.  This is because lg(38) is too big: we would
have less than 1 bit of headroom left, which is too little.

Compute `self^2`.

Compute `2*self^2`.

## src/backend/serial/u32/mod.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

The `u32` backend uses `u32`s and a `(u32, u32) -> u64` multiplier.

This code is intended to be portable, but it requires that
multiplication of two $32$-bit values to a $64$-bit result
is constant-time on the target platform.

## src/backend/serial/u32/scalar.rs

Arithmetic mod 2^252 + 27742317777372353535851937790883648493
with 9 29-bit unsigned limbs

To see that this is safe for intermediate results, note that
the largest limb in a 9 by 9 product of 29-bit limbs will be
(0x1fffffff^2) * 9 = 0x23fffffdc0000009 (62 bits).

For a one level Karatsuba decomposition, the specific ranges
depend on how the limbs are combined, but will stay within
-0x1ffffffe00000008 (62 bits with sign bit) to
0x43fffffbc0000011 (63 bits), which is still safe.

The `Scalar29` struct represents an element in $\mathbb{Z} / \ell\mathbb{Z}$ as 9 29-bit
limbs

u32 * u32 = u64 multiply helper
The scalar $ 0 $.

Unpack a 32 byte / 256 bit scalar into 9 29-bit limbs.

Reduce a 64 byte / 512 bit scalar mod l.

Pack the limbs of this `Scalar29` into 32 bytes.

Compute `a + b` (mod l).

a + b

subtract l if the sum is >= l

Compute `a - b` (mod l).

a - b

conditionally add l if the difference is negative

Compute `a * b`.

This is implemented with a one-level refined Karatsuba decomposition

Compute `a^2`.

Compute `limbs/R` (mod l), where R is the Montgomery modulus 2^261

note: l5,l6,l7 are zero, so their multiplies can be skipped

the first half computes the Montgomery adjustment factor n, and begins adding n*l to make limbs divisible by R

limbs is divisible by R now, so we can divide by R by simply storing the upper half as the result

result may be >= l, so attempt to subtract l

Compute `a * b` (mod l).

Compute `a^2` (mod l).

Compute `(a * b) / R` (mod l), where R is the Montgomery modulus 2^261

Compute `(a^2) / R` (mod l) in Montgomery form, where R is the Montgomery modulus 2^261

Puts a Scalar29 in to Montgomery form, i.e. computes `a*R (mod l)`

Takes a Scalar29 out of Montgomery form, i.e. computes `a/R (mod l)`

Note: x is 2^253-1 which is slightly larger than the largest scalar produced by
this implementation (l-1), and should verify there are no overflows for valid scalars

x = 2^253-1 = 14474011154664524427946373126085988481658748083205070504932198000989141204991
x = 7237005577332262213973186563042994240801631723825162898930247062703686954002 mod l
x = 5147078182513738803124273553712992179887200054963030844803268920753008712037*R mod l in Montgomery form

x^2 = 3078544782642840487852506753550082162405942681916160040940637093560259278169 mod l

x^2 = 2912514428060642753613814151688322857484807845836623976981729207238463947987*R mod l in Montgomery form

y = 6145104759870991071742105800796537629880401874866217824609283457819451087098

x*y = 36752150652102274958925982391442301741

x*y = 3783114862749659543382438697751927473898937741870308063443170013240655651591*R mod l in Montgomery form

a = 2351415481556538453565687241199399922945659411799870114962672658845158063753

b = 4885590095775723760407499321843594317911456947580037491039278279440296187236

a+b = 0
a-b = 4702830963113076907131374482398799845891318823599740229925345317690316127506

c = (2^512 - 1) % l = 1627715501170711445284395025044413883736156588369414752970002579683115011840

## src/backend/serial/u64/common_verus.rs


Auxiliary lemma for multiplication (of nat!)
a * b != 0 <==> a != 0 /\ b != 0
a1 < b1 /\ a2 > 0 ==> a1 * a2 < b1 * a2

a2 < b2 /\ b2 > 0 ==> a2 * b1 < b2 * b1
a1 < b1 /\ a2 > 0 ==> a1 * a2 < b1 * a2

a2 < b2 /\ b2 > 0 ==> a2 * b1 < b2 * b1

Auxiliary lemma for exponentiation

Rewriting lemma; 2^(a + b) * x = 2^a * (2^b * x)
Parenthesis placement matters here

Specialization of lemma_u64_shl_is_mul for x = 1

v << 0 == v for all v

v << (a + b) == (v << a) << b
2^(a + b) == 2^a * 2^b

2^a < 2^(a + b) ...

..., which implies v * 2^a < v * 2^(a + b) <= u64::MAX

v << a + b = v * 2^(a+b)

v << a = v * 2^a
(v * 2^a) << b = (v * 2^a) * 2^b

[<<] preserves [<=] (u64 version)

// If a <= b then v << a <= v << b (up to overflow)
trivial
a != b <=> b > 0
if a != 0 and a != b then 0 < d < b

v << b = (v << (b - a)) << a
we need the precond v * pow2(d) < M

[v <= v << d] => [(v << a) <= (v << d) << a]

v >> 0 == v for all v

v >> (a + b) == (v >> a) >> b

2^(a + b) == 2^a * 2^b

v >> a + b = v / 2^(a+b)

v >> a = v / 2^a

(v / 2^a) << b = (v / 2^a) / 2^b

2^k > 0

v / 2^a / 2^b = v / 2^(a + b)

[>>] preserves [<=] (u64 version)

If a <= b then v >> a >= v >> b
v >> b = (v >> (b - a)) >> a
a <= b => a >> x <= b >> x

u64::MAX = 2^64 - 1
u64::MAX >> k = 2^(64 - k) - 1
1u64 << (64 - k) = 2^(64 - k)

recursion base case
M >> (k + 1) < 1 << (63 - k)

M >> (k + 1) = (M >> k) >> 1

precondition
64 - k = 63
tautology
64 - k < 63

1 << 64 - k = (1 << 63 - k) << 1

(M >> k) >> 1 = (M >> k) / pow2(1);

lemma_u64_shl_is_mul(x, n) precondition: x * pow2(n) <= u64::MAX

(1 << 63 - k) << 1 = (1 << 63 - k) * pow2(1);

Corollary of lemma_u64_max_shifting, since for any
v: u64 it holds that v <= u64::MAX and >> preserves [<=]
(v >> k) <= (u64::MAX >> k)

u64::MAX >> k < 1u64 << (64 - k)

Because &-ing low_bits_mask(k) is a mod operation, it follows that
v & (low_bits_mask(k) as u64) = v % pow2(k) < pow2(k)
v & (low_bits_mask(k) as u64) = v % pow2(k)

pow2(k) > 0

v % pow2(k) < pow2(k)

1 << k = pow2(k)
lbm(0) = 0

lbm(b) = 2 * lbm(b - 1) + 1, in particular, > 0
lbm(b) / 2 = lbm(b - 1)

lbm(a) / 2 = lbm(a - 1)

lbm(a - 1) < lbm(b - 1)

v >> k = v / pow2(k);

v & low_bits_mask(k) = v % pow2(k);

0 < pow2(k) <= u64::MAX

v = (pow2(k) * (v / pow2(k)) + (v % pow2(k)))

m(_,_) multiplication is bounded by the product of the individual bounds

dummy, so we can call `verus common_verus.rs`

## src/backend/serial/u64/constants.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

This module contains backend-specific constant values, such as the 64-bit limbs of curve constants.

The value of minus one, equal to `-&FieldElement::ONE`

sqrt(-486664)

Edwards `d` value, equal to `-121665/121666 mod p`.

Edwards `2*d` value, equal to `2*(-121665/121666) mod p`.

One minus edwards `d` value squared, equal to `(1 - (-121665/121666) mod p) pow 2`

Edwards `d` value minus one squared, equal to `(((-121665/121666) mod p) - 1) pow 2`

`= sqrt(a*d - 1)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.

`= 1/sqrt(a-d)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.

Precomputed value of one of the square roots of -1 (mod p)

`APLUS2_OVER_FOUR` is (A+2)/4. (This is used internally within the Montgomery ladder.)

`MONTGOMERY_A` is equal to 486662, which is a constant of the curve equation
for Curve25519 in its Montgomery form. (This is used internally within the
Elligator map.)

`MONTGOMERY_A_NEG` is equal to -486662. (This is used internally within the
Elligator map.)

`L` is the order of base point, i.e. 2^252 + 27742317777372353535851937790883648493

`L` * `LFACTOR` = -1 (mod 2^52)

`R` = R % L where R = 2^260

`RR` = (R^2) % L where R = 2^260

The Ed25519 basepoint, as an `EdwardsPoint`.

This is called `_POINT` to distinguish it from
`ED25519_BASEPOINT_TABLE`, which should be used for scalar
multiplication (it's much faster).

The 8-torsion subgroup $\mathcal E \[8\]$.

In the case of Curve25519, it is cyclic; the $i$-th element of
the array is $\[i\]P$, where $P$ is a point of order $8$
generating $\mathcal E\[8\]$.

Thus $\mathcal E\[4\]$ is the points indexed by `0,2,4,6`, and
$\mathcal E\[2\]$ is the points indexed by `0,4`.

Inner item used to hide limb constants from cargo doc output.

Table containing precomputed multiples of the Ed25519 basepoint $B = (x, 4/5)$.

Inner constant, used to avoid filling the docs with precomputed points.

Odd multiples of the basepoint `[B, 3B, 5B, 7B, 9B, 11B, 13B, 15B, ..., 127B]`.

## src/backend/serial/u64/field.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Field arithmetic modulo $p = 2^{255} - 19$, using $64$-bit
limbs with $128$-bit products.

A `FieldElement51` represents an element of the field
$ \mathbb Z / (2^{255} - 19)$.

In the 64-bit implementation, a `FieldElement` is represented in
radix $2^{51}$ as five `u64`s; the coefficients are allowed to
grow up to $2^{54}$ between reductions modulo $p$.

### Note

The `curve25519_dalek::field` module provides a type alias
`curve25519_dalek::field::FieldElement` to either `FieldElement51`
or `FieldElement2625`.

The backend-specific type `FieldElement51` should not be used
outside of the `curve25519_dalek::field` module.
To avoid underflow, first add a multiple of p.
Choose 16*p = p << 4 to be larger than 54-bit _rhs.

If we could statically track the bitlengths of the limbs
of every FieldElement51, we could choose a multiple of p
just bigger than _rhs and avoid having to do a reduction.

Since we don't yet have type-level integers to do this, we
have to add an explicit reduction call here.
Helper function to multiply two 64-bit integers with 128
bits of output.

Alias self, _rhs for more readable formulas

Precondition: assume input limbs a[i], b[i] are bounded as

a[i], b[i] < 2^(51 + b)

where b is a real parameter measuring the "bit excess" of the limbs.

64-bit precomputations to avoid 128-bit multiplications.

This fits into a u64 whenever 51 + b + lg(19) < 64.

Since 51 + b + lg(19) < 51 + 4.25 + b
= 55.25 + b,
this fits if b < 8.75.

Multiply to get 128-bit coefficients of output

How big are the c[i]? We have

c[i] < 2^(102 + 2*b) * (1+i + (4-i)*19)
< 2^(102 + lg(1 + 4*19) + 2*b)
< 2^(108.27 + 2*b)

The carry (c[i] >> 51) fits into a u64 when
108.27 + 2*b - 51 < 64
2*b < 6.73
b < 3.365.

So we require b < 3 to ensure this fits.

Casting to u64 and back tells the compiler that the carry is
bounded by 2^64, so that the addition is a u128 + u64 rather
than u128 + u128.

To see that this does not overflow, we need out[0] + carry * 19 < 2^64.

c4 < a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0 + (carry from c3)
< 5*(2^(51 + b) * 2^(51 + b)) + (carry from c3)
< 2^(102 + 2*b + lg(5)) + 2^64.

When b < 3 we get

c4 < 2^110.33  so that carry < 2^59.33

so that

out[0] + carry * 19 < 2^51 + 19 * 2^59.33 < 2^63.58

and there is no overflow.

Now out[1] < 2^51 + 2^(64 -51) = 2^51 + 2^13 < 2^(51 + epsilon).

Now out[i] < 2^(51 + epsilon) for all i.

The scalar $ 0 $.

The scalar $ 1 $.

The scalar $ -1 $.

Invert the sign of this field element

See commentary in the Sub impl

Given 64-bit input limbs, reduce to enforce the bound 2^(51 + epsilon).

Since the input limbs are bounded by 2^64, the biggest
carry-out is bounded by 2^13.

The biggest carry-in is c4 * 19, resulting in

2^51 + 19*2^13 < 2^51.0000000001

Because we don't need to canonicalize, only to reduce the
limb sizes, it's OK to do a "weak reduction", where we
compute the carry-outs in parallel.

Load a `FieldElement51` from the low 255 bits of a 256-bit
input.

### Warning

This function does not check that the input used the canonical
representative.  It masks the high bit, but it will happily
decode 2^255 - 18 to 1.  Applications that require a canonical
encoding of every field element should decode, re-encode to
the canonical encoding, and check that the input was
canonical.

load bits [  0, 64), no shift

load bits [ 48,112), shift to [ 51,112)

load bits [ 96,160), shift to [102,160)

load bits [152,216), shift to [153,216)

load bits [192,256), shift to [204,112)

Serialize this `FieldElement51` to a 32-byte array.  The
encoding is canonical.
Let h = limbs[0] + limbs[1]*2^51 + ... + limbs[4]*2^204.

Write h = pq + r with 0 <= r < p.

We want to compute r = h mod p.

If h < 2*p = 2^256 - 38,
then q = 0 or 1,

with q = 0 when h < p
and q = 1 when h >= p.

Notice that h >= p <==> h + 19 >= p + 19 <==> h + 19 >= 2^255.
Therefore q can be computed as the carry bit of h + 19.

First, reduce the limbs to ensure h < 2*p.

Now we can compute r as r = h - pq = r - (2^255-19)q = r + 19q - 2^255q

Now carry the result to compute r + 19q ...
... but instead of carrying (limbs[4] >> 51) = 2^255q
into another limb, discard it, subtracting the value

Now arrange the bits of the limbs.

High bit should be zero.

Given `k > 0`, return `self^(2^k)`.

Multiply two 64-bit integers with 128 bits of output.
Precondition: assume input limbs a[i] are bounded as

a[i] < 2^(51 + b)

where b is a real parameter measuring the "bit excess" of the limbs.

Precomputation: 64-bit multiply by 19.

This fits into a u64 whenever 51 + b + lg(19) < 64.

Since 51 + b + lg(19) < 51 + 4.25 + b
= 55.25 + b,
this fits if b < 8.75.

Multiply to get 128-bit coefficients of output.

The 128-bit multiplications by 2 turn into 1 slr + 1 slrd each,
which doesn't seem any better or worse than doing them as precomputations
on the 64-bit inputs.

Same bound as in multiply:
c[i] < 2^(102 + 2*b) * (1+i + (4-i)*19)
< 2^(102 + lg(1 + 4*19) + 2*b)
< 2^(108.27 + 2*b)

The carry (c[i] >> 51) fits into a u64 when
108.27 + 2*b - 51 < 64
2*b < 6.73
b < 3.365.

So we require b < 3 to ensure this fits.

Casting to u64 and back tells the compiler that the carry is bounded by 2^64, so
that the addition is a u128 + u64 rather than u128 + u128.

To see that this does not overflow, we need a[0] + carry * 19 < 2^64.

c4 < a2^2 + 2*a0*a4 + 2*a1*a3 + (carry from c3)
< 2^(102 + 2*b + lg(5)) + 2^64.

When b < 3 we get

c4 < 2^110.33  so that carry < 2^59.33

so that

a[0] + carry * 19 < 2^51 + 19 * 2^59.33 < 2^63.58

and there is no overflow.

Now a[1] < 2^51 + 2^(64 -51) = 2^51 + 2^13 < 2^(51 + epsilon).

Now all a[i] < 2^(51 + epsilon) and a = self^(2^k).

Returns the square of this field element.

Returns 2 times the square of this field element.

## src/backend/serial/u64/field_lemmas.rs


Lemmas and spec functions only used in field_verus.rs
A lemma should be in this file instead of `common_verus` if:
- It references some constant prominent in `field_verus` (e.g. 51 for bit operations, 2^255 -19)
- It defines or reasons about a spec function relevant only to `field_verus`

p = 2^255 - 19

Proof that 2^255 > 19

Specialization for b = 51

Evaluation function, given a field element as limbs, reconstruct the nat value it represents.

Evaluation function, given a field element as limbs, reconstruct the nat value it represents.

Verus error: `core::iter::range::impl&%15::fold` is not supported
we write them out manually

Lemma: If a > b pointwise, then as_nat(a - b) = as_nat(a) - as_nat(b)
distribute pow2
0 < b  /\ a < b * c => a/b < c

>> preserves [<=]. Unfortunately, these operations are u128 and
we need lemma_u128_shr_is_div.

Corollary of above, using the identity (a << x) >> x == a for u64::MAX

dummy, so we can call `verus`

## src/backend/serial/u64/field_verus.rs

field.rs

ADAPTED CODE LINES: X.0 globally replaced with X.limbs

MANUALLY moved outside and made explicit
LOW_51_BIT_MASK: u64 = (1u64 << 51) -1; originally

Basic properties of LOW_51_BIT_MASK:
- It's the value of low_bits_mask (spec function defined in vstd and used in its lemmas)
- it's less than 2^51

Masking with low_bits_mask(51) gives a value bounded by 2^51

lemma_div_and_mod specialization for k = 51, using LOW_51_BIT_MASK == low_bits_mask(51)

Each component of spec_reduce is bounded.
The reason we _don't_ write
ensures forall |i: int| 0 <= i < 5 ==> spec_reduce(limbs)[i] < (1u64 << 52)
is that the solver treats `spec_reduce`` above as symbolic and does _not_ instantiate e.g.
((limbs[4] & LOW_51_BIT_MASK) + (limbs[3] >> 51)) as u64 < (1u64 << 52)
\A i. limbs[i] < 2^13

\A i. limbs[i] & LOW_51_BIT_MASK < 2^51

Since 19 < 2^5 and (limbs[4] >> 51) < 2^13, their product is less than 2^18
If (limbs[4] >> 51) < 2^13 and 19 < 2^5 then their product is less than 2^18

The final values (limbs[i] += cX) are all bounded by 2^51 + eps, for eps \in {2^18, 2^13}.

In summary, they're all bounded by 2^52
The solver can prove this automatically
Suppose l = (l0, l1, l2, l3, l4) are the input limbs.
They represent a number
e(l) =  l0 + l1 * 2^51 + l2 * 2^102 + l3 * 2^153 + l4 * 2^204
in Z_p, for p = 2^255 - 19
reduce(l) returns v = (v0, v1, v2, v3, v4), such that
v0 = 19 * a4 + b0
v1 =      a0 + b1
v2 =      a1 + b2
v3 =      a2 + b3
v4 =      a3 + b4
where ai = li >> 51 and bi = li & LOW_51_BIT_MASK
we can reformulate this as ai = li / 2^51 (flooring division) and bi = li % 2^51
Using the following identity connecting integer division and remainder:
x = y * (x / y) + x % y
we can see that li = ai * 2^51 + bi
Plugging the above identities into the equations for v, we can observe that
e(v) = e(l) - p * (l4 >> 51)
IOW, e(reduce(l)) = e(l) (mod p)
additionally, if all limbs are below 2^51, reduce(l) = l

-----
reduce identity for small limbs

Can't seem to reference r within this proof block, we reconstruct it here

-- as_nat identity

ai = limbs[i] / 2^52

bi = limbs[i] % 2^52

distribute

factor out

change groupings

invoke div/mod identity

Add missing limbs[4] parts

The solver can collect components of as_nat(limbs) automatically:
as_nat(rr) == as_nat(limbs) - pow2(204) * (pow2(51) * a4 ) + 19 * a4
... as well as pull in minus
as_nat(rr) == as_nat(limbs) - (pow2(204) * (pow2(51) * a4 ) - 19 * a4)

collect components of p() * a4

MANUALLY moved outside, named return value

MANUALLY moved outside
ADAPTED CODE LINE: we give a name to the field: "limbs"
ADAPTED CODE LINE: limbs is now a named field

Modified to use direct struct

Invert the sign of this field element
Assume we start with l = (l0, l1, l2, l3, l4).
Using c0 = 2^51 - 19 and c = 2^51 - 1, we can see that
( 36028797018963664u64 - l0,
36028797018963952u64 - l1,
36028797018963952u64 - l2,
36028797018963952u64 - l3,
36028797018963952u64 - l4 )
is just 16 * (c0, c, c, c, c) - l (in vector notation)
Further, as_nat((c0, c, c, c, c)) = p, so
as_nat(16 * (c0, c, c, c, c) - l) is 16p - as_nat(l)
We know as_nat(reduce(v)) = as_nat(v) - p * (v4 >> 51) for any v.
This gives us the identity
as_nat(negate(l)) = as_nat(reduce(16 * (c0, c, c, c, c) - l))
= 16p - as_nat(l) - p * ((16c - l4) >> 51)
Note that (16c - l4) >> 51 is either 14 or 15, in either case < 16.
solver knows 36028797018963664u64 == 16 * c0
solver knows 36028797018963952u64 == 16 * c;

Introduce 16p as a vector
by definition of as_nat

solver can reorder factors and pull out 16 on its own
...

Write out `c`s and sum up powers
See commentary in the Sub impl: (copied below)
To avoid underflow, first add a multiple of p.
Choose 16*p = p << 4 to be larger than 54-bit _rhs.

If we could statically track the bitlengths of the limbs
of every FieldElement51, we could choose a multiple of p
just bigger than _rhs and avoid having to do a reduction.

Since we don't yet have type-level integers to do this, we
have to add an explicit reduction call here.
Note on "magic numbers":
36028797018963664u64 = 2^55 - 304 = 16 * (2^51 - 19)
36028797018963952u64 = 2^55 - 16 =  16 * (2^51 - 1)

Given 64-bit input limbs, reduce to enforce the bound 2^(51 + epsilon).

Since the input limbs are bounded by 2^64, the biggest
carry-out is bounded by 2^13.

The biggest carry-in is c4 * 19, resulting in

2^51 + 19*2^13 < 2^51.0000000001

Because we don't need to canonicalize, only to reduce the
limb sizes, it's OK to do a "weak reduction", where we
compute the carry-outs in parallel.

ADAPTED CODE LINE: limbs is now a named field

Load a `FieldElement51` from the low 255 bits of a 256-bit
input.

### Warning

This function does not check that the input used the canonical
representative.  It masks the high bit, but it will happily
decode 2^255 - 18 to 1.  Applications that require a canonical
encoding of every field element should decode, re-encode to
the canonical encoding, and check that the input was
canonical.

TODO:
as_nat(r.limbs) =?= as_nat_32_u8(bytes)
ADAPTED CODE LINE: limbs is now a named field

load bits [  0, 64), no shift

load bits [ 48,112), shift to [ 51,112)

load bits [ 96,160), shift to [102,160)

load bits [152,216), shift to [153,216)

load bits [192,256), shift to [204,112)

Serialize this `FieldElement51` to a 32-byte array.  The
encoding is canonical.
TODO:
as_nat(self.limbs) =?= as_nat_32_u8(r),
canonical encoding
forall|i: int| 0 <= i < 5 ==> r[i] < (1u64 << 51)
Explicit values for pow2(k) for k < 64

TODO
let rr = [
l0 & LOW_51_BIT_MASK,
l1 & LOW_51_BIT_MASK,
l2 & LOW_51_BIT_MASK,
l3 & LOW_51_BIT_MASK,
l4 & LOW_51_BIT_MASK
];

let r = [
rr[0]                           as u8,
(rr[0] >>  8)                    as u8,
(rr[0] >> 16)                    as u8,
(rr[0] >> 24)                    as u8,
(rr[0] >> 32)                    as u8,
(rr[0] >> 40)                    as u8,
((rr[0] >> 48) | (rr[1] << 3)) as u8,
(rr[1] >>  5)                    as u8,
(rr[1] >> 13)                    as u8,
(rr[1] >> 21)                    as u8,
(rr[1] >> 29)                    as u8,
(rr[1] >> 37)                    as u8,
((rr[1] >> 45) | (rr[2] << 6)) as u8,
(rr[2] >>  2)                    as u8,
(rr[2] >> 10)                    as u8,
(rr[2] >> 18)                    as u8,
(rr[2] >> 26)                    as u8,
(rr[2] >> 34)                    as u8,
(rr[2] >> 42)                    as u8,
((rr[2] >> 50) | (rr[3] << 1)) as u8,
(rr[3] >>  7)                    as u8,
(rr[3] >> 15)                    as u8,
(rr[3] >> 23)                    as u8,
(rr[3] >> 31)                    as u8,
(rr[3] >> 39)                    as u8,
((rr[3] >> 47) | (rr[4] << 4)) as u8,
(rr[4] >>  4)                    as u8,
(rr[4] >> 12)                    as u8,
(rr[4] >> 20)                    as u8,
(rr[4] >> 28)                    as u8,
(rr[4] >> 36)                    as u8,
(rr[4] >> 44)                    as u8
];
Let h = limbs[0] + limbs[1]*2^51 + ... + limbs[4]*2^204.

Write h = pq + r with 0 <= r < p.

We want to compute r = h mod p.

If h < 2*p = 2^256 - 38,
then q = 0 or 1,

with q = 0 when h < p
and q = 1 when h >= p.

Notice that h >= p <==> h + 19 >= p + 19 <==> h + 19 >= 2^255.
Therefore q can be computed as the carry bit of h + 19.

First, reduce the limbs to ensure h < 2*p.

Now we can compute r as r = h - pq = r - (2^255-19)q = r + 19q - 2^255q

Now carry the result to compute r + 19q ...
... but instead of carrying (limbs[4] >> 51) = 2^255q
into another limb, discard it, subtracting the value

Now arrange the bits of the limbs.

High bit should be zero.
DISABLED DUE TO NO VERUS SUPPORT FOR PANICS
debug_assert!((s[31] & 0b1000_0000u8) == 0u8);

Given `k > 0`, return `self^(2^k)`.

bv arithmetic

c0
conclusion, (1 + 2 * (19 + 19)) = 77

c1
conclusion, (19 + 2 * (1 + 19)) = 59

c2
conclusion, (1 + 2 * (1 + 19)) = 41

c3
conclusion, (19 + 2 * (1 + 1)) = 23

c4
conclusion, (1 + 2 * (1 + 1)) = 5
a0_0 < (1u64 << 51)
a1_0 < (1u64 << 51)
a2 < (1u64 << 51)
a3 < (1u64 << 51)

a4 < (1u64 << 51)

From the comments below:
c4 < 2^110.33  so that carry < 2^59.33
and
a[0] + carry * 19 < 2^51 + 19 * 2^59.33 < 2^63.58

ceil(2^59.33)

a[0] += carry * 19 fits in u64

a1_0 < (1u64 << 51)

Now a[1] < 2^51 + 2^(64 -51) = 2^51 + 2^13 < 2^(51 + epsilon).
a0_2 < (1u64 << 51)
Precondition: assume input limbs a[i] are bounded as

a[i] < 2^(51 + b)

where b is a real parameter measuring the "bit excess" of the limbs.

Precomputation: 64-bit multiply by 19.

This fits into a u64 whenever 51 + b + lg(19) < 64.

Since 51 + b + lg(19) < 51 + 4.25 + b
= 55.25 + b,
this fits if b < 8.75.

Multiply to get 128-bit coefficients of output.

The 128-bit multiplications by 2 turn into 1 slr + 1 slrd each,
which doesn't seem any better or worse than doing them as precomputations
on the 64-bit inputs.

Same bound as in multiply:
c[i] < 2^(102 + 2*b) * (1+i + (4-i)*19)
< 2^(102 + lg(1 + 4*19) + 2*b)
< 2^(108.27 + 2*b)

The carry (c[i] >> 51) fits into a u64 when
108.27 + 2*b - 51 < 64
2*b < 6.73
b < 3.365.

So we require b < 3 to ensure this fits.
DISABLED DUE TO NO VERUS SUPPORT FOR PANICS
debug_assert!(a[0] < (1 << 54));
debug_assert!(a[1] < (1 << 54));
debug_assert!(a[2] < (1 << 54));
debug_assert!(a[3] < (1 << 54));
debug_assert!(a[4] < (1 << 54));

const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1; // already defined

Casting to u64 and back tells the compiler that the carry is bounded by 2^64, so
that the addition is a u128 + u64 rather than u128 + u128.

To see that this does not overflow, we need a[0] + carry * 19 < 2^64.

c4 < a2^2 + 2*a0*a4 + 2*a1*a3 + (carry from c3)
< 2^(102 + 2*b + lg(5)) + 2^64.

When b < 3 we get

c4 < 2^110.33  so that carry < 2^59.33

so that

a[0] + carry * 19 < 2^51 + 19 * 2^59.33 < 2^63.58

and there is no overflow.

Now a[1] < 2^51 + 2^(64 -51) = 2^51 + 2^13 < 2^(51 + epsilon).

Now all a[i] < 2^(51 + epsilon) and a = self^(2^k).

ADAPTED CODE LINE: limbs is now a named field

Returns the square of this field element.
The precondition in pow2k loop propagates to here
TODO
as_nat(square(x)) = as_nat(x) * as_nat(x)

Returns 2 times the square of this field element.
The precondition in pow2k loop propagates to here
TODO
as_nat(square2(x)) = 2 * as_nat(x) * as_nat(x)

## src/backend/serial/u64/mod.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2018 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

The `u64` backend uses `u64`s and a `(u64, u64) -> u128` multiplier.

On x86_64, the idiom `(x as u128) * (y as u128)` lowers to `MUL`
instructions taking 64-bit inputs and producing 128-bit outputs.  On
other platforms, this implementation is not recommended.

On Haswell and newer, the BMI2 extension provides `MULX`, and on
Broadwell and newer, the ADX extension provides `ADCX` and `ADOX`
(allowing the CPU to compute two carry chains in parallel).  These
will be used if available.

## src/backend/serial/u64/scalar.rs

Arithmetic mod $2^{252} + 27742317777372353535851937790883648493$
with five $52$-bit unsigned limbs.

$51$-bit limbs would cover the desired bit range ($253$
bits), but isn't large enough to reduce a $512$-bit number with
Montgomery multiplication, so $52$ bits is used instead.  To see
that this is safe for intermediate results, note that the largest
limb in a $5\times 5$ product of $52$-bit limbs will be

```text
(0xfffffffffffff^2) * 5 = 0x4ffffffffffff60000000000005 (107 bits).
```

The `Scalar52` struct represents an element in
$\mathbb Z / \ell \mathbb Z$ as 5 $52$-bit limbs.

u64 * u64 = u128 multiply helper
The scalar $ 0 $.

Unpack a 32 byte / 256 bit scalar into 5 52-bit limbs.

Reduce a 64 byte / 512 bit scalar mod l

Pack the limbs of this `Scalar52` into 32 bytes

Compute `a + b` (mod l)

a + b

subtract l if the sum is >= l

Compute `a - b` (mod l)

a - b

conditionally add l if the difference is negative

Compute `a * b`

Compute `a^2`

Compute `limbs/R` (mod l), where R is the Montgomery modulus 2^260

note: l[3] is zero, so its multiples can be skipped

the first half computes the Montgomery adjustment factor n, and begins adding n*l to make limbs divisible by R

limbs is divisible by R now, so we can divide by R by simply storing the upper half as the result

result may be >= l, so attempt to subtract l

Compute `a * b` (mod l)

Compute `a^2` (mod l)

Compute `(a * b) / R` (mod l), where R is the Montgomery modulus 2^260

Compute `(a^2) / R` (mod l) in Montgomery form, where R is the Montgomery modulus 2^260

Puts a Scalar52 in to Montgomery form, i.e. computes `a*R (mod l)`

Takes a Scalar52 out of Montgomery form, i.e. computes `a/R (mod l)`

Note: x is 2^253-1 which is slightly larger than the largest scalar produced by
this implementation (l-1), and should show there are no overflows for valid scalars

x = 14474011154664524427946373126085988481658748083205070504932198000989141204991
x = 7237005577332262213973186563042994240801631723825162898930247062703686954002 mod l
x = 3057150787695215392275360544382990118917283750546154083604586903220563173085*R mod l in Montgomery form

x^2 = 3078544782642840487852506753550082162405942681916160040940637093560259278169 mod l

x^2 = 4413052134910308800482070043710297189082115023966588301924965890668401540959*R mod l in Montgomery form

y = 6145104759870991071742105800796537629880401874866217824609283457819451087098

x*y = 36752150652102274958925982391442301741 mod l

x*y = 658448296334113745583381664921721413881518248721417041768778176391714104386*R mod l in Montgomery form

a = 2351415481556538453565687241199399922945659411799870114962672658845158063753

b = 4885590095775723760407499321843594317911456947580037491039278279440296187236

a+b = 0
a-b = 4702830963113076907131374482398799845891318823599740229925345317690316127506

c = (2^512 - 1) % l = 1627715501170711445284395025044413883736156588369414752970002579683115011840

## src/backend/serial/u64/scalar_verus.rs

scalar64_verus.rs
use crate::constants; // We manually import needed constants

MANUALLY IMPORTED FROM curve25519-dalek/src/backend/serial/u64/constants.rs
`L` is the order of base point, i.e. 2^252 + 27742317777372353535851937790883648493

`RR` = (R^2) mod L where R = 2^260

`LFACTOR` = (-(L^(-1))) mod 2^52

Modular reduction of to_nat mod L

natural value of a 256 bit bitstring represented as array of 32 bytes

Convert bytes to nat in little-endian order using recursive helper

Generic function to convert array of words to natural number
Takes: array of words, number of words, bits per word
Note: This is a specification function that works with concrete types

natural value of a 256 bit bitstring represented as an array of 4 words of 64 bits
Now implemented using the generic function

Group order: the value of L as a natural number

u64 * u64 = u128 multiply helper
ADAPTED CODE LINE: we give a name to the field: "limbs"

***** IMPLEMENTATION CONSTANTS AND FUNCTIONS *******

Unpack a 32 byte / 256 bit scalar into 5 52-bit limbs.

ADAPTED CODE LINE: we give a name to the output: "s"

SPECIFICATION: unpacking keeps the same nat value
TODO: prove property about words array
let mut s = Scalar52::ZERO; // ORIGINAL IMPLEMENTATION

Reduce a 64 byte / 512 bit scalar mod l
TODO; just signature for now

Pack the limbs of this `Scalar52` into 32 bytes
DIFF-SPEC-3: we give a name to the output: "s"
SPECIFICATION: packing keeps the same nat value

Compute `a + b` (mod l)
let mut sum = Scalar52::ZERO;

a + b
forall|j: int| 0 <= j < i ==> sum.limbs[j] < 1u64 << 52,

subtract l if the sum is >= l

** BEGIN: ADAPTED CODE BLOCK **

ORIGINAL CODE
let mut s = Scalar52::sub(&sum, &Self::L);
OUR ADAPTED CODE FOR VERUS; PROVED EQUIVALENT TO ORIGINAL CODE

** END: ADAPTED CODE BLOCK **

Compute `a - b` (mod l)
let mut difference = Scalar52::ZERO;

a - b

conditionally add l if the difference is negative
** BEGIN: ADAPTED CODE BLOCK **
ORIGINAL CODE
let addend = u64::conditional_select(&0, &constants::L[i], underflow);
OUR ADAPTED CODE FOR VERUS

** END: ADAPTED CODE BLOCK **

Compute `a * b`
Each m() result is < 2^104
Sum: 2^104 + 2^104 = 2^105 < 2^128
Each m() result is < 2^104
Sum: 3 * 2^104 = 3 * 2^104 < 2^106 < 2^128
Each m() result is < 2^104
Sum: 4 * 2^104 = 2^2 * 2^104 = 2^106 < 2^128
Each m() result is < 2^104
Sum: 5 * 2^104 < 8 * 2^104 = 2^3 * 2^104 = 2^107 < 2^128

Compute `a^2`
m() ensures its result is < 2^104
Since m_result < 2^104, we have m_result * 2 < 2^105
and 2^105 is well within u128 bounds
Each m() result is < 2^104
m_term1 * 2 < 2^105

Sum: 2^105 + 2^104 = 3 * 2^104 < 2^106 < 2^128
Each m() result is < 2^104
Each * 2 gives < 2^105

Sum: 2^105 + 2^105 = 2^106 < 2^128
Each m() result is < 2^104
First two terms * 2 give < 2^105

Sum: 2^105 + 2^105 + 2^104 = 2^106 + 2^104 < 2^107 < 2^128

Compute `a * b` (mod l)

Compute `a^2` (mod l)

Compute `(a * b) / R` (mod l), where R is the Montgomery modulus 2^260

Compute `(a^2) / R` (mod l) in Montgomery form, where R is the Montgomery modulus 2^260

Helper function for part1 of Montgomery reduction

Helper function for part2 of Montgomery reduction

Montgomery reduction: reduces a 9-limb number to a 5-limb scalar
This is the core of Montgomery arithmetic - it computes (x / R) mod L
where R = 2^260 and L is the scalar field order
TODO: Add proper specification for Montgomery reduction
First half: compute Montgomery adjustment factor n and add n*L to make limbs divisible by R

Second half: limbs is now divisible by R, so divide by R by taking upper half

Result may be >= L, so attempt to subtract L

Puts a Scalar52 into Montgomery form, i.e. computes `a*R (mod L)`
TODO: Add proper specification for Montgomery form conversion

Takes a Scalar52 out of Montgomery form, i.e. computes `a/R (mod L)`
TODO: Add proper specification for Montgomery form conversion

Inverts the scalar using Montgomery logic (simplified)

TODO

Verification: scalar * scalar.invert() ≡ 1 mod L

requires to_scalar(&self.limbs) != 0
ensures (to_scalar(&self.limbs) * invert_spec(&self.limbs)) % group_order() == 1
Test scalar creation from bytes

## src/backend/vector/avx2/constants.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

This module contains constants used by the AVX2 backend.

The identity element as an `ExtendedPoint`.

The identity element as a `CachedPoint`.

The low limbs of (2p, 2p, 2p, 2p), so that
```ascii,no_run
(2p, 2p, 2p, 2p) = [P_TIMES_2_LO, P_TIMES_2_HI, P_TIMES_2_HI, P_TIMES_2_HI, P_TIMES_2_HI]
```

The high limbs of (2p, 2p, 2p, 2p), so that
```ascii,no_run
(2p, 2p, 2p, 2p) = [P_TIMES_2_LO, P_TIMES_2_HI, P_TIMES_2_HI, P_TIMES_2_HI, P_TIMES_2_HI]
```

The low limbs of (16p, 16p, 16p, 16p), so that
```ascii,no_run
(16p, 16p, 16p, 16p) = [P_TIMES_16_LO, P_TIMES_16_HI, P_TIMES_16_HI, P_TIMES_16_HI, P_TIMES_16_HI]
```

The high limbs of (16p, 16p, 16p, 16p), so that
```ascii,no_run
(16p, 16p, 16p, 16p) = [P_TIMES_16_LO, P_TIMES_16_HI, P_TIMES_16_HI, P_TIMES_16_HI, P_TIMES_16_HI]
```

Odd multiples of the Ed25519 basepoint:

## src/backend/vector/avx2/edwards.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Parallel Edwards Arithmetic for Curve25519.

This module currently has two point types:

* `ExtendedPoint`: a point stored in vector-friendly format, with
vectorized doubling and addition;

* `CachedPoint`: used for readdition.

Details on the formulas can be found in the documentation for the
parent `avx2` module.

This API is designed to be safe: vectorized points can only be
created from serial points (which do validation on decompression),
and operations on valid points return valid points, so invalid
point states should be unrepresentable.

This design goal is met, with one exception: the `Neg`
implementation for the `CachedPoint` performs a lazy negation, so
that subtraction can be efficiently implemented as a negation and
an addition.  Repeatedly negating a `CachedPoint` will cause its
coefficients to grow and eventually overflow.  Repeatedly negating
a point should not be necessary anyways.

A point on Curve25519, using parallel Edwards formulas for curve
operations.

### Invariant

The coefficients of an `ExtendedPoint` are bounded with
$ b < 0.007 $.
Compute the double of this point.

Want to compute (X1 Y1 Z1 X1+Y1).
Not sure how to do this less expensively than computing
(X1 Y1 Z1 T1) --(256bit shuffle)--> (X1 Y1 X1 Y1)
(X1 Y1 X1 Y1) --(2x128b shuffle)--> (Y1 X1 Y1 X1)
and then adding.

Set tmp0 = (X1 Y1 X1 Y1)

Set tmp1 = (Y1 X1 Y1 X1)

Set tmp0 = (X1 Y1 Z1 X1+Y1)

Set tmp1 = tmp0^2, negating the D values

Now tmp1 = (S1 S2 S3 -S4) with b < 0.007

See discussion of bounds in the module-level documentation.
We want to compute

+ | S1 | S1 | S1 | S1 |
+ | S2 |    |    | S2 |
+ |    |    | S3 |    |
+ |    |    | S3 |    |
+ |    |    |    |-S4 |
+ |    | 2p | 2p |    |
- |    | S2 | S2 |    |
=======================
S5   S6   S8   S9
tmp0 = (0, 0,  2S_3, 0)

tmp0 = (0, 0,  2S_3, -S_4)

tmp0 = (  S_1,   S_1, S_1 + 2S_3, S_1 - S_4)

tmp0 = (S_1 + S_2,   S_1, S_1 + 2S_3, S_1 + S_2 - S_4)

tmp0 = (S_1 + S_2, S_1 - S_2, S_1 - S_2 + 2S_3, S_1 + S_2 - S_4)
b < (     1.01,       1.6,             2.33,             1.6)
Now tmp0 = (S_5, S_6, S_8, S_9)

Set tmp1 = ( S_9,  S_6,  S_6,  S_9)
b < ( 1.6,  1.6,  1.6,  1.6)

Set tmp0 = ( S_8,  S_5,  S_8,  S_5)
b < (2.33, 1.01, 2.33, 1.01)

Bounds on (tmp0, tmp1) are (2.33, 1.6) < (2.5, 1.75).

A cached point with some precomputed variables used for readdition.

### Warning

It is not safe to negate this point more than once.

### Invariant

As long as the `CachedPoint` is not repeatedly negated, its
coefficients will be bounded with $ b < 1.0 $.
x = (Y2 - X2, Y2 + X2, Z2, T2) = (S2 S3 Z2 T2)
x = (121666*S2 121666*S3 2*121666*Z2 2*121665*T2)
x = (121666*S2 121666*S3 2*121666*Z2 -2*121665*T2)

The coefficients of the output are bounded with b < 0.007.
Lazily negate the point.

### Warning

Because this method does not perform a reduction, it is not
safe to repeatedly negate a point.

Add an `ExtendedPoint` and a `CachedPoint`.

The coefficients of an `ExtendedPoint` are reduced after
every operation.  If the `CachedPoint` was negated, its
coefficients grow by one bit.  So on input, `self` is
bounded with `b < 0.007` and `other` is bounded with
`b < 1.0`.
tmp = (Y1-X1 Y1+X1 Z1 T1) = (S0 S1 Z1 T1) with b < 1.6

(tmp, other) bounded with b < (1.6, 1.0) < (2.5, 1.75).

tmp = (S0*S2' S1*S3' Z1*Z2' T1*T2') = (S8 S9 S10 S11)
tmp = (S8 S9 S11 S10)
tmp = (S9-S8 S9+S8 S10-S11 S10+S11) = (S12 S13 S14 S15)
t0 = (S12 S15 S15 S12)

t1 = (S14 S13 S14 S13)

All coefficients of t0, t1 are bounded with b < 1.6.
Return (S12*S14 S15*S13 S15*S14 S12*S13) = (X3 Y3 Z3 T3)

Implement subtraction by negating the point and adding.

Empirically, this seems about the same cost as a custom
subtraction impl (maybe because the benefit is cancelled by
increased code size?)
Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A, ..., 127A]
Test the serial implementation of the parallel addition formulas

Test the vector implementation of the parallel readdition formulas

## src/backend/vector/avx2/field.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Nightly and stable currently disagree on the requirement of unsafe blocks when `unsafe_target_feature`
gets used.
See: https://github.com/rust-lang/rust/issues/132856

An implementation of 4-way vectorized 32bit field arithmetic using
AVX2.

The `FieldElement2625x4` struct provides a vector of four field
elements, implemented using AVX2 operations.  Its API is designed
to abstract away the platform-dependent details, so that point
arithmetic can be implemented only in terms of a vector of field
elements.

At this level, the API is optimized for speed and not safety.  The
`FieldElement2625x4` does not always perform reductions.  The pre-
and post-conditions on the bounds of the coefficients are
documented for each method, but it is the caller's responsibility
to ensure that there are no overflows.

Unpack 32-bit lanes into 64-bit lanes:
```ascii,no_run
(a0, b0, a1, b1, c0, d0, c1, d1)
```
into
```ascii,no_run
(a0, 0, b0, 0, c0, 0, d0, 0)
(a1, 0, b1, 0, c1, 0, d1, 0)
```

Repack 64-bit lanes into 32-bit lanes:
```ascii,no_run
(a0, 0, b0, 0, c0, 0, d0, 0)
(a1, 0, b1, 0, c1, 0, d1, 0)
```
into
```ascii,no_run
(a0, b0, a1, b1, c0, d0, c1, d1)
```

Input: x = (a0, 0, b0, 0, c0, 0, d0, 0)
Input: y = (a1, 0, b1, 0, c1, 0, d1, 0)

x' = (a0, b0,  0,  0, c0, d0,  0,  0)
y' = ( 0,  0, a1, b1,  0,  0, c1, d1)

The `Lanes` enum represents a subset of the lanes `A,B,C,D` of a
`FieldElement2625x4`.

It's used to specify blend operations without
having to know details about the data layout of the
`FieldElement2625x4`.

The `Shuffle` enum represents a shuffle of a `FieldElement2625x4`.

The enum variants are named by what they do to a vector $
(A,B,C,D) $; for instance, `Shuffle::BADC` turns $ (A, B, C,
D) $ into $ (B, A, D, C) $.

A vector of four field elements.

Each operation on a `FieldElement2625x4` has documented effects on
the bounds of the coefficients.  This API is designed for speed
and not safety; it is the caller's responsibility to ensure that
the post-conditions of one operation are compatible with the
pre-conditions of the next.

Split this vector into an array of four (serial) field
elements.

Rearrange the elements of this vector according to `control`.

The `control` parameter should be a compile-time constant, so
that when this function is inlined, LLVM is able to lower the
shuffle using an immediate.
Note that this gets turned into a generic LLVM
shuffle-by-constants, which can be lowered to a simpler
instruction than a generic permute.

Blend `self` with `other`, taking lanes specified in `control` from `other`.

The `control` parameter should be a compile-time constant, so
that this function can be inlined and LLVM can lower it to a
blend instruction using an immediate.

This would be much cleaner if we could factor out the match
statement on the control. Unfortunately, rustc forgets
constant-info very quickly, so we can't even write
```
match control {
Lanes::C => {
let imm = C_LANES as i32;
_mm256_blend_epi32(..., imm)
```
let alone
```
let imm = match control {
Lanes::C => C_LANES as i32,
}
_mm256_blend_epi32(..., imm)
```
even though both of these would be constant-folded by LLVM
at a lower level (as happens in the shuffle implementation,
which does not require a shuffle immediate but *is* lowered
to immediate shuffles anyways).

Convenience wrapper around `new(x,x,x,x)`.

Create a `FieldElement2625x4` from four `FieldElement51`s.

### Postconditions

The resulting `FieldElement2625x4` is bounded with $ b < 0.0002 $.

We don't know that the original `FieldElement51`s were
fully reduced, so the odd limbs may exceed 2^25.
Reduce them to be sure.

Given $(A,B,C,D)$, compute $(-A,-B,-C,-D)$, without
performing a reduction.

### Preconditions

The coefficients of `self` must be bounded with $ b < 0.999 $.

### Postconditions

The coefficients of the result are bounded with $ b < 1 $.
The limbs of self are bounded with b < 0.999, while the
smallest limb of 2*p is 67108845 > 2^{26+0.9999}, so
underflows are not possible.

Given `self = (A,B,C,D)`, compute `(B - A, B + A, D - C, D + C)`.

### Preconditions

The coefficients of `self` must be bounded with $ b < 0.01 $.

### Postconditions

The coefficients of the result are bounded with $ b < 1.6 $.
tmp1 = (B, A, D, C)

tmp2 = (-A, B, -C, D)

(B - A, B + A, D - C, D + C) bounded with b < 1.6

Reduce this vector of field elements $\mathrm{mod} p$.

### Postconditions

The coefficients of the result are bounded with $ b < 0.0002 $.

Let c(x) denote the carryout of the coefficient x.

Given    (   x0,    y0,    x1,    y1,    z0,    w0,    z1,    w1),
compute  (c(x1), c(y1), c(x0), c(y0), c(z1), c(w1), c(z0), c(w0)).

The carryouts are bounded by 2^(32 - 25) = 2^7.

Combine (lo, lo, lo, lo, lo, lo, lo, lo)
with (hi, hi, hi, hi, hi, hi, hi, hi)
to (lo, lo, hi, hi, lo, lo, hi, hi)

This allows combining carryouts, e.g.,

lo  (c(x1), c(y1), c(x0), c(y0), c(z1), c(w1), c(z0), c(w0))
hi  (c(x3), c(y3), c(x2), c(y2), c(z3), c(w3), c(z2), c(w2))
->  (c(x1), c(y1), c(x2), c(y2), c(z1), c(w1), c(z2), c(w2))

which is exactly the vector of carryins for

(   x2,    y2,    x3,    y3,    z2,    w2,    z3,    w3).


Need to rearrange c98, since vpmuludq uses the low
32-bits of each 64-bit lane to compute the product:

c98       = (c(x9), c(y9), c(x8), c(y8), c(z9), c(w9), c(z8), c(w8));
c9_spread = (c(x9), c(x8), c(y9), c(y8), c(z9), c(z8), c(w9), c(w8)).

Since the carryouts are bounded by 2^7, their products with 19
are bounded by 2^11.25.  This means that

c9_19_spread = (19*c(x9), 0, 19*c(y9), 0, 19*c(z9), 0, 19*c(w9), 0).

Unshuffle:
c9_19 = (19*c(x9), 19*c(y9), 0, 0, 19*c(z9), 19*c(w9), 0, 0).

Add the final carryin.

Each output coefficient has exactly one carryin, which is
bounded by 2^11.25, so they are bounded as

c_even < 2^26 + 2^11.25 < 26.00006 < 2^{26+b}
c_odd  < 2^25 + 2^11.25 < 25.0001  < 2^{25+b}

where b = 0.0002.

Given an array of wide coefficients, reduce them to a `FieldElement2625x4`.

### Postconditions

The coefficients of the result are bounded with $ b < 0.007 $.
These aren't const because splat isn't a const fn

Carry the value from limb i = 0..8 to limb i+1
Even limbs have 26 bits
Odd limbs have 25 bits

Perform two halves of the carry chain in parallel.
Since z[3] < 2^64, c < 2^(64-25) = 2^39,
so    z[4] < 2^26 + 2^39 < 2^39.0002

Now z[4] < 2^26
and z[5] < 2^25 + 2^13.0002 < 2^25.0004 (good enough)

Last carry has a multiplication by 19.  In the serial case we
do a 64-bit multiplication by 19, but here we want to do a
32-bit multiplication.  However, if we only know z[9] < 2^64,
the carry is bounded as c < 2^(64-25) = 2^39, which is too
big.  To ensure c < 2^32, we would need z[9] < 2^57.
Instead, we split the carry in two, with c = c_0 + c_1*2^26.

The output coefficients are bounded with

b = 0.007  for z[1]
b = 0.0004 for z[5]
b = 0      for other z[i].

So the packed result is bounded with b = 0.007.

Square this field element, and negate the result's $D$ value.

### Preconditions

The coefficients of `self` must be bounded with $ b < 1.5 $.

### Postconditions

The coefficients of the result are bounded with $ b < 0.007 $.

The biggest z_i is bounded as z_i < 249*2^(51 + 2*b);
if b < 1.5 we get z_i < 4485585228861014016.

The limbs of the multiples of p are bounded above by

0x3fffffff << 37 = 9223371899415822336 < 2^63

and below by

0x1fffffff << 37 = 4611685880988434432
> 4485585228861014016

So these multiples of p are big enough to avoid underflow
in subtraction, and small enough to fit within u64
with room for a carry.

Negate this field element, performing a reduction.

If the coefficients are known to be small, use `negate_lazy`
to avoid performing a reduction.

### Preconditions

The coefficients of `self` must be bounded with $ b < 4.0 $.

### Postconditions

The coefficients of the result are bounded with $ b < 0.0002 $.
Add two `FieldElement2625x4`s, without performing a reduction.
Perform a multiplication by a vector of small constants.

### Postconditions

The coefficients of the result are bounded with $ b < 0.007 $.
Multiply `self` by `rhs`.

### Preconditions

The coefficients of `self` must be bounded with $ b < 2.5 $.

The coefficients of `rhs` must be bounded with $ b < 1.75 $.

### Postconditions

The coefficients of the result are bounded with $ b < 0.007 $.


The bounds on z[i] are the same as in the serial 32-bit code
and the comment below is copied from there:

How big is the contribution to z[i+j] from x[i], y[j]?

Using the bounds above, we get:

i even, j even:   x[i]*y[j] <   2^(26+b)*2^(26+b) = 2*2^(51+2*b)
i  odd, j even:   x[i]*y[j] <   2^(25+b)*2^(26+b) = 1*2^(51+2*b)
i even, j  odd:   x[i]*y[j] <   2^(26+b)*2^(25+b) = 1*2^(51+2*b)
i  odd, j  odd: 2*x[i]*y[j] < 2*2^(25+b)*2^(25+b) = 1*2^(51+2*b)

We perform inline reduction mod p by replacing 2^255 by 19
(since 2^255 - 19 = 0 mod p).  This adds a factor of 19, so
we get the bounds (z0 is the biggest one, but calculated for
posterity here in case finer estimation is needed later):

z0 < ( 2 + 1*19 + 2*19 + 1*19 + 2*19 + 1*19 + 2*19 + 1*19 + 2*19 + 1*19 )*2^(51 + 2b) = 249*2^(51 + 2*b)
z1 < ( 1 +  1   + 1*19 + 1*19 + 1*19 + 1*19 + 1*19 + 1*19 + 1*19 + 1*19 )*2^(51 + 2b) = 154*2^(51 + 2*b)
z2 < ( 2 +  1   +  2   + 1*19 + 2*19 + 1*19 + 2*19 + 1*19 + 2*19 + 1*19 )*2^(51 + 2b) = 195*2^(51 + 2*b)
z3 < ( 1 +  1   +  1   +  1   + 1*19 + 1*19 + 1*19 + 1*19 + 1*19 + 1*19 )*2^(51 + 2b) = 118*2^(51 + 2*b)
z4 < ( 2 +  1   +  2   +  1   +  2   + 1*19 + 2*19 + 1*19 + 2*19 + 1*19 )*2^(51 + 2b) = 141*2^(51 + 2*b)
z5 < ( 1 +  1   +  1   +  1   +  1   +  1   + 1*19 + 1*19 + 1*19 + 1*19 )*2^(51 + 2b) =  82*2^(51 + 2*b)
z6 < ( 2 +  1   +  2   +  1   +  2   +  1   +  2   + 1*19 + 2*19 + 1*19 )*2^(51 + 2b) =  87*2^(51 + 2*b)
z7 < ( 1 +  1   +  1   +  1   +  1   +  1   +  1   +  1   + 1*19 + 1*19 )*2^(51 + 2b) =  46*2^(51 + 2*b)
z8 < ( 2 +  1   +  2   +  1   +  2   +  1   +  2   +  1   +  2   + 1*19 )*2^(51 + 2b) =  33*2^(51 + 2*b)
z9 < ( 1 +  1   +  1   +  1   +  1   +  1   +  1   +  1   +  1   +  1   )*2^(51 + 2b) =  10*2^(51 + 2*b)

So z[0] fits into a u64 if 51 + 2*b + lg(249) < 64
if b < 2.5.

In fact this bound is slightly sloppy, since it treats both
inputs x and y as being bounded by the same parameter b,
while they are in fact bounded by b_x and b_y, and we
already require that b_y < 1.75 in order to fit the
multiplications by 19 into a u32.  The tighter bound on b_y
means we could get a tighter bound on the outputs, or a
looser bound on b_x.

## src/backend/vector/avx2/mod.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

## src/backend/vector/ifma/constants.rs


This file is part of curve25519-dalek.
Copyright (c) 2018-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- Henry de Valence <hdevalence@hdevalence.ca>

This module contains constants used by the IFMA backend.

The identity element as an `ExtendedPoint`.

The identity element as a `CachedPoint`.

Odd multiples of the Ed25519 basepoint:

## src/backend/vector/ifma/edwards.rs


This file is part of curve25519-dalek.
Copyright (c) 2018-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- Henry de Valence <hdevalence@hdevalence.ca>
(Y1 X1 T1 Z1) -- uses vpshufd (1c latency @ 1/c)

(X1+Y1 X1+Y1 X1+Y1 X1+Y1) -- can use vpinserti128

(X1 Y1 Z1 X1+Y1)
Now tmp1 = (S1 S2 S3 S4)

We want to compute

+ | S1 | S1 | S1 | S1 |
+ | S2 |    |    | S2 |
+ |    |    | S3 |    |
+ |    |    | S3 |    |
+ |    |16p |16p |16p |
- |    | S2 | S2 |    |
- |    |    |    | S4 |
=======================
S5   S6   S8   S9

Add an `ExtendedPoint` and a `CachedPoint`.
tmp = (Y1-X1 Y1+X1 Z1 T1) = (S0 S1 Z1 T1)
tmp = (S0*S2' S1*S3' Z1*Z2' T1*T2') = (S8 S9 S10 S11)
tmp = (S8 S9 S11 S10)
tmp = (S9-S8 S9+S8 S10-S11 S10+S11) = (S12 S13 S14 S15)
t0 = (S12 S15 S15 S12)

t1 = (S14 S13 S14 S13)

Return (S12*S14 S15*S13 S15*S14 S12*S13) = (X3 Y3 Z3 T3)

Implement subtraction by negating the point and adding.
Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A, ..., 127A]
Test the serial implementation of the parallel addition formulas
let R_serial: edwards::EdwardsPoint = serial_add(P.into(), Q.into()).into();

Test the vector implementation of the parallel readdition formulas
println!("R_serial = {:?}", R_serial);
assert_eq!(R_serial.compress(), (&P + &Q).compress());
let R1: edwards::EdwardsPoint = serial_double(P.into()).into();
println!("(serial) R1 = {:?}", R1);
assert_eq!(R1.compress(), (&P + &P).compress());

## src/backend/vector/ifma/field.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Nightly and stable currently disagree on the requirement of unsafe blocks when `unsafe_target_feature`
gets used.
See: https://github.com/rust-lang/rust/issues/132856

A wrapper around `vpmadd52luq` that works on `u64x4`.

A wrapper around `vpmadd52huq` that works on `u64x4`.

A vector of four field elements in radix 2^51, with unreduced coefficients.

A vector of four field elements in radix 2^51, with reduced coefficients.
tmp1 = (B, A, D, C)

tmp2 = (-A, B, -C, D)

(B - A, B + A, D - C, D + C)

Represent values with coeff. 2

Represent values with coeff. 4

Compute carryouts in parallel

Wave 0

Wave 2
Inputs

Accumulators for terms with coeff 1

Accumulators for terms with coeff 2

LLVM doesn't seem to do much work reordering IFMA
instructions, so try to organize them into "waves" of 8
independent operations (4c latency, 0.5 c throughput
means 8 in flight)

Wave 0

Wave 1

Wave 2

Wave 3

Wave 4

Wave 5

Wave 6

Wave 7

Wave 8
Invert a small field element to get a big one
Invert a small field element to get a big one

... but now multiply it by 16 without reducing coeffs
Invert a small field element to get a big one

... but now multiply it by 128 without reducing coeffs
Invert a small field element to get a big one
Invert a small field element to get a big one
Invert a small field element to get a big one
Invert a small field element to get a big one
Invert a small field element to get a big one

## src/backend/vector/ifma/mod.rs


This file is part of curve25519-dalek.
Copyright (c) 2018-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- Henry de Valence <hdevalence@hdevalence.ca>

## src/backend/vector/mod.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

## src/backend/vector/packed_simd.rs


This file is part of curve25519-dalek.
See LICENSE for licensing information.

Nightly and stable currently disagree on the requirement of unsafe blocks when `unsafe_target_feature`
gets used.
See: https://github.com/rust-lang/rust/issues/132856

This module defines wrappers over platform-specific SIMD types to make them
more convenient to use.

UNSAFETY: Everything in this module assumes that we're running on hardware
which supports at least AVX2. This invariant *must* be enforced
by the callers of this code.
This compares each pair of 8-bit packed integers and returns either 0xFF or
0x00 depending on whether they're equal.

So the values are equal if (and only if) this returns a value that's filled
with only 0xFF.

Pseudocode of what this does:
self.0
.bytes()
.zip(rhs.0.bytes())
.map(|a, b| if a == b { 0xFF } else { 0x00 })
.join();

Now we need to reduce the 256-bit value to something on which we can branch.

This will just take the most significant bit of every 8-bit packed integer
and build an `i32` out of it. If the values we previously compared were
equal then all off the most significant bits will be equal to 1, which means
that this will return 0xFFFFFFFF, which is equal to -1 when represented as
an `i32`.

We define SIMD functionality over packed unsigned integer types. However, all the integer
intrinsics deal with signed integers. So we cast unsigned to signed, pack it into SIMD, do
add/sub/shl/shr arithmetic, and finally cast back to unsigned at the end. Why is this equivalent
to doing the same thing on unsigned integers? Shl/shr is clear, because casting does not change
the bits of the integer. But what about add/sub? This is due to the following:

1) Rust uses two's complement to represent signed integers. So we're assured that the values
we cast into SIMD and extract out at the end are two's complement.

https://doc.rust-lang.org/reference/types/numeric.html

2) Wrapping add/sub is compatible between two's complement signed and unsigned integers.
That is, for all x,y: u64 (or any unsigned integer type),

x.wrapping_add(y) == (x as i64).wrapping_add(y as i64) as u64, and
x.wrapping_sub(y) == (x as i64).wrapping_sub(y as i64) as u64

https://julesjacobs.com/2019/03/20/why-twos-complement-works.html

3) The add/sub functions we use for SIMD are indeed wrapping. The docs indicate that
__mm256_add/sub compile to vpaddX/vpsubX instructions where X = w, d, or q depending on
the bitwidth. From x86 docs:

When an individual result is too large to be represented in X bits (overflow), the
result is wrapped around and the low X bits are written to the destination operand
(that is, the carry is ignored).

https://www.felixcloutier.com/x86/paddb:paddw:paddd:paddq
https://www.felixcloutier.com/x86/psubb:psubw:psubd
https://www.felixcloutier.com/x86/psubq
A constified variant of `new`.

Should only be called from `const` contexts. At runtime `new` is going to be faster.
SAFETY: Transmuting between an array and a SIMD type is safe
https://rust-lang.github.io/unsafe-code-guidelines/layout/packed-simd-vectors.html

A constified variant of `splat`.

Should only be called from `const` contexts. At runtime `splat` is going to be faster.

Constructs a new instance.
_mm256_set_epi64 sets the underlying vector in reverse order of the args

Constructs a new instance with all of the elements initialized to the given value.
A constified variant of `new`.

Should only be called from `const` contexts. At runtime `new` is going to be faster.
SAFETY: Transmuting between an array and a SIMD type is safe
https://rust-lang.github.io/unsafe-code-guidelines/layout/packed-simd-vectors.html

A constified variant of `splat`.

Should only be called from `const` contexts. At runtime `splat` is going to be faster.

Constructs a new instance.
_mm256_set_epi32 sets the underlying vector in reverse order of the args

Constructs a new instance with all of the elements initialized to the given value.
Multiplies the low unsigned 32-bits from each packed 64-bit element
and returns the unsigned 64-bit results.

(This ignores the upper 32-bits from each packed 64-bits!)
NOTE: This ignores the upper 32-bits from each packed 64-bits.

## src/backend/vector/scalar_mul/mod.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Implementations of various multiplication algorithms for the SIMD backends.

## src/backend/vector/scalar_mul/pippenger.rs


This file is part of curve25519-dalek.
Copyright (c) 2019 Oleg Andreev
See LICENSE for licensing information.

Authors:
- Oleg Andreev <oleganza@gmail.com>

Implements a version of Pippenger's algorithm.

See the documentation in the serial `scalar_mul::pippenger` module for details.

Collect optimized scalars and points in a buffer for repeated access
(scanning the whole collection per each digit position).

Prepare 2^w/2 buckets.
buckets[i] corresponds to a multiplication factor (i+1).
Clear the buckets when processing another digit.

Iterate over pairs of (point, scalar)
and add/sub the point to the corresponding bucket.
Note: if we add support for precomputed lookup tables,
we'll be adding/subtractiong point premultiplied by `digits[i]` to buckets[0].

Widen digit so that we don't run into edge cases when w=8.

Add the buckets applying the multiplication factor to each bucket.
The most efficient way to do that is to have a single sum with two running sums:
an intermediate sum from last bucket to the first, and a sum of intermediate sums.

For example, to add buckets 1*A, 2*B, 3*C we need to add these points:
C
C B
C B A   Sum = C + (C+B) + (C+B+A)

Take the high column as an initial value to avoid wasting time doubling the identity element in `fold()`.

Reuse points across different tests

## src/backend/vector/scalar_mul/precomputed_straus.rs


This file is part of curve25519-dalek.
Copyright (c) 2019 Henry de Valence.
See LICENSE for licensing information.

Authors:
- Henry de Valence <hdevalence@hdevalence.ca>

Precomputation for Straus's method.

We could save some doublings by looking for the highest
nonzero NAF coefficient, but since we might have a lot of
them to search, it's not clear it's worthwhile to check.

## src/backend/vector/scalar_mul/straus.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Multiscalar multiplication using interleaved window / Straus'
method.  See the `Straus` struct in the serial backend for more
details.

This exists as a separate implementation from that one because the
AVX2 code uses different curve models (it does not pass between
multiple models during scalar mul), and it has to convert the
point representation on the fly.
Construct a lookup table of [P,2P,3P,4P,5P,6P,7P,8P]
for each input point P
Pass ownership to a `Zeroizing` wrapper
Q = Q + s_{i,j} * P_i

## src/backend/vector/scalar_mul/variable_base.rs


Perform constant-time, variable-base scalar multiplication.

Construct a lookup table of [P,2P,3P,4P,5P,6P,7P,8P]

Setting s = scalar, compute

s = s_0 + s_1*16^1 + ... + s_63*16^63,

with `-8 ≤ s_i < 8` for `0 ≤ i < 63` and `-8 ≤ s_63 ≤ 8`.

Compute s*P as

s*P = P*(s_0 +   s_1*16^1 +   s_2*16^2 + ... +   s_63*16^63)
s*P =  P*s_0 + P*s_1*16^1 + P*s_2*16^2 + ... + P*s_63*16^63
s*P = P*s_0 + 16*(P*s_1 + 16*(P*s_2 + 16*( ... + P*s_63)...))

We sum right-to-left.

## src/backend/vector/scalar_mul/vartime_double_base.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Compute $aA + bB$ in variable time, where $B$ is the Ed25519 basepoint.

Find starting index

## src/common_verus.rs

This module provides functionality for...

Currently contains verus code which is required in several places.


Evaluation function, given a field element as limbs, reconstruct the nat value it represents.
This also appears in `curve25519-dalek/src/backend/serial/u64/field_lemmas.rs`, to be combined.

## src/constants.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>
Various constants, such as the Ristretto and Ed25519 basepoints.

The Ed25519 basepoint, in `CompressedEdwardsY` format.

This is the little-endian byte encoding of $ 4/5 \pmod p $,
which is the $y$-coordinate of the Ed25519 basepoint.

The sign bit is 0 since the basepoint has $x$ chosen to be positive.

The X25519 basepoint, in `MontgomeryPoint` format.

The Ristretto basepoint, in `CompressedRistretto` format.

The Ristretto basepoint, as a `RistrettoPoint`.

This is called `_POINT` to distinguish it from `_TABLE`, which
provides fast scalar multiplication.

`BASEPOINT_ORDER` is the order of the Ristretto group and of the Ed25519 basepoint, i.e.,
$$
\ell = 2^\{252\} + 27742317777372353535851937790883648493.
$$

The Ristretto basepoint, as a `RistrettoBasepointTable` for scalar multiplication.
SAFETY: `RistrettoBasepointTable` is a `#[repr(transparent)]` newtype of
`EdwardsBasepointTable`

Test that SQRT_M1 is the positive square root of -1

Test that d = -121665/121666

Test that d = -121665/121666

Test that ED25519_SQRTAM2 squared is MONTGOMERY_A_NEG - 2

## src/diagnostics.rs

Build time diagnostics

auto is assumed or selected

fiat was overridden

serial was assumed or overridden

simd was assumed over overridden

32 bits target_pointer_width was assumed or overridden

64 bits target_pointer_width was assumed or overridden

## src/edwards.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2020 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Group operations for Curve25519, in Edwards form.

#### Encoding and Decoding

Encoding is done by converting to and from a `CompressedEdwardsY`
struct, which is a typed wrapper around `[u8; 32]`.

#### Equality Testing

The `EdwardsPoint` struct implements the [`subtle::ConstantTimeEq`]
trait for constant-time equality checking, and also uses this to
ensure `Eq` equality checking runs in constant time.

#### Cofactor-related functions

The order of the group of points on the curve $\mathcal E$
is $|\mathcal E| = 8\ell $, so its structure is $ \mathcal
E = \mathcal E\[8\] \times \mathcal E[\ell]$.  The torsion
subgroup $ \mathcal E\[8\] $ consists of eight points of small
order.  Technically, all of $\mathcal E$ is torsion, but we
use the word only to refer to the small $\mathcal E\[8\]$ part, not
the large prime-order $\mathcal E[\ell]$ part.

To test if a point is in $ \mathcal E\[8\] $, use
[`EdwardsPoint::is_small_order`].

To test if a point is in $ \mathcal E[\ell] $, use
[`EdwardsPoint::is_torsion_free`].

To multiply by the cofactor, use [`EdwardsPoint::mul_by_cofactor`].

To avoid dealing with cofactors entirely, consider using Ristretto.

#### Scalars

Scalars are represented by the [`Scalar`] struct. To construct a scalar, see
[`Scalar::from_canonical_bytes`] or [`Scalar::from_bytes_mod_order_wide`].

#### Scalar Multiplication

Scalar multiplication on Edwards points is provided by:

* the `*` operator between a `Scalar` and a `EdwardsPoint`, which
performs constant-time variable-base scalar multiplication;

* the `*` operator between a `Scalar` and a
`EdwardsBasepointTable`, which performs constant-time fixed-base
scalar multiplication;

* an implementation of the
[`MultiscalarMul`](../traits/trait.MultiscalarMul.html) trait for
constant-time variable-base multiscalar multiplication;

* an implementation of the
[`VartimeMultiscalarMul`](../traits/trait.VartimeMultiscalarMul.html)
trait for variable-time variable-base multiscalar multiplication;

#### Implementation

The Edwards arithmetic is implemented using the “extended twisted
coordinates” of Hisil, Wong, Carter, and Dawson, and the
corresponding complete formulas.  For more details,
see the [`curve_models` submodule][curve_models]
of the internal documentation.

#### Validity Checking

There is no function for checking whether a point is valid.
Instead, the `EdwardsPoint` struct is guaranteed to hold a valid
point on the curve.

We use the Rust type system to make invalid points
unrepresentable: `EdwardsPoint` objects can only be created via
successful decompression of a compressed point, or else by
operations on other (valid) `EdwardsPoint`s.

[curve_models]: https://docs.rs/curve25519-dalek/latest/curve25519-dalek/backend/serial/curve_models/index.html

We allow non snake_case names because coordinates in projective space are
traditionally denoted by the capitalisation of their respective
counterparts in affine space.  Yeah, you heard me, rustc, I'm gonna have my
affine and projective cakes and eat both of them too.

### Compressed points

In "Edwards y" / "Ed25519" format, the curve point $(x,y)$ is
determined by the $y$-coordinate and the sign of $x$.

The first 255 bits of a `CompressedEdwardsY` represent the
$y$-coordinate.  The high bit of the 32nd byte gives the sign of $x$.
View this `CompressedEdwardsY` as an array of bytes.

Copy this `CompressedEdwardsY` to an array of bytes.

Attempt to decompress to an `EdwardsPoint`.

Returns `None` if the input is not the $y$-coordinate of a
curve point.
FieldElement::sqrt_ratio_i always returns the nonnegative square root,
so we negate according to the supplied sign bit.

### Serde support
Serializes to and from `EdwardsPoint` directly, doing compression
and decompression internally.  This means that users can create
structs containing `EdwardsPoint`s and use Serde's derived
serializers to serialize those structures.

### Internal point representations

An `EdwardsPoint` represents a point on the Edwards form of Curve25519.

### Constructors
Construct a `CompressedEdwardsY` from a slice of bytes.

### Errors

Returns [`TryFromSliceError`] if the input `bytes` slice does not have
a length of 32.

### Zeroize implementations for wiping points from memory
Reset this `CompressedEdwardsY` to the compressed form of the identity element.
Reset this `EdwardsPoint` to the identity element.

### Validity checks (for debugging, not CT)

### Constant-time assignment

### Equality
We would like to check that the point (X/Z, Y/Z) is equal to
the point (X'/Z', Y'/Z') without converting into affine
coordinates (x, y) and (x', y'), which requires two inversions.
We have that X = xZ and X' = x'Z'. Thus, x = x' is equivalent to
(xZ)Z' = (x'Z')Z, and similarly for the y-coordinate.

### Point conversions
Convert to a ProjectiveNielsPoint

Convert the representation of this point from extended
coordinates to projective coordinates.

Free.

Dehomogenize to a `AffineNielsPoint`.
Mainly for testing.

Dehomogenize to `AffinePoint`.

Convert this `EdwardsPoint` on the Edwards model to the
corresponding `MontgomeryPoint` on the Montgomery model.

This function has one exceptional case; the identity point of
the Edwards curve is sent to the 2-torsion point $(0,0)$
on the Montgomery curve.

Note that this is a one-way conversion, since the Montgomery
model does not retain sign information.

We have u = (1+y)/(1-y) = (Z+Y)/(Z-Y).

The denominator is zero only when y=1, the identity point of
the Edwards curve.  Since 0.invert() = 0, in this case we
compute the 2-torsion point (0,0).

Converts a large batch of points to Edwards at once. This has the same
behavior on identity elements as [`Self::to_montgomery`].
Do the same thing as the above function. u = (1+y)/(1-y) = (Z+Y)/(Z-Y).
We will do this in a batch, ie compute (Z-Y) for all the input
points, then invert them all at once

Compute the denominators in a batch

Now compute the Montgomery u coordinate for every point

Compress this point to `CompressedEdwardsY` format.

Compress several `EdwardsPoint`s into `CompressedEdwardsY` format, using a batch inversion
for a significant speedup.
Perform hashing to curve, with explicit hash function and domain separator, `domain_sep`,
using the suite `edwards25519_XMD:SHA-512_ELL2_NU_`. The input is the concatenation of the
elements of `bytes`. Likewise for the domain separator with `domain_sep`. At least one
element of `domain_sep`, MUST be nonempty, and the concatenation MUST NOT exceed
255 bytes.

### Panics
Panics if `domain_sep.collect().len() == 0` or `> 255`
For reference see
https://www.rfc-editor.org/rfc/rfc9380.html#name-elligator-2-method-2

The `to_edwards` conversion we're performing takes as input the sign of the Edwards
`y` coordinate. However, the specification uses `is_sq` to determine the sign of the
Montgomery `v` coordinate. Our approach reconciles this mismatch as follows:

* We arbitrarily fix the sign of the Edwards `y` coordinate (we choose 0).
* Using the Montgomery `u` coordinate and the Edwards `X` coordinate, we recover `v`.
* We verify that the sign of `v` matches the expected one, i.e., `is_sq == mont_v.is_negative()`.
* If it does not match, we conditionally negate to correct the sign.

Note: This logic aligns with the RFC draft specification:
https://www.rfc-editor.org/rfc/rfc9380.html#name-elligator-2-method-2
followed by the mapping
https://www.rfc-editor.org/rfc/rfc9380.html#name-mappings-for-twisted-edward
The only difference is that our `elligator_encode` returns only the Montgomery `u` coordinate,
so we apply this workaround to reconstruct and validate the sign.

Now we recover v, to ensure that we got the sign right.

Return an `EdwardsPoint` chosen uniformly at random using a user-provided RNG.

### Inputs

* `rng`: any RNG which implements `RngCore`

### Returns

A random `EdwardsPoint`.

### Implementation

Uses rejection sampling, generating a random `CompressedEdwardsY` and then attempting point
decompression, rejecting invalid points.

### Doubling
Add this point to itself.

### Addition and Subtraction

### Negation

### Scalar multiplication
Scalar multiplication: compute `scalar * self`.

For scalar multiplication of a basepoint,
`EdwardsBasepointTable` is approximately 4x faster.

Scalar multiplication: compute `scalar * self`.

For scalar multiplication of a basepoint,
`EdwardsBasepointTable` is approximately 4x faster.
Fixed-base scalar multiplication by the Ed25519 base point.

Uses precomputed basepoint tables when the `precomputed-tables` feature
is enabled, trading off increased code size for ~4x better performance.

Multiply this point by `clamp_integer(bytes)`. For a description of clamping, see
[`clamp_integer`].

We have to construct a Scalar that is not reduced mod l, which breaks scalar invariant
###2. But #2 is not necessary for correctness of variable-base multiplication. All that
needs to hold is invariant #1, i.e., the scalar is less than 2^255. This is guaranteed
by clamping.
Further, we don't do any reduction or arithmetic with this clamped value, so there's no
issues arising from the fact that the curve point is not necessarily in the prime-order
subgroup.

Multiply the basepoint by `clamp_integer(bytes)`. For a description of clamping, see
[`clamp_integer`].

See reasoning in Self::mul_clamped why it is OK to make an unreduced Scalar here. We
note that fixed-base multiplication is also defined for all values of `bytes` less than
2^255.

### Multiscalar Multiplication impls

These use the iterator's size hint and the target settings to
forward to a specific backend implementation.
Sanity-check lengths of input iterators

Lower and upper bounds on iterators

They should all be equal

Now we know there's a single size.  When we do
size-dependent algorithm dispatch, use this as the hint.
Sanity-check lengths of input iterators

Lower and upper bounds on iterators

They should all be equal

Now we know there's a single size.
Use this as the hint to decide which algorithm to use.

Precomputation for variable-time multiscalar multiplication with `EdwardsPoint`s.
This wraps the inner implementation in a facade type so that we can
decouple stability of the inner type from the stability of the
outer type.
Compute $aA + bB$ in variable time, where $B$ is the Ed25519 basepoint.
A precomputed table of multiples of a basepoint, for accelerating
fixed-base scalar multiplication.  One table, for the Ed25519
basepoint, is provided in the [`constants`] module.

The basepoint tables are reasonably large, so they should probably be boxed.

The sizes for the tables and the number of additions required for one scalar
multiplication are as follows:

* [`EdwardsBasepointTableRadix16`]: 30KB, 64A
(this is the default size, and is used for
[`constants::ED25519_BASEPOINT_TABLE`])
* [`EdwardsBasepointTableRadix64`]: 120KB, 43A
* [`EdwardsBasepointTableRadix128`]: 240KB, 37A
* [`EdwardsBasepointTableRadix256`]: 480KB, 33A

### Why 33 additions for radix-256?

Normally, the radix-256 tables would allow for only 32 additions per scalar
multiplication.  However, due to the fact that standardised definitions of
legacy protocols—such as x25519—require allowing unreduced 255-bit scalars
invariants, when converting such an unreduced scalar's representation to
radix-$2^{8}$, we cannot guarantee the carry bit will fit in the last
coefficient (the coefficients are `i8`s).  When, $w$, the power-of-2 of
the radix, is $w < 8$, we can fold the final carry onto the last
coefficient, $d$, because $d < 2^{w/2}$, so
$$
d + carry \cdot 2^{w} = d + 1 \cdot 2^{w} < 2^{w+1} < 2^{8}
$$
When $w = 8$, we can't fit $carry \cdot 2^{w}$ into an `i8`, so we
add the carry bit onto an additional coefficient.

Create a table of precomputed multiples of `basepoint`.

XXX use init_with
P = (2w)^i * B

Get the basepoint for this table as an `EdwardsPoint`.

self.0[0].select(1) = 1*(16^2)^0*B
but as an `AffineNielsPoint`, so add identity to convert to extended.

The computation uses Pippeneger's algorithm, as described for the
specific case of radix-16 on page 13 of the Ed25519 paper.

### Piggenger's Algorithm Generalised

Write the scalar $a$ in radix-$w$, where $w$ is a power of
2, with coefficients in $[\frac{-w}{2},\frac{w}{2})$, i.e.,
$$
a = a_0 + a_1 w^1 + \cdots + a_{x} w^{x},
$$
with
$$
\begin{aligned}
\frac{-w}{2} \leq a_i < \frac{w}{2}
&&\cdots&&
\frac{-w}{2} \leq a_{x} \leq \frac{w}{2}
\end{aligned}
$$
and the number of additions, $x$, is given by
$x = \lceil \frac{256}{w} \rceil$. Then
$$
a B = a_0 B + a_1 w^1 B + \cdots + a_{x-1} w^{x-1} B.
$$
Grouping even and odd coefficients gives
$$
\begin{aligned}
a B = \quad a_0 w^0 B +& a_2 w^2 B + \cdots + a_{x-2} w^{x-2} B    \\\\
+ a_1 w^1 B +& a_3 w^3 B + \cdots + a_{x-1} w^{x-1} B    \\\\
= \quad(a_0 w^0 B +& a_2 w^2 B + \cdots + a_{x-2} w^{x-2} B)   \\\\
+ w(a_1 w^0 B +& a_3 w^2 B + \cdots + a_{x-1} w^{x-2} B).  \\\\
\end{aligned}
$$
For each $i = 0 \ldots 31$, we create a lookup table of
$$
[w^{2i} B, \ldots, \frac{w}{2}\cdot w^{2i} B],
$$
and use it to select $ y \cdot w^{2i} \cdot B $ in constant time.

The radix-$w$ representation requires that the scalar is bounded
by $2^{255}$, which is always the case.

The above algorithm is trivially generalised to other powers-of-2 radices.

Construct an `EdwardsPoint` from a `Scalar` $a$ by
computing the multiple $aB$ of this basepoint $B$.

delegate to a private function so that its documentation appears in internal docs

Construct an `EdwardsPoint` from a `Scalar` $a$ by
computing the multiple $aB$ of this basepoint $B$.

The number of additions required is ceil(256/w) where w is the radix representation.

A type-alias for [`EdwardsBasepointTable`] because the latter is
used as a constructor in the [`constants`] module.

Same as for `LookupTableRadix16`, we have to define `EdwardsBasepointTable`
first, because it's used as a constructor, and then provide a type alias for
it.
Conversions from radix 16

Conversions from radix 32

Conversions from radix 64

Conversions from radix 128
Multiply by the cofactor: return $\[8\]P$.

Compute $[2^k] P $ by successive doublings. Requires $ k > 0 $.
Unroll last iteration so we can go directly as_extended()

Determine if this point is of small order.

### Return

* `true` if `self` is in the torsion subgroup $ \mathcal E\[8\] $;
* `false` if `self` is not in the torsion subgroup $ \mathcal E\[8\] $.

### Example

```
use curve25519_dalek::constants;

// Generator of the prime-order subgroup
let P = constants::ED25519_BASEPOINT_POINT;
// Generator of the torsion subgroup
let Q = constants::EIGHT_TORSION[1];

// P has large order
assert_eq!(P.is_small_order(), false);

// Q has small order
assert_eq!(Q.is_small_order(), true);
```

Determine if this point is “torsion-free”, i.e., is contained in
the prime-order subgroup.

### Return

* `true` if `self` has zero torsion component and is in the
prime-order subgroup;
* `false` if `self` has a nonzero torsion component and is not
in the prime-order subgroup.

### Example

```
use curve25519_dalek::constants;

// Generator of the prime-order subgroup
let P = constants::ED25519_BASEPOINT_POINT;
// Generator of the torsion subgroup
let Q = constants::EIGHT_TORSION[1];

// P is torsion-free
assert_eq!(P.is_torsion_free(), true);

// P + Q is not torsion-free
assert_eq!((P+Q).is_torsion_free(), false);
```

### Debug traits

### group traits

Use the full trait path to avoid Group::identity overlapping Identity::identity in the
rest of the module (e.g. tests).
Just use the checked API; there are no checks we can skip.

A `SubgroupPoint` represents a point on the Edwards form of Curve25519, that is
guaranteed to be in the prime-order subgroup.

Scalar multiplication: compute `scalar * self`.

For scalar multiplication of a basepoint,
`EdwardsBasepointTable` is approximately 4x faster.

Scalar multiplication: compute `scalar * self`.

For scalar multiplication of a basepoint,
`EdwardsBasepointTable` is approximately 4x faster.

This will almost never loop, but `Group::random` is documented as returning a
non-identity element.

This gives an element of the prime-order subgroup.

### Tests

X coordinate of the basepoint.
= 15112221349535400772501151409588531511454012693041857206046113283949847762202

Compressed Edwards Y form of 2*basepoint.

Compressed Edwards Y form of 16*basepoint.

4493907448824000747700850167940867464579944529806937181821189941592931634714

2506056684125797857694181776241676200180934651973138769173342316833279714961

A_SCALAR * basepoint, computed with ed25519.py

A_SCALAR * (A_TIMES_BASEPOINT) + B_SCALAR * BASEPOINT
computed with ed25519.py

Test round-trip decompression for the basepoint.
Check that decompression actually gives the correct X coordinate

Test sign handling in decompression
Manually set the high bit of the last byte to flip the sign
Test projective coordinates exactly since we know they should
only differ by a flipped sign.

Test that computing 1*basepoint gives the correct basepoint.

Test that `EdwardsBasepointTable::basepoint()` gives the correct basepoint.

Test `impl Add<EdwardsPoint> for EdwardsPoint`
using basepoint + basepoint versus the 2*basepoint constant.

Test `impl Add<ProjectiveNielsPoint> for EdwardsPoint`
using the basepoint, basepoint2 constants

Test `impl Add<AffineNielsPoint> for EdwardsPoint`
using the basepoint, basepoint2 constants

Check that equality of `EdwardsPoints` handles projective
coordinates correctly.

Sanity check for conversion to precomputed points
construct a point as aB so it has denominators (ie. Z != 1)

Test mul_base versus a known scalar multiple from ed25519.py

Test that multiplication by the basepoint order kills the basepoint

Test precomputed basepoint mult

Test scalar_mul versus a known scalar multiple from ed25519.py

Test basepoint.double() versus the 2*basepoint constant.

Test that computing 2*basepoint is the same as basepoint.double()

Test that all the basepoint table types compute the same results.

Check unreduced scalar multiplication by the basepoint tables is the same no matter what
radix the table is.

Check that converting to projective and then back to extended round-trips.

Test computing 16*basepoint vs mul_by_pow_2(4)

Check that mul_base_clamped and mul_clamped agree

Make a random curve point in the curve. Give it torsion to make things interesting.
Make a basepoint table from the random point. We'll use this with mul_base_clamped

Now test scalar mult. agreement on the default basepoint as well as random_point

Test that mul_base_clamped and mul_clamped agree on a large integer. Even after
clamping, this integer is not reduced mod l.

Test agreement on random integers

This will be reduced mod l with probability l / 2^256 ≈ 6.25%
Test that sum works for non-empty iterators

Test that sum works for the empty iterator

Test that sum works on owning iterators

Test that the conditional assignment trait works for AffineNielsPoints.
The basepoint has large prime order

constants::EIGHT_TORSION has all points of small order.

TODO(tarcieri): proptests?
Make some points deterministically then randomly

Check that the batch-compressed points match the individually compressed ones

Rust's debug builds have overflow and underflow trapping,
and enable `debug_assert!()`.  This performs many scalar
multiplications to attempt to trigger possible overflows etc.

For instance, the `u64` `Mul` implementation for
`FieldElements` requires the input `Limb`s to be bounded by
2^54, but we cannot enforce this dynamically at runtime, or
statically at compile time (until Rust gets type-level
integers, at which point we can encode "bits of headroom" into
the type system and prove correctness).
N.B. each scalar_mul does 1407 field mults, 1024 field squarings,
so this does ~ 1M of each operation.

A single iteration of a consistency check for MSM.

Construct random coefficients x0, ..., x_{n-1},
followed by some extra hardcoded ones.

Construct points G_i = x_i * B

Compute H1 = <xs, Gs> (consttime)

Compute H2 = <xs, Gs> (vartime)

Compute H3 = <xs, Gs> = sum(xi^2) * B

Use different multiscalar sizes to hit different internal
parameters.

Test double_scalar_mul_vartime vs ed25519.py

Check that the encoding is 32 bytes exactly

Check that the encoding itself matches the usual one

Hash-to-curve test vectors from
https://www.rfc-editor.org/rfc/rfc9380.html#name-edwards25519_xmdsha-512_ell2
These are of the form (input_msg, output_x, output_y)

## src/edwards/affine.rs


Affine Edwards point on untwisted curve.
Convert to extended coordinates.

Compress affine Edwards coordinates into `CompressedEdwardsY` format.

## src/field.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis agora lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- Isis Agora Lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Field arithmetic modulo $p = 2^{255} - 19$.

The `curve25519_dalek::field` module provides a type alias
`curve25519_dalek::field::FieldElement` to a field element type
defined in the `backend` module; either `FieldElement51` or
`FieldElement2625`.

Field operations defined in terms of machine
operations, such as field multiplication or squaring, are defined in
the backend implementation.

Field operations defined in terms of other field operations, such as
field inversion or square roots, are defined here.
A `FieldElement` represents an element of the field
$ \mathbb Z / (2^{255} - 19)$.

The `FieldElement` type is an alias for one of the platform-specific
implementations.

Using formally-verified field arithmetic from fiat-crypto.

A `FieldElement` represents an element of the field
$ \mathbb Z / (2^{255} - 19)$.

The `FieldElement` type is an alias for one of the platform-specific
implementations.

Using formally-verified field arithmetic from fiat-crypto.
A `FieldElement` represents an element of the field
$ \mathbb Z / (2^{255} - 19)$.

The `FieldElement` type is an alias for one of the platform-specific
implementations.
A `FieldElement` represents an element of the field
$ \mathbb Z / (2^{255} - 19)$.

The `FieldElement` type is an alias for one of the platform-specific
implementations.
Test equality between two `FieldElement`s.  Since the
internal representation is not canonical, the field elements
are normalized to wire format before comparison.
Load a `FieldElement` from 64 bytes, by reducing modulo q.
Mask off the top bits of both halves, since from_bytes masks them off anyway. We'll add
them back in later.

Interpret both sides as field elements

The full field elem is now fe_f + 2²⁵⁵ fl_top_bit + 2²⁵⁶ fe_g + 2⁵¹¹ gl_top_bit

Add the masked off bits back to fe_f. fl_top_bit, if set, is 2^255 ≡ 19 (mod q).
gl_top_bit, if set, is 2^511 ≡ 722 (mod q)

This only need to be a u16 because the max value is 741

Now add the high half into fe_f. The RHS is multiplied by 2^256 ≡ 38 (mod q)

Determine if this `FieldElement` is negative, in the sense
used in the ed25519 paper: `x` is negative if the low bit is
set.

### Return

If negative, return `Choice(1)`.  Otherwise, return `Choice(0)`.

Determine if this `FieldElement` is zero.

### Return

If zero, return `Choice(1)`.  Otherwise, return `Choice(0)`.

Compute (self^(2^250-1), self^11), used as a helper function
within invert() and pow22523().
Instead of managing which temporary variables are used
for what, we define as many as we need and leave stack
allocation to the compiler

Each temporary variable t_i is of the form (self)^e_i.
Squaring t_i corresponds to multiplying e_i by 2,
so the pow2k function shifts e_i left by k places.
Multiplying t_i and t_j corresponds to adding e_i + e_j.

Temporary t_i                      Nonzero bits of e_i


Given a slice of pub(crate)lic `FieldElements`, replace each with its inverse.

When an input `FieldElement` is zero, its value is unchanged.
Montgomery’s Trick and Fast Implementation of Masked AES
Genelle, Prouff and Quisquater
Section 3.2

Keep an accumulator of all of the previous products

Pass through the input vector, recording the previous
products in the scratch space
acc <- acc * input, but skipping zeros (constant-time)

acc is nonzero because we skipped zeros in inputs

Compute the inverse of all products

Pass through the vector backwards to compute the inverses
in place
input <- acc * scratch, then acc <- tmp
Again, we skip zeros in a constant-time way

Given a nonzero field element, compute its inverse.

The inverse is computed as self^(p-2), since
x^(p-2)x = x^(p-1) = 1 (mod p).

This function returns zero on input zero.
The bits of p-2 = 2^255 -19 -2 are 11010111111...11.

nonzero bits of exponent

Raise this field element to the power (p-5)/8 = 2^252 -3.
The bits of (p-5)/8 are 101111.....11.

nonzero bits of exponent

Given `FieldElements` `u` and `v`, compute either `sqrt(u/v)`
or `sqrt(i*u/v)` in constant time.

This function always returns the nonnegative square root.

### Return

- `(Choice(1), +sqrt(u/v))  ` if `v` is nonzero and `u/v` is square;
- `(Choice(1), zero)        ` if `u` is zero;
- `(Choice(0), zero)        ` if `v` is zero and `u` is nonzero;
- `(Choice(0), +sqrt(i*u/v))` if `u/v` is nonsquare (so `i*u/v` is square).


Using the same trick as in ed25519 decoding, we merge the
inversion, the square root, and the square test as follows.

To compute sqrt(α), we can compute β = α^((p+3)/8).
Then β^2 = ±α, so multiplying β by sqrt(-1) if necessary
gives sqrt(α).

To compute 1/sqrt(α), we observe that
1/β = α^(p-1 - (p+3)/8) = α^((7p-11)/8)
= α^3 * (α^7)^((p-5)/8).

We can therefore compute sqrt(u/v) = sqrt(u)/sqrt(v)
by first computing
r = u^((p+3)/8) v^(p-1-(p+3)/8)
= u u^((p-5)/8) v^3 (v^7)^((p-5)/8)
= (uv^3) (uv^7)^((p-5)/8).

If v is nonzero and u/v is square, then r^2 = ±u/v,
so vr^2 = ±u.
If vr^2 =  u, then sqrt(u/v) = r.
If vr^2 = -u, then sqrt(u/v) = r*sqrt(-1).

If v is zero, r is also zero.

Choose the nonnegative square root.

Attempt to compute `sqrt(1/self)` in constant time.

Convenience wrapper around `sqrt_ratio_i`.

This function always returns the nonnegative square root.

### Return

- `(Choice(1), +sqrt(1/self))  ` if `self` is a nonzero square;
- `(Choice(0), zero)           ` if `self` is zero;
- `(Choice(0), +sqrt(i/self))  ` if `self` is a nonzero nonsquare;

Perform hashing to a [`FieldElement`], per the
[`hash_to_curve`](https://www.rfc-editor.org/rfc/rfc9380.html#section-5.2) specification.
Uses the suite `edwards25519_XMD:SHA-512_ELL2_NU_`. The input is the concatenation of the
elements of `bytes`. Likewise for the domain separator with `domain_sep`. At least one
element of `domain_sep`, MUST be nonempty, and the concatenation MUST NOT exceed 255 bytes.

### Panics
Panics if `domain_sep.collect().len() == 0` or `> 255`

§5.2, we only generate count * m * L = 1 * 1 * (256 + 128)/8 = 48 bytes

Random element a of GF(2^255-19), from Sage
a = 1070314506888354081329385823235218444233221\
2228051251926706380353716438957572

Byte representation of a**2

Byte representation of 1/a

Byte representation of a^((p-5)/8)

0/0 should return (1, 0) since u is 0

1/0 should return (0, 0) since v is 0, u is nonzero

2/1 is nonsquare, so we expect (0, sqrt(i*2))

4/1 is square, so we expect (1, sqrt(4))

1/4 is square, so we expect (1, 1/sqrt(4))

Notice that the last element has the high bit set, which
should be ignored
Encode 1 wrongly as 1 + (2^255 - 19) = 2^255 - 18
Decode to a field element

.. then check that the encoding is correct

The following two consts were generated with the following sage script:

import random

F = GF(2**255 - 19)
### Use a seed to make sure we produce the same test vectors every time
random.seed("Ozamataz Buckshank")

### Generates test vectors, each of the form (input_bytes, reduced_field_elem_bytes),
### where input_bytes is length input_bytes_len
def gen_example(input_bytes_len):
### Generate random bytes
input_bytes = [random.randint(0, 255) for _ in range(input_bytes_len)]

### Now convert to a field element and get the reduced byte representation
elem = F(int.from_bytes(input_bytes, byteorder='little'))
reduced_bytes = list(int(elem).to_bytes(32, byteorder='little'))

### Format input and output as hex strings
input_bytes_hex = ''.join(f'{byte:02x}' for byte in input_bytes)
reduced_bytes_hex = ''.join(f'{byte:02x}' for byte in reduced_bytes)
return f"(\"{input_bytes_hex}\", \"{reduced_bytes_hex}\")"

print("SET 1: Input bytes are length 64")
for _ in range(5):
print(gen_example(64))

print("SET 2: Input bytes are length 48")
for _ in range(5):
print(gen_example(48))

Test vectors for FieldElement::from_bytes_wide. Elements are of the form (len-64 bytestring,
reduced field element)

Test vectors for FieldElement::from_bytes_wide. Elements are of the form (len-48 bytestring,
reduced field element)
Do the 64-byte input ones first

Now do the 48-byte inputs

Hash to field test vectors from
https://www.rfc-editor.org/rfc/rfc9380.html#name-edwards25519_xmdsha-512_ell2
These are of the form (input_msg, output_field_elem)

## src/lib.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>
### Documentation:
### Linting:

### External dependencies:

TODO: move std-dependent tests to `tests/`

Internal macros. Must come first!

### curve25519-dalek public modules

Scalar arithmetic mod l = 2^252 + ..., the order of the Ristretto group

Point operations on the Montgomery form of Curve25519

Point operations on the Edwards form of Curve25519

Group operations on the Ristretto group

Useful constants, like the Ed25519 basepoint

External (and internal) traits.

Verus

### curve25519-dalek internal modules

Finite field arithmetic mod p = 2^255 - 19

Arithmetic backends (using u32, u64, etc) live here

Generic code for window lookups

Build time diagnostics for validation

## src/macros.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis agora lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Internal macros.

Define borrow and non-borrow variants of `Add`.

Define non-borrow variants of `AddAssign`.

Define borrow and non-borrow variants of `Sub`.

Define non-borrow variants of `SubAssign`.

Define borrow and non-borrow variants of `Mul`.

Define non-borrow variants of `MulAssign`.

## src/montgomery.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Scalar multiplication on the Montgomery form of Curve25519.

To avoid notational confusion with the Edwards code, we use
variables $ u, v $ for the Montgomery curve, so that “Montgomery
$u$” here corresponds to “Montgomery $x$” elsewhere.

Montgomery arithmetic works not on the curve itself, but on the
$u$-line, which discards sign information and unifies the curve
and its quadratic twist.  See [_Montgomery curves and their
arithmetic_][costello-smith] by Costello and Smith for more details.

The `MontgomeryPoint` struct contains the affine $u$-coordinate
$u_0(P)$ of a point $P$ on either the curve or the twist.
Here the map $u_0 : \mathcal M \rightarrow \mathbb F_p $ is
defined by $u_0((u,v)) = u$; $u_0(\mathcal O) = 0$.  See
section 5.4 of Costello-Smith for more details.

### Scalar Multiplication

Scalar multiplication on `MontgomeryPoint`s is provided by the `*`
operator, which implements the Montgomery ladder.

### Edwards Conversion

The $2$-to-$1$ map from the Edwards model to the Montgomery
$u$-line is provided by `EdwardsPoint::to_montgomery()`.

To lift a `MontgomeryPoint` to an `EdwardsPoint`, use
`MontgomeryPoint::to_edwards()`, which takes a sign parameter.
This function rejects `MontgomeryPoints` which correspond to points
on the twist.

[costello-smith]: https://eprint.iacr.org/2017/212.pdf

We allow non snake_case names because coordinates in projective space are
traditionally denoted by the capitalisation of their respective
counterparts in affine space.  Yeah, you heard me, rustc, I'm gonna have my
affine and projective cakes and eat both of them too.

Holds the $u$-coordinate of a point on the Montgomery form of
Curve25519 or its twist.

Equality of `MontgomeryPoint`s is defined mod p.

Equal MontgomeryPoints must hash to the same value. So we have to get them into a canonical
encoding first
Do a round trip through a `FieldElement`. `as_bytes` is guaranteed to give a canonical
32-byte encoding
Return the group identity element, which has order 4.
Fixed-base scalar multiplication (i.e. multiplication by the base point).

Multiply this point by `clamp_integer(bytes)`. For a description of clamping, see
[`clamp_integer`].

We have to construct a Scalar that is not reduced mod l, which breaks scalar invariant
###2. But #2 is not necessary for correctness of variable-base multiplication. All that
needs to hold is invariant #1, i.e., the scalar is less than 2^255. This is guaranteed
by clamping.
Further, we don't do any reduction or arithmetic with this clamped value, so there's no
issues arising from the fact that the curve point is not necessarily in the prime-order
subgroup.

Multiply the basepoint by `clamp_integer(bytes)`. For a description of clamping, see
[`clamp_integer`].

See reasoning in Self::mul_clamped why it is OK to make an unreduced Scalar here. We
note that fixed-base multiplication is also defined for all values of `bytes` less than
2^255.

Given `self` $ = u_0(P) $, and a big-endian bit representation of an integer
$n$, return $ u_0(\[n\]P) $. This is constant time in the length of `bits`.

**NOTE:** You probably do not want to use this function. Almost every protocol built on
Curve25519 uses _clamped multiplication_, explained
[here](https://neilmadden.blog/2020/05/28/whats-the-curve25519-clamping-all-about/).
When in doubt, use [`Self::mul_clamped`].

Algorithm 8 of Costello-Smith 2017

Go through the bits from most to least significant, using a sliding window of 2
The final value of prev_bit above is scalar.bits()[0], i.e., the LSB of scalar

Don't leave the bit in the stack

View this `MontgomeryPoint` as an array of bytes.

Convert this `MontgomeryPoint` to an array of bytes.

Attempt to convert to an `EdwardsPoint`, using the supplied
choice of sign for the `EdwardsPoint`.

### Inputs

* `sign`: a `u8` donating the desired sign of the resulting
`EdwardsPoint`.  `0` denotes positive and `1` negative.

### Return

* `Some(EdwardsPoint)` if `self` is the $u$-coordinate of a
point on (the Montgomery form of) Curve25519;

* `None` if `self` is the $u$-coordinate of a point on the
twist of (the Montgomery form of) Curve25519;


To decompress the Montgomery u coordinate to an
`EdwardsPoint`, we apply the birational map to obtain the
Edwards y coordinate, then do Edwards decompression.

The birational map is y = (u-1)/(u+1).

The exceptional points are the zeros of the denominator,
i.e., u = -1.

But when u = -1, v^2 = u*(u^2+486662*u+1) = 486660.

Since this is nonsquare mod p, u = -1 corresponds to a point
on the twist, not the curve, so we can reject it early.

Perform the Elligator2 mapping to a Montgomery point. Returns a Montgomery point and a `Choice`
determining whether eps is a square. This is required by the standard to determine the
sign of the v coordinate.

See <https://www.rfc-editor.org/rfc/rfc9380.html#name-elligator-2-method>

2r^2

A/(1+2r^2)
eps = d^3 + Ad^2 + d
0, or A if nonsquare
d, or d+A if nonsquare
d, or -d-A if nonsquare

A `ProjectivePoint` holds a point on the projective line
$ \mathbb P(\mathbb F_p) $, which we identify with the Kummer
line of the Montgomery curve.
Dehomogenize this point to affine coordinates.

### Return

* $ u = U / W $ if $ W \neq 0 $;
* $ 0 $ if $ W \eq 0 $;

Perform the double-and-add step of the Montgomery ladder.

Given projective points
$ (U_P : W_P) = u(P) $,
$ (U_Q : W_Q) = u(Q) $,
and the affine difference
$      u_{P-Q} = u(P-Q) $, set
$$
(U_P : W_P) \gets u(\[2\]P)
$$
and
$$
(U_Q : W_Q) \gets u(P + Q).
$$

Multiply this `MontgomeryPoint` by a `Scalar`.

Given `self` $ = u_0(P) $, and a `Scalar` $n$, return $ u_0(\[n\]P) $

We multiply by the integer representation of the given Scalar. By scalar invariant #1,
the MSB is 0, so we can skip it.

### Tests

Test Montgomery -> Edwards on the X/Ed25519 basepoint
sign bit = 0 => basepoint
sign bit = 1 => minus basepoint

Test Edwards -> Montgomery on the X/Ed25519 basepoint

Check that Montgomery -> Edwards fails for points on the twist.

u = 2 corresponds to a point on the twist.

u = -1 corresponds to a point on the twist, but should be
checked explicitly because it's an exceptional point for the
birational map.  For instance, libsignal will accept it.

Returns a random point on the prime-order subgroup

Given a bytestring that's little-endian at the byte level, return an iterator over all the
bits, in little-endian order.
As i runs from 0..256, the bottom 3 bits index the bit, while the upper bits index
the byte. Since self.bytes is little-endian at the byte level, this iterator is
little-endian on the bit level

Tests that, on the prime-order subgroup, MontgomeryPoint::mul_bits_be is the same as
multiplying by the Scalar representation of the same bits
Make a random prime-order point P

Make a random integer b

Check that bP is the same whether calculated as scalar-times-edwards or
integer-times-montgomery.

Tests that MontgomeryPoint::mul_bits_be is consistent on any point, even ones that might be
on the curve's twist. Specifically, this tests that b₁(b₂P) == b₂(b₁P) for random
integers b₁, b₂ and random (curve or twist) point P.
Make a random point P on the curve or its twist

Compute two big integers b₁ and b₂

Compute b₁P and b₂P

Check that b₁(b₂P) == b₂(b₁P)

Check that mul_base_clamped and mul_clamped agree

Test agreement on a large integer. Even after clamping, this is not reduced mod l.

Test agreement on random integers

This will be reduced mod l with probability l / 2^256 ≈ 6.25%

## src/ristretto.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2020 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

We allow non snake_case names because coordinates in projective space are
traditionally denoted by the capitalisation of their respective
counterparts in affine space.  Yeah, you heard me, rustc, I'm gonna have my
affine and projective cakes and eat both of them too.

An implementation of [Ristretto][ristretto_main], which provides a
prime-order group.

### The Ristretto Group

Ristretto is a modification of Mike Hamburg's Decaf scheme to work
with cofactor-$8$ curves, such as Curve25519.

The introduction of the Decaf paper, [_Decaf:
Eliminating cofactors through point
compression_](https://eprint.iacr.org/2015/673.pdf), notes that while
most cryptographic systems require a group of prime order, most
concrete implementations using elliptic curve groups fall short –
they either provide a group of prime order, but with incomplete or
variable-time addition formulae (for instance, most Weierstrass
models), or else they provide a fast and safe implementation of a
group whose order is not quite a prime $q$, but $hq$ for a
small cofactor $h$ (for instance, Edwards curves, which have
cofactor at least $4$).

This abstraction mismatch is commonly “handled” by pushing the
complexity upwards, adding ad-hoc protocol modifications.  But
these modifications require careful analysis and are a recurring
source of [vulnerabilities][cryptonote] and [design
complications][ed25519_hkd].

Instead, Decaf (and Ristretto) use a quotient group to implement a
prime-order group using a non-prime-order curve.  This provides
the correct abstraction for cryptographic systems, while retaining
the speed and safety benefits of an Edwards curve.

Decaf is named “after the procedure which divides the effect of
coffee by $4$”.  However, Curve25519 has a cofactor of
$8$.  To eliminate its cofactor, Ristretto restricts further;
this [additional restriction][ristretto_coffee] gives the
_Ristretto_ encoding.

More details on why Ristretto is necessary can be found in the
[Why Ristretto?][why_ristretto] section of the Ristretto website.

Ristretto
points are provided in `curve25519-dalek` by the `RistrettoPoint`
struct.

#### Encoding and Decoding

Encoding is done by converting to and from a `CompressedRistretto`
struct, which is a typed wrapper around `[u8; 32]`.

The encoding is not batchable, but it is possible to
double-and-encode in a batch using
`RistrettoPoint::double_and_compress_batch`.

#### Equality Testing

Testing equality of points on an Edwards curve in projective
coordinates requires an expensive inversion.  By contrast, equality
checking in the Ristretto group can be done in projective
coordinates without requiring an inversion, so it is much faster.

The `RistrettoPoint` struct implements the
[`subtle::ConstantTimeEq`] trait for constant-time equality
checking, and also uses this to ensure `Eq` equality checking
runs in constant time.

#### Scalars

Scalars are represented by the `Scalar` struct.  Each scalar has a
canonical representative mod the group order.  To attempt to load
a supposedly-canonical scalar, use
`Scalar::from_canonical_bytes()`. To check whether a
representative is canonical, use `Scalar::is_canonical()`.

#### Scalar Multiplication

Scalar multiplication on Ristretto points is provided by:

* the `*` operator between a `Scalar` and a `RistrettoPoint`, which
performs constant-time variable-base scalar multiplication;

* the `*` operator between a `Scalar` and a
`RistrettoBasepointTable`, which performs constant-time fixed-base
scalar multiplication;

* an implementation of the
[`MultiscalarMul`](../traits/trait.MultiscalarMul.html) trait for
constant-time variable-base multiscalar multiplication;

* an implementation of the
[`VartimeMultiscalarMul`](../traits/trait.VartimeMultiscalarMul.html)
trait for variable-time variable-base multiscalar multiplication;

#### Random Points and Hashing to Ristretto

The Ristretto group comes equipped with an Elligator map.  This is
used to implement

* `RistrettoPoint::random()`, which generates random points from an
RNG - enabled by `rand_core` feature;

* `RistrettoPoint::from_hash()` and
`RistrettoPoint::hash_from_bytes()`, which perform hashing to the
group.

The Elligator map itself is not currently exposed.

#### Implementation

The Decaf suggestion is to use a quotient group, such as $\mathcal
E / \mathcal E\[4\]$ or $2 \mathcal E / \mathcal E\[2\] $, to
implement a prime-order group using a non-prime-order curve.

This requires only changing

1. the function for equality checking (so that two representatives
of the same coset are considered equal);
2. the function for encoding (so that two representatives of the
same coset are encoded as identical bitstrings);
3. the function for decoding (so that only the canonical encoding of
a coset is accepted).

Internally, each coset is represented by a curve point; two points
$ P, Q $ may represent the same coset in the same way that two
points with different $X,Y,Z$ coordinates may represent the
same point.  The group operations are carried out with no overhead
using Edwards formulas.

Notes on the details of the encoding can be found in the
[Details][ristretto_notes] section of the Ristretto website.

[cryptonote]:
https://moderncrypto.org/mail-archive/curves/2017/000898.html
[ed25519_hkd]:
https://moderncrypto.org/mail-archive/curves/2017/000858.html
[ristretto_coffee]:
https://en.wikipedia.org/wiki/Ristretto
[ristretto_notes]:
https://ristretto.group/details/index.html
[why_ristretto]:
https://ristretto.group/why_ristretto.html
[ristretto_main]:
https://ristretto.group/

### Compressed points

A Ristretto point, in compressed wire format.

The Ristretto encoding is canonical, so two points are equal if and
only if their encodings are equal.
Copy the bytes of this `CompressedRistretto`.

View this `CompressedRistretto` as an array of bytes.

Construct a `CompressedRistretto` from a slice of bytes.

### Errors

Returns [`TryFromSliceError`] if the input `bytes` slice does not have
a length of 32.

Attempt to decompress to an `RistrettoPoint`.

### Return

- `Some(RistrettoPoint)` if `self` was the canonical encoding of a point;

- `None` if `self` was not the canonical encoding of a point.
Step 1. Check s for validity:
1.a) s must be 32 bytes (we get this from the type system)
1.b) s < p
1.c) s is nonnegative

Our decoding routine ignores the high bit, so the only
possible failure for 1.b) is if someone encodes s in 0..18
as s+p in 2^255-19..2^255-1.  We can check this by
converting back to bytes, and checking that we get the
original input, since our encoding routine is canonical.
Step 2.  Compute (X:Y:Z:T).

v == ad(1+as²)² - (1-as²)²            where d=-121665/121666

x == | 2s/sqrt(v) | == + sqrt(4s²/(ad(1+as²)² - (1-as²)²))

y == (1-as²)/(1+as²)

t == ((1+as²) sqrt(4s²/(ad(1+as²)² - (1-as²)²)))/(1-as²)

### Serde support
Serializes to and from `RistrettoPoint` directly, doing compression
and decompression internally.  This means that users can create
structs containing `RistrettoPoint`s and use Serde's derived
serializers to serialize those structures.

### Internal point representations

A `RistrettoPoint` represents a point in the Ristretto group for
Curve25519.  Ristretto, a variant of Decaf, constructs a
prime-order group as a quotient group of a subgroup of (the
Edwards form of) Curve25519.

Internally, a `RistrettoPoint` is implemented as a wrapper type
around `EdwardsPoint`, with custom equality, compression, and
decompression routines to account for the quotient.  This means that
operations on `RistrettoPoint`s are exactly as fast as operations on
`EdwardsPoint`s.

Compress this point using the Ristretto encoding.
Ignore return value since this is always square

Double-and-compress a batch of points.  The Ristretto encoding
is not batchable, since it requires an inverse square root.

However, given input points $ P_1, \ldots, P_n, $
it is possible to compute the encodings of their doubles $
\mathrm{enc}( \[2\]P_1), \ldots, \mathrm{enc}( \[2\]P_n ) $
in a batch.

```

### use curve25519_dalek::ristretto::RistrettoPoint;
use rand_core::{OsRng, TryRngCore};

### // Need fn main() here in comment so the doctest compiles
### // See https://doc.rust-lang.org/book/documentation.html#documentation-as-tests
### fn main() {
let mut rng = OsRng.unwrap_err();

let points: Vec<RistrettoPoint> =
(0..32).map(|_| RistrettoPoint::random(&mut rng)).collect();

let compressed = RistrettoPoint::double_and_compress_batch(&points);

for (P, P2_compressed) in points.iter().zip(compressed.iter()) {
assert_eq!(*P2_compressed, (P + P).compress());
}
### }
```

Return the coset self + E\[4\], for debugging.

Computes the Ristretto Elligator map. This is the
[`MAP`](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#section-4.3.4)
function defined in the Ristretto spec.

### Note

This method is not public because it's just used for hashing
to a point -- proper elligator support is deferred for now.

The conversion from W_i is exactly the conversion from P1xP1.
Return a `RistrettoPoint` chosen uniformly at random using a user-provided RNG.

### Inputs

* `rng`: any RNG which implements `CryptoRng` interface.

### Returns

A random element of the Ristretto group.

### Implementation

Uses the Ristretto-flavoured Elligator 2 map, so that the
discrete log of the output point with respect to any other
point should be unknown.  The map is applied twice and the
results are added, to ensure a uniform distribution.
Return a `RistrettoPoint` chosen uniformly at random using a user-provided RNG.

### Inputs

* `rng`: any RNG which implements `TryCryptoRng` interface.

### Returns

A random element of the Ristretto group.

### Implementation

Uses the Ristretto-flavoured Elligator 2 map, so that the
discrete log of the output point with respect to any other
point should be unknown.  The map is applied twice and the
results are added, to ensure a uniform distribution.
Hash a slice of bytes into a `RistrettoPoint`.

Takes a type parameter `D`, which is any `Digest` producing 64
bytes of output.

Convenience wrapper around `from_hash`.

### Implementation

Uses the Ristretto-flavoured Elligator 2 map, so that the
discrete log of the output point with respect to any other
point should be unknown.  The map is applied twice and the
results are added, to ensure a uniform distribution.

### Example

```

### use curve25519_dalek::ristretto::RistrettoPoint;
use sha2::Sha512;

### // Need fn main() here in comment so the doctest compiles
### // See https://doc.rust-lang.org/book/documentation.html#documentation-as-tests
### fn main() {
let msg = "To really appreciate architecture, you may even need to commit a murder";
let P = RistrettoPoint::hash_from_bytes::<Sha512>(msg.as_bytes());
### }
```

Construct a `RistrettoPoint` from an existing `Digest` instance.

Use this instead of `hash_from_bytes` if it is more convenient
to stream data into the `Digest` than to pass a single byte
slice.
dealing with generic arrays is clumsy, until const generics land

Construct a `RistrettoPoint` from 64 bytes of data.

If the input bytes are uniformly distributed, the resulting
point will be uniformly distributed over the group, and its
discrete log with respect to other points should be unknown.

### Implementation

This function splits the input array into two 32-byte halves,
takes the low 255 bits of each half mod p, applies the
Ristretto-flavored Elligator map to each, and adds the results.

This follows the one-way map construction from the Ristretto RFC:
https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#section-4.3.4

Applying Elligator twice and adding the results ensures a
uniform distribution.

### Equality
Test equality between two `RistrettoPoint`s.

### Returns

* `Choice(1)` if the two `RistrettoPoint`s are equal;
* `Choice(0)` otherwise.

### Arithmetic
Scalar multiplication: compute `scalar * self`.

Scalar multiplication: compute `self * scalar`.
Fixed-base scalar multiplication by the Ristretto base point.

Uses precomputed basepoint tables when the `precomputed-tables` feature
is enabled, trading off increased code size for ~4x better performance.

### Multiscalar Multiplication impls

These use iterator combinators to unwrap the underlying points and
forward to the EdwardsPoint implementations.

Precomputation for variable-time multiscalar multiplication with `RistrettoPoint`s.

Note that for large numbers of `RistrettoPoint`s, this functionality may be less
efficient than the corresponding `VartimeMultiscalarMul` implementation.
This wraps the inner implementation in a facade type so that we can
decouple stability of the inner type from the stability of the
outer type.
Compute $aA + bB$ in variable time, where $B$ is the
Ristretto basepoint.

A precomputed table of multiples of a basepoint, used to accelerate
scalar multiplication.

A precomputed table of multiples of the Ristretto basepoint is
available in the `constants` module:
```
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_TABLE;
use curve25519_dalek::scalar::Scalar;

let a = Scalar::from(87329482u64);
let P = &a * RISTRETTO_BASEPOINT_TABLE;
```
Create a precomputed table of multiples of the given `basepoint`.

Get the basepoint for this table as a `RistrettoPoint`.

### Constant-time conditional selection
Conditionally select between `self` and `other`.

### Example

```
use subtle::ConditionallySelectable;
use subtle::Choice;
#
### use curve25519_dalek::traits::Identity;
### use curve25519_dalek::ristretto::RistrettoPoint;
### use curve25519_dalek::constants;
### fn main() {

let A = RistrettoPoint::identity();
let B = constants::RISTRETTO_BASEPOINT_POINT;

let mut P = A;

P = RistrettoPoint::conditional_select(&A, &B, Choice::from(0));
assert_eq!(P, A);
P = RistrettoPoint::conditional_select(&A, &B, Choice::from(1));
assert_eq!(P, B);
### }
```

### Debug traits

### group traits

Use the full trait path to avoid Group::identity overlapping Identity::identity in the
rest of the module (e.g. tests).
NOTE: this is duplicated due to different `rng` bounds
Just use the checked API; the checks we could skip aren't expensive.

Ristretto has a cofactor of 1.

### Zeroize traits

### Tests

Check that the encoding is 32 bytes exactly

Check that the encoding itself matches the usual one
Test that sum works for non-empty iterators

Test that sum works for the empty iterator

Test that sum works on owning iterators
constants::d is neg, so decompression should fail as |d| != d.
Check that bp_recaf differs from bp by a point of order 4
Table of encodings of i*basepoint
Generated using ristretto.sage
Test vectors extracted from ristretto.sage.

Notice that all of the byte sequences have bit 255 set to 0; this is because
ristretto.sage does not mask the high bit of a field element.  When the high bit is set,
the ristretto.sage elligator implementation gives different results, since it takes a
different field element as input.

Known answer tests for the one-way mapping function in the Ristretto RFC
These inputs are from
https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#appendix-A.3
Check that onewaymap(input) == output for all the above vectors

Use zero scalars

Compute the linear combination using precomputed multiscalar multiplication

Compute the linear combination manually

Use one fewer scalars

Compute the linear combination using precomputed multiscalar multiplication

Compute the linear combination manually

Use one fewer scalars

Compute the linear combination using precomputed multiscalar multiplication

Compute the linear combination manually

Use zero scalars

Compute the linear combination using precomputed multiscalar multiplication

Compute the linear combination manually

## src/scalar.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
Portions Copyright 2017 Brian Smith
See LICENSE for licensing information.

Authors:
- Isis Agora Lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>
- Brian Smith <brian@briansmith.org>

Arithmetic on scalars (integers mod the group order).

Both the Ristretto group and the Ed25519 basepoint have prime order
$ \ell = 2^{252} + 27742317777372353535851937790883648493 $.

This code is intended to be useful with both the Ristretto group
(where everything is done modulo $ \ell $), and the X/Ed25519
setting, which mandates specific bit-twiddles that are not
well-defined modulo $ \ell $.

All arithmetic on `Scalars` is done modulo $ \ell $.

### Constructing a scalar

To create a [`Scalar`](struct.Scalar.html) from a supposedly canonical encoding, use
[`Scalar::from_canonical_bytes`](struct.Scalar.html#method.from_canonical_bytes).

This function does input validation, ensuring that the input bytes
are the canonical encoding of a `Scalar`.
If they are, we'll get
`Some(Scalar)` in return:

```
use curve25519_dalek::scalar::Scalar;

let one_as_bytes: [u8; 32] = Scalar::ONE.to_bytes();
let a: Option<Scalar> = Scalar::from_canonical_bytes(one_as_bytes).into();

assert!(a.is_some());
```

However, if we give it bytes representing a scalar larger than $ \ell $
(in this case, $ \ell + 2 $), we'll get `None` back:

```
use curve25519_dalek::scalar::Scalar;

let l_plus_two_bytes: [u8; 32] = [
0xef, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
];
let a: Option<Scalar> = Scalar::from_canonical_bytes(l_plus_two_bytes).into();

assert!(a.is_none());
```

Another way to create a `Scalar` is by reducing a $256$-bit integer mod
$ \ell $, for which one may use the
[`Scalar::from_bytes_mod_order`](struct.Scalar.html#method.from_bytes_mod_order)
method.  In the case of the second example above, this would reduce the
resultant scalar $ \mod \ell $, producing $ 2 $:

```
use curve25519_dalek::scalar::Scalar;

let l_plus_two_bytes: [u8; 32] = [
0xef, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
];
let a: Scalar = Scalar::from_bytes_mod_order(l_plus_two_bytes);

let two: Scalar = Scalar::ONE + Scalar::ONE;

assert!(a == two);
```

There is also a constructor that reduces a $512$-bit integer,
[`Scalar::from_bytes_mod_order_wide`].

To construct a `Scalar` as the hash of some input data, use
[`Scalar::hash_from_bytes`], which takes a buffer, or
[`Scalar::from_hash`], which allows an IUF API.

```

### fn main() {
use sha2::{Digest, Sha512};
use curve25519_dalek::scalar::Scalar;

// Hashing a single byte slice
let a = Scalar::hash_from_bytes::<Sha512>(b"Abolish ICE");

// Streaming data into a hash object
let mut hasher = Sha512::default();
hasher.update(b"Abolish ");
hasher.update(b"ICE");
let a2 = Scalar::from_hash(hasher);

assert_eq!(a, a2);
### }
```

See also `Scalar::hash_from_bytes` and `Scalar::from_hash` that
reduces a $512$-bit integer, if the optional `digest` feature
has been enabled.
An `UnpackedScalar` represents an element of the field GF(l), optimized for speed.

This is a type alias for one of the scalar types in the `backend`
module.

An `UnpackedScalar` represents an element of the field GF(l), optimized for speed.

This is a type alias for one of the scalar types in the `backend`
module.
An `UnpackedScalar` represents an element of the field GF(l), optimized for speed.

This is a type alias for one of the scalar types in the `backend`
module.
An `UnpackedScalar` represents an element of the field GF(l), optimized for speed.

This is a type alias for one of the scalar types in the `backend`
module.

The `Scalar` struct holds an element of $\mathbb Z / \ell\mathbb Z $.
`bytes` is a little-endian byte encoding of an integer representing a scalar modulo the
group order.

### Invariant #1

The integer representing this scalar is less than $2^{255}$. That is, the most
significant bit of `bytes[31]` is 0.

This is required for `EdwardsPoint` variable- and fixed-base multiplication, because most
integers above 2^255 are unrepresentable in our radix-16 NAF (see [`Self::as_radix_16`]).
The invariant is also required because our `MontgomeryPoint` multiplication assumes the MSB
is 0 (see `MontgomeryPoint::mul`).

### Invariant #2 (weak)

The integer representing this scalar is less than $2^{255} - 19 $, i.e., it represents
a canonical representative of an element of $ \mathbb Z / \ell\mathbb Z $. This is
stronger than invariant #1. It also sometimes has to be broken.

This invariant is deliberately broken in the implementation of `EdwardsPoint::{mul_clamped,
mul_base_clamped}`, `MontgomeryPoint::{mul_clamped, mul_base_clamped}`, and
`BasepointTable::mul_base_clamped`. This is not an issue though. As mentioned above,
scalar-point multiplication is defined for any choice of `bytes` that satisfies invariant
###1. Since clamping guarantees invariant #1 is satisfied, these operations are well defined.

Note: Scalar-point mult is the _only_ thing you can do safely with an unreduced scalar.
Scalar-scalar addition and subtraction are NOT correct when using unreduced scalars.
Multiplication is correct, but this is only due to a quirk of our implementation, and not
guaranteed to hold in general in the future.

Note: It is not possible to construct an unreduced `Scalar` from the public API unless the
`legacy_compatibility` is enabled (thus making `Scalar::from_bits` public). Thus, for all
public non-legacy uses, invariant #2
always holds.

Construct a `Scalar` by reducing a 256-bit little-endian integer
modulo the group order $ \ell $.

Temporarily allow s_unreduced.bytes > 2^255 ...

Then reduce mod the group order and return the reduced representative.

Construct a `Scalar` by reducing a 512-bit little-endian integer
modulo the group order $ \ell $.

Attempt to construct a `Scalar` from a canonical byte representation.

### Return

- `Some(s)`, where `s` is the `Scalar` corresponding to `bytes`,
if `bytes` is a canonical byte representation modulo the group order $ \ell $;
- `None` if `bytes` is not a canonical byte representation.

Construct a `Scalar` from the low 255 bits of a 256-bit integer. This breaks the invariant
that scalars are always reduced. Scalar-scalar arithmetic, i.e., addition, subtraction,
multiplication, **does not work** on scalars produced from this function. You may only use
the output of this function for `EdwardsPoint::mul`, `MontgomeryPoint::mul`, and
`EdwardsPoint::vartime_double_scalar_mul_basepoint`. **Do not use this function** unless
you absolutely have to.
Ensure invariant #1 holds. That is, make s < 2^255 by masking the high bit.

Index the bytes of the representative for this `Scalar`.  Mutation is not permitted.
The UnpackedScalar::add function produces reduced outputs if the inputs are reduced. By
Scalar invariant #1, this is always the case.
The UnpackedScalar::sub function produces reduced outputs if the inputs are reduced. By
Scalar invariant #1, this is always the case.
Construct a scalar from the given `u64`.

### Inputs

An `u64` to convert to a `Scalar`.

### Returns

A `Scalar` corresponding to the input `u64`.

### Example

```
use curve25519_dalek::scalar::Scalar;

let fourtytwo = Scalar::from(42u64);
let six = Scalar::from(6u64);
let seven = Scalar::from(7u64);

assert!(fourtytwo == six * seven);
```
The scalar $ 0 $.

The scalar $ 1 $.
Return a `Scalar` chosen uniformly at random using a user-provided RNG.

### Inputs

* `rng`: any RNG which implements `CryptoRng` interface.

### Returns

A random scalar within $\mathbb{Z} / \ell\mathbb{Z}$.

### Example

```
### fn main() {
use curve25519_dalek::scalar::Scalar;

use rand_core::{OsRng, TryRngCore};

let mut csprng = OsRng.unwrap_err();
let a: Scalar = Scalar::random(&mut csprng);
### }
```

Hash a slice of bytes into a scalar.

Takes a type parameter `D`, which is any `Digest` producing 64
bytes (512 bits) of output.

Convenience wrapper around `from_hash`.

### Example

```

### use curve25519_dalek::scalar::Scalar;
use sha2::Sha512;

### // Need fn main() here in comment so the doctest compiles
### // See https://doc.rust-lang.org/book/documentation.html#documentation-as-tests
### fn main() {
let msg = "To really appreciate architecture, you may even need to commit a murder";
let s = Scalar::hash_from_bytes::<Sha512>(msg.as_bytes());
### }
```
Construct a scalar from an existing `Digest` instance.

Use this instead of `hash_from_bytes` if it is more convenient
to stream data into the `Digest` than to pass a single byte
slice.

### Example

```
### use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::digest::Update;

use sha2::Digest;
use sha2::Sha512;

### fn main() {
let mut h = Sha512::new()
.chain("To really appreciate architecture, you may even need to commit a murder.")
.chain("While the programs used for The Manhattan Transcripts are of the most extreme")
.chain("nature, they also parallel the most common formula plot: the archetype of")
.chain("murder. Other phantasms were occasionally used to underline the fact that")
.chain("perhaps all architecture, rather than being about functional standards, is")
.chain("about love and death.");

let s = Scalar::from_hash(h);

println!("{:?}", s.to_bytes());
assert_eq!(
s.to_bytes(),
[  21,  88, 208, 252,  63, 122, 210, 152,
154,  38,  15,  23,  16, 167,  80, 150,
192, 221,  77, 226,  62,  25, 224, 148,
239,  48, 176,  10, 185,  69, 168,  11, ],
);
### }
```

Convert this `Scalar` to its underlying sequence of bytes.

### Example

```
use curve25519_dalek::scalar::Scalar;

let s: Scalar = Scalar::ZERO;

assert!(s.to_bytes() == [0u8; 32]);
```

View the little-endian byte encoding of the integer representing this Scalar.

### Example

```
use curve25519_dalek::scalar::Scalar;

let s: Scalar = Scalar::ZERO;

assert!(s.as_bytes() == &[0u8; 32]);
```

Given a nonzero `Scalar`, compute its multiplicative inverse.

### Warning

`self` **MUST** be nonzero.  If you cannot
*prove* that this is the case, you **SHOULD NOT USE THIS
FUNCTION**.

### Returns

The multiplicative inverse of the this `Scalar`.

### Example

```
use curve25519_dalek::scalar::Scalar;

// x = 2238329342913194256032495932344128051776374960164957527413114840482143558222
let X: Scalar = Scalar::from_bytes_mod_order([
0x4e, 0x5a, 0xb4, 0x34, 0x5d, 0x47, 0x08, 0x84,
0x59, 0x13, 0xb4, 0x64, 0x1b, 0xc2, 0x7d, 0x52,
0x52, 0xa5, 0x85, 0x10, 0x1b, 0xcc, 0x42, 0x44,
0xd4, 0x49, 0xf4, 0xa8, 0x79, 0xd9, 0xf2, 0x04,
]);
// 1/x = 6859937278830797291664592131120606308688036382723378951768035303146619657244
let XINV: Scalar = Scalar::from_bytes_mod_order([
0x1c, 0xdc, 0x17, 0xfc, 0xe0, 0xe9, 0xa5, 0xbb,
0xd9, 0x24, 0x7e, 0x56, 0xbb, 0x01, 0x63, 0x47,
0xbb, 0xba, 0x31, 0xed, 0xd5, 0xa9, 0xbb, 0x96,
0xd5, 0x0b, 0xcd, 0x7a, 0x3f, 0x96, 0x2a, 0x0f,
]);

let inv_X: Scalar = X.invert();
assert!(XINV == inv_X);
let should_be_one: Scalar = &inv_X * &X;
assert!(should_be_one == Scalar::ONE);
```

Given a slice of nonzero (possibly secret) `Scalar`s,
compute their inverses in a batch.

### Return

Each element of `inputs` is replaced by its inverse.

The product of all inverses is returned.

### Warning

All input `Scalars` **MUST** be nonzero.  If you cannot
*prove* that this is the case, you **SHOULD NOT USE THIS
FUNCTION**.

### Example

```
### use curve25519_dalek::scalar::Scalar;
### fn main() {
let mut scalars = [
Scalar::from(3u64),
Scalar::from(5u64),
Scalar::from(7u64),
Scalar::from(11u64),
];

let allinv = Scalar::batch_invert(&mut scalars);

assert_eq!(allinv, Scalar::from(3*5*7*11u64).invert());
assert_eq!(scalars[0], Scalar::from(3u64).invert());
assert_eq!(scalars[1], Scalar::from(5u64).invert());
assert_eq!(scalars[2], Scalar::from(7u64).invert());
assert_eq!(scalars[3], Scalar::from(11u64).invert());
### }
```
This code is essentially identical to the FieldElement
implementation, and is documented there.  Unfortunately,
it's not easy to write it generically, since here we want
to use `UnpackedScalar`s internally, and `Scalar`s
externally, but there's no corresponding distinction for
field elements.

Keep an accumulator of all of the previous products

Pass through the input vector, recording the previous
products in the scratch space

Avoid unnecessary Montgomery multiplication in second pass by
keeping inputs in Montgomery form

acc is nonzero iff all inputs are nonzero

Compute the inverse of all products

We need to return the product of all inverses later

Pass through the vector backwards to compute the inverses
in place

Get the bits of the scalar, in little-endian order
As i runs from 0..256, the bottom 3 bits index the bit, while the upper bits index
the byte. Since self.bytes is little-endian at the byte level, this iterator is
little-endian on the bit level

Compute a width-$w$ "Non-Adjacent Form" of this scalar.

A width-$w$ NAF of a positive integer $k$ is an expression
$$
k = \sum_{i=0}^m n_i 2^i,
$$
where each nonzero
coefficient $n_i$ is odd and bounded by $|n_i| < 2^{w-1}$,
$n_{m-1}$ is nonzero, and at most one of any $w$ consecutive
coefficients is nonzero.  (Hankerson, Menezes, Vanstone; def 3.32).

The length of the NAF is at most one more than the length of
the binary representation of $k$.  This is why the
`Scalar` type maintains an invariant (invariant #1) that the top bit is
$0$, so that the NAF of a scalar has at most 256 digits.

Intuitively, this is like a binary expansion, except that we
allow some coefficients to grow in magnitude up to
$2^{w-1}$ so that the nonzero coefficients are as sparse
as possible.

When doing scalar multiplication, we can then use a lookup
table of precomputed multiples of a point to add the nonzero
terms $ k_i P $.  Using signed digits cuts the table size
in half, and using odd digits cuts the table size in half
again.

To compute a $w$-NAF, we use a modification of Algorithm 3.35 of HMV:

1. $ i \gets 0 $
2. While $ k \ge 1 $:
1. If $k$ is odd, $ n_i \gets k \operatorname{mods} 2^w $, $ k \gets k - n_i $.
2. If $k$ is even, $ n_i \gets 0 $.
3. $ k \gets k / 2 $, $ i \gets i + 1 $.
3. Return $ n_0, n_1, ... , $

Here $ \bar x = x \operatorname{mods} 2^w $ means the
$ \bar x $ with $ \bar x \equiv x \pmod{2^w} $ and
$ -2^{w-1} \leq \bar x < 2^{w-1} $.

We implement this by scanning across the bits of $k$ from
least-significant bit to most-significant-bit.
Write the bits of $k$ as
$$
k = \sum_{i=0}^m k_i 2^i,
$$
and split the sum as
$$
k = \sum_{i=0}^{w-1} k_i 2^i + 2^w \sum_{i=0} k_{i+w} 2^i
$$
where the first part is $ k \mod 2^w $.

If $ k \mod 2^w$ is odd, and $ k \mod 2^w < 2^{w-1} $, then we emit
$ n_0 = k \mod 2^w $.  Instead of computing
$ k - n_0 $, we just advance $w$ bits and reindex.

If $ k \mod 2^w$ is odd, and $ k \mod 2^w \ge 2^{w-1} $, then
$ n_0 = k \operatorname{mods} 2^w = k \mod 2^w - 2^w $.
The quantity $ k - n_0 $ is
$$
\begin{aligned}
k - n_0 &= \sum_{i=0}^{w-1} k_i 2^i + 2^w \sum_{i=0} k_{i+w} 2^i
- \sum_{i=0}^{w-1} k_i 2^i + 2^w \\\\
&= 2^w + 2^w \sum_{i=0} k_{i+w} 2^i
\end{aligned}
$$
so instead of computing the subtraction, we can set a carry
bit, advance $w$ bits, and reindex.

If $ k \mod 2^w$ is even, we emit $0$, advance 1 bit
and reindex.  In fact, by setting all digits to $0$
initially, we don't need to emit anything.

required by the NAF definition

required so that the NAF digits fit in i8
Construct a buffer of bits of the scalar, starting at bit `pos`
This window's bits are contained in a single u64
Combine the current u64's bits with the bits from the next u64

Add the carry into the current window
If the window value is even, preserve the carry and continue.
Why is the carry preserved?
If carry == 0 and window & 1 == 0, then the next carry should be 0
If carry == 1 and window & 1 == 0, then bit_buf & 1 == 1 so the next carry should be 1

Write this scalar in radix 16, with coefficients in $[-8,8)$,
i.e., compute $a_i$ such that
$$
a = a_0 + a_1 16^1 + \cdots + a_{63} 16^{63},
$$
with $-8 \leq a_i < 8$ for $0 \leq i < 63$ and $-8 \leq a_{63} \leq 8$.

The largest value that can be decomposed like this is just over $2^{255}$. Thus, in
order to not error, the top bit MUST NOT be set, i.e., `Self` MUST be less than
$2^{255}$.

Step 1: change radix.
Convert from radix 256 (bytes) to radix 16 (nibbles)
Precondition note: since self[31] <= 127, output[63] <= 7

Step 2: recenter coefficients from [0,16) to [-8,8)
Precondition note: output[63] is not recentered.  It
increases by carry <= 1.  Thus output[63] <= 8.

Returns a size hint indicating how many entries of the return
value of `to_radix_2w` are nonzero.
See comment in to_radix_2w on handling the terminal carry.

Creates a representation of a Scalar in radix $ 2^w $ with $w = 4, 5, 6, 7, 8$ for
use with the Pippenger algorithm. Higher radixes are not supported to save cache space.
Radix 256 is near-optimal even for very large inputs.

Radix below 16 or above 256 is prohibited.
This method returns digits in a fixed-sized array, excess digits are zeroes.

For radix 16, `Self` must be less than $2^{255}$. This is because most integers larger
than $2^{255}$ are unrepresentable in the form described below for $w = 4$. This
would be true for $w = 8$ as well, but it is compensated for by increasing the size
hint by 1.

#### Scalar representation

Radix $2^w$, with $n = ceil(256/w)$ coefficients in $[-(2^w)/2,(2^w)/2)$,
i.e., scalar is represented using digits $a_i$ such that
$$
a = a_0 + a_1 2^1w + \cdots + a_{n-1} 2^{w*(n-1)},
$$
with $-2^w/2 \leq a_i < 2^w/2$ for $0 \leq i < (n-1)$ and $-2^w/2 \leq a_{n-1} \leq 2^w/2$.


Scalar formatted as four `u64`s with carry bit packed into the highest bit.
Construct a buffer of bits of the scalar, starting at `bit_offset`.

Read the bits from the scalar

This window's bits are contained in a single u64,
or it's the last u64 anyway.
Combine the current u64's bits with the bits from the next u64

Read the actual coefficient value from the window

Recenter coefficients from [0,2^w) to [-2^w/2, 2^w/2)

When 4 < w < 8, we can fold the final carry onto the last digit d,
because d < 2^w/2 so d + carry*2^w = d + 1*2^w < 2^(w+1) < 2^8.

When w = 8, we can't fit carry*2^w into an i8.  This should
not happen anyways, because the final carry will be 0 for
reduced scalars, but Scalar invariant #1 allows 255-bit scalars.
To handle this, we expand the size_hint by 1 when w=8,
and accumulate the final carry onto another digit.

Unpack this `Scalar` to an `UnpackedScalar` for faster arithmetic.

Reduce this `Scalar` modulo $\ell$.

Check whether this `Scalar` is the canonical representative mod $\ell$. This is not
public because any `Scalar` that is publicly observed is reduced, by scalar invariant #2.
Pack the limbs of this `UnpackedScalar` into a `Scalar`.

Inverts an UnpackedScalar in Montgomery form.
Uses the addition chain from
https://briansmith.org/ecc-inversion-addition-chains-01#curve25519_scalar_inversion

_10000

Inverts an UnpackedScalar not in Montgomery form.
NOTE: this is duplicated due to different `rng` bounds
Check that the high bit is not set

Read one or more u64s stored as little endian bytes.

#### Panics
Panics if `src.len() != 8 * dst.len()`.

_Clamps_ the given little-endian representation of a 32-byte integer. Clamping the value puts
it in the range:

**n ∈ 2^254 + 8\*{0, 1, 2, 3, . . ., 2^251 − 1}**

### Explanation of clamping

For Curve25519, h = 8, and multiplying by 8 is the same as a binary left-shift by 3 bits.
If you take a secret scalar value between 2^251 and 2^252 – 1 and left-shift by 3 bits
then you end up with a 255-bit number with the most significant bit set to 1 and
the least-significant three bits set to 0.

The Curve25519 clamping operation takes **an arbitrary 256-bit random value** and
clears the most-significant bit (making it a 255-bit number), sets the next bit, and then
clears the 3 least-significant bits. In other words, it directly creates a scalar value that is
in the right form and pre-multiplied by the cofactor.

See [here](https://neilmadden.blog/2020/05/28/whats-the-curve25519-clamping-all-about/) for
more details.

x = 2238329342913194256032495932344128051776374960164957527413114840482143558222
1/x = 6859937278830797291664592131120606308688036382723378951768035303146619657244
y = 2592331292931086675770238855846338635550719849568364935475441891787804997264

The largest scalar that satisfies invariant #1, i.e., the largest scalar with the top bit
set to 0. Since this scalar violates invariant #2, i.e., it's greater than the modulus `l`,
addition and subtraction are broken. The only thing you can do with this is scalar-point
multiplication (and actually also scalar-scalar multiplication, but that's just a quirk of
our implementation).

x*y = 5690045403673944803228348699031245560686958845067437804563560795922180092780

sage: l = 2^252 + 27742317777372353535851937790883648493
sage: big = 2^256 - 1
sage: repr((big % l).digits(256))

The largest clamped integer
LE bytes of 24519928653854221733733552434404946937899825954937634815
LE bytes of 4975441334397345751130612518500927154628011511324180036903450236863266160640
LE bytes of 6432735165214683820902750800207468552549813371247423777071615116673864412038

also_a = (a mod l)

also_b = (b mod l)

Reconstruct the scalar from the computed NAF
Check that addition wraps around the modulus
Check that subtraction wraps around the modulus
Test that product works for non-empty iterators

Test that product works for the empty iterator

Test that product works for iterators where Item = Scalar
now zs is an iterator with Item = Scalar
Test that sum works for non-empty iterators

Test that sum works for the empty iterator

Test that sum works for owned types
now zs is an iterator with Item = Scalar
set bignum = x + 2^256x
3958878930004874126169954872055634648693766179881526445624823978500314864344
= x + 2^256x (mod l)

Negating a scalar twice should result in the original scalar.

set bignum = x + 2^256x
x + 2^256x (mod l)
= 3958878930004874126169954872055634648693766179881526445624823978500314864344

The reduced scalar should match the expected

(x + 2^256x) * R
((x + 2^256x) * R) / R  (mod l)

The Montgomery reduced scalar should match the reduced one, as well as the expected
canonical encoding of 1667457891

encoding of
7265385991361016183439748078976496179028704920197054998554201349516117938192
= 28380414028753969466561515933501938171588560817147392552250411230663687203 (mod l)
non_canonical because unreduced mod l

encoding with high bit set, to check that the parser isn't pre-masking the high bit

Check that the encoding is 32 bytes exactly

Check that the encoding itself matches the usual one
This should panic in debug mode.
When the input is unreduced, we may only recover the scalar mod l.
For each valid radix it tests that 1000 random-ish scalars can be restored
from the produced representation precisely.
The largest unreduced scalar, s = 2^255-1. This is not reduced mod l. Scalar mult
still works though.

Tests consistency of From<{integer}> impls for Scalar

For `x` in `u8`, `u16`, `u32`, `u64`, and `u128`, check that
`Scalar::from(x + 1) == Scalar::from(x) + Scalar::from(1)`

ROOT_OF_UNITY^{2^s} mod m == 1

DELTA^{t} mod m == 1
We should get back either the positive or negative root.
One byte short

Check that a * b == a.reduce() * a.reduce() for ANY scalars a,b, even ones that violate
invariant #1, i.e., a,b > 2^255. Old versions of ed25519-dalek did multiplication where a
was reduced and b was clamped and unreduced. This checks that was always well-defined.
Also define c that's clamped. We'll make sure that clamping doesn't affect
computation

Make sure this is the same product no matter how you cut it

## src/scalar_verus.rs

scalar_verus.rs

This module provides functionality for...

Currently natural language definitions for all the public api functions in scalar.rs

use vstd::arithmetic::power2::*;

use the shared verus definitions

#### Constants

- Prime order of the Ristretto group and the Ed25519 basepoint:
ℓ = 2^{252} + 27742317777372353535851937790883648493

- Cofactor of curve25519:
h = 8

In all cases the 32 byte value is interpreted as an integer in little endian format (`as_nat_32_u8`)

#### Specification for:
`curve25519_dalek::scalar::Scalar`
`pub fn from_bytes_mod_order(bytes: [u8; 32]) -> Scalar`

1. Result is equal to the input mod ℓ

#### Specification for:
`curve25519_dalek::scalar::Scalar`
`pub fn from_bytes_mod_order_wide(input: &[u8; 64]) -> Scalar`

1. Result is equal to the input mod ℓ

#### Specification for:
`curve25519_dalek::scalar::Scalar`
`pub fn from_canonical_bytes(bytes: [u8; 32]) -> CtOption<Scalar>``

1. Outputs none if input represents an integer which is greater than of equal to ℓ
2. Otherwise outputs the input

#### Specification for:
curve25519_dalek::scalar::Scalar
pub const ZERO

1. Equal to 0

#### Specification for:
curve25519_dalek::scalar::Scalar
pub const ONE

1. Equal to 1

#### Specification for:
curve25519_dalek::scalar::Scalar
pub fn random<R>(rng: &mut R) -> Self

1. Returns a valid scalar (i.e., corresponds to an integer in {0, 1,..., ℓ - 1})
2. Uniformly random in {0, 1,..., ℓ - 1}

#### Specification for:
curve25519_dalek::scalar::Scalar
pub fn hash_from_bytes<D>(input: &[u8]) -> Scalar

1. Output is a valid scalar, i.e. an integer less than ℓ
2. Function is deterministic, same input always gives the same output
3. Uniform distribution in {0, 1,..., ℓ - 1}

#### Specification for:
curve25519_dalek::scalar::Scalar
pub fn from_hash<D>(hash: D) -> Scalar

1. Output is a valid scalar, i.e. an integer less than ℓ
2. Function is deterministic, same input always gives the same output
3. Uniform distribution in {0, 1,..., ℓ - 1}

#### Specification for:
curve25519_dalek::scalar::Scalar
pub const fn to_bytes(&self) -> [u8; 32]

1. Output equal to self

#### Specification for:
curve25519_dalek::scalar::Scalar
pub const fn as_bytes(&self) -> [u8; 32]

1. Output equal to self (same as above but pointer version)

#### Specification for:
curve25519_dalek::scalar::Scalar
pub fn invert(&self) -> Scalar

1. If self ≠ 0, self * result = 1 (mod ℓ)

#### Specification for:
curve25519_dalek::scalar::Scalar
pub fn batch_invert(inputs: &mut [Scalar]) -> Scalar

1. Same as above but for a batch of scalars

#### Specification for:
curve25519_dalek::scalar::Scalar
pub(crate) fn bits_le(&self) -> impl DoubleEndedIterator<Item = bool> + '_

1. Output is equal to self

#### Specification for:
curve25519_dalek::scalar::Scalar
pub(crate) fn non_adjacent_form(&self, w: usize) -> [i8; 256]
Permitted in source only for (2 <= w <= 8)
Called "w-Non-Adjacent Form"

let n_i denote the output

1. k = \sum_i n_i 2^i,
2. each nonzero coefficient n_i is odd
3. each nonzero coefficient is bounded |n_i| < 2^{w-1}
4. n_{m-1} is nonzero
5. at most one of any w consecutive coefficients is nonzero

#### Specification for:
curve25519_dalek::scalar::Scalar
pub(crate) fn as_radix_16(&self) -> [i8; 64]

let a_i denote the output

Requires that self < 2^{255}
1. a = a_0 + a_1 16^1 + \cdots + a_{63} 16^{63}
2. -8 <= a_i < 8

#### Specification for:
curve25519_dalek::scalar::Scalar
pub(crate) fn to_radix_2w_size_hint(w: usize) -> usize

Unclear how to specify, returns a size hint indicating how many entries
of the return value of `to_radix_2w` are nonzero.
Might not be relevant except for speed concerns.

#### Specification for:
curve25519_dalek::scalar::Scalar
pub(crate) fn as_radix_2w(&self, w: usize) -> [i8; 64]
Permitted in source only for w = 4, 5, 6, 7, 8

let a_i denote the output coefficients

1. a = a_0 + a_1 2^1 w + \cdots + a_{n-1} 2^{w*(n-1)}
2. -2^w/2 \leq a_i < 2^w/2 if 0 \leq i < (n-1)
3. -2^w/2 \leq a_{n-1} \leq 2^w/2

#### Specification for:
curve25519_dalek::scalar::Scalar
pub(crate) fn unpack(&self) -> UnpackedScalar

1. The output (5 52-bit limbs) represents the same integer as the 32 byte input

#### Specification for:
curve25519_dalek::scalar::Scalar52
pub fn montgomery_invert(&self) -> UnpackedScalar

1. If self is in montgomery form then output is the inverse

#### Specification for:
curve25519_dalek::scalar::Scalar52
pub fn invert(&self) -> UnpackedScalar

1. self * result = 1 (mod ℓ) (surely self ≠ 0 is required although not stated in the docs)

#### Specification for:
`curve25519_dalek::scalar``
`pub const fn clamp_integer(mut bytes: [u8; 32]) -> [u8; 32]`

Let n denote the 32 byte output interpreted as an integer in little endian format (`as_nat_32_u8`)

1. 2^254 ≤ n
2. n < 2^255
3. n is divisible by 8 (the cofactor of curve25519)
4. If the input is uniformly random then the output is uniformly random

[Further info](https://neilmadden.blog/2020/05/28/whats-the-curve25519-clamping-all-about/)

## src/traits.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Module for common traits.

### Public Traits

Trait for getting the identity element of a point type.

Returns the identity element of the curve.
Can be used as a constructor.

Trait for testing if a curve point is equivalent to the identity point.

Return true if this element is the identity element of the curve.

Implement generic identity equality testing for a point representations
which have constant-time equality testing and a defined identity
constructor.

A precomputed table of basepoints, for optimising scalar multiplications.

The type of point contained within this table.

Generate a new precomputed basepoint table from the given basepoint.

Retrieve the original basepoint from this table.

Multiply a `scalar` by this precomputed basepoint table, in constant time.

Multiply `clamp_integer(bytes)` by this precomputed basepoint table, in constant time. For
a description of clamping, see [`clamp_integer`].

Basepoint multiplication is defined for all values of `bytes` up to and including
2^255 - 1. The limit comes from the fact that scalar.as_radix_16() doesn't work for
most scalars larger than 2^255.

A trait for constant-time multiscalar multiplication without precomputation.

The type of point being multiplied, e.g., `RistrettoPoint`.

Given an iterator of (possibly secret) scalars and an iterator of
public points, compute
$$
Q = c_1 P_1 + \cdots + c_n P_n.
$$

It is an error to call this function with two iterators of different lengths.

### Examples

The trait bound aims for maximum flexibility: the inputs must be
convertible to iterators (`I: IntoIter`), and the iterator's items
must be `Borrow<Scalar>` (or `Borrow<Point>`), to allow
iterators returning either `Scalar`s or `&Scalar`s.

```
### #[cfg(feature = "alloc")]
### {
use curve25519_dalek::constants;
use curve25519_dalek::traits::MultiscalarMul;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;

// Some scalars
let a = Scalar::from(87329482u64);
let b = Scalar::from(37264829u64);
let c = Scalar::from(98098098u64);

// Some points
let P = constants::RISTRETTO_BASEPOINT_POINT;
let Q = P + P;
let R = P + Q;

// A1 = a*P + b*Q + c*R
let abc = [a,b,c];
let A1 = RistrettoPoint::multiscalar_mul(&abc, &[P,Q,R]);
// Note: (&abc).into_iter(): Iterator<Item=&Scalar>

// A2 = (-a)*P + (-b)*Q + (-c)*R
let minus_abc = abc.iter().map(|x| -x);
let A2 = RistrettoPoint::multiscalar_mul(minus_abc, &[P,Q,R]);
// Note: minus_abc.into_iter(): Iterator<Item=Scalar>

assert_eq!(A1.compress(), (-A2).compress());
### }
```

A trait for variable-time multiscalar multiplication without precomputation.

The type of point being multiplied, e.g., `RistrettoPoint`.

Given an iterator of public scalars and an iterator of
`Option`s of points, compute either `Some(Q)`, where
$$
Q = c_1 P_1 + \cdots + c_n P_n,
$$
if all points were `Some(P_i)`, or else return `None`.

This function is particularly useful when verifying statements
involving compressed points.  Accepting `Option<Point>` allows
inlining point decompression into the multiscalar call,
avoiding the need for temporary buffers.
```
###[cfg(feature = "alloc")]
### {
use curve25519_dalek::constants;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;

// Some scalars
let a = Scalar::from(87329482u64);
let b = Scalar::from(37264829u64);
let c = Scalar::from(98098098u64);
let abc = [a,b,c];

// Some points
let P = constants::RISTRETTO_BASEPOINT_POINT;
let Q = P + P;
let R = P + Q;
let PQR = [P, Q, R];

let compressed = [P.compress(), Q.compress(), R.compress()];

// Now we can compute A1 = a*P + b*Q + c*R using P, Q, R:
let A1 = RistrettoPoint::vartime_multiscalar_mul(&abc, &PQR);

// Or using the compressed points:
let A2 = RistrettoPoint::optional_multiscalar_mul(
&abc,
compressed.iter().map(|pt| pt.decompress()),
);

assert_eq!(A2, Some(A1));

// It's also possible to mix compressed and uncompressed points:
let A3 = RistrettoPoint::optional_multiscalar_mul(
abc.iter()
.chain(abc.iter()),
compressed.iter().map(|pt| pt.decompress())
.chain(PQR.iter().map(|&pt| Some(pt))),
);

assert_eq!(A3, Some(A1+A1));
### }
```

Given an iterator of public scalars and an iterator of
public points, compute
$$
Q = c_1 P_1 + \cdots + c_n P_n,
$$
using variable-time operations.

It is an error to call this function with two iterators of different lengths.

### Examples

The trait bound aims for maximum flexibility: the inputs must be
convertible to iterators (`I: IntoIter`), and the iterator's items
must be `Borrow<Scalar>` (or `Borrow<Point>`), to allow
iterators returning either `Scalar`s or `&Scalar`s.

```
###[cfg(feature = "alloc")]
### {
use curve25519_dalek::constants;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;

// Some scalars
let a = Scalar::from(87329482u64);
let b = Scalar::from(37264829u64);
let c = Scalar::from(98098098u64);

// Some points
let P = constants::RISTRETTO_BASEPOINT_POINT;
let Q = P + P;
let R = P + Q;

// A1 = a*P + b*Q + c*R
let abc = [a,b,c];
let A1 = RistrettoPoint::vartime_multiscalar_mul(&abc, &[P,Q,R]);
// Note: (&abc).into_iter(): Iterator<Item=&Scalar>

// A2 = (-a)*P + (-b)*Q + (-c)*R
let minus_abc = abc.iter().map(|x| -x);
let A2 = RistrettoPoint::vartime_multiscalar_mul(minus_abc, &[P,Q,R]);
// Note: minus_abc.into_iter(): Iterator<Item=Scalar>

assert_eq!(A1.compress(), (-A2).compress());
### }
```

A trait for variable-time multiscalar multiplication with precomputation.

A general multiscalar multiplication with precomputation can be written as
$$
Q = a_1 A_1 + \cdots + a_n A_n + b_1 B_1 + \cdots + b_m B_m,
$$
where the $B_i$ are *static* points, for which precomputation
is possible, and the $A_j$ are *dynamic* points, for which
precomputation is not possible.

This trait has three methods for performing this computation:

* [`Self::vartime_multiscalar_mul`], which handles the special case where
$n = 0$ and there are no dynamic points;

* [`Self::vartime_mixed_multiscalar_mul`], which takes the dynamic points as
already-validated `Point`s and is infallible;

* [`Self::optional_mixed_multiscalar_mul`], which takes the dynamic points
as `Option<Point>`s and returns an `Option<Point>`, allowing decompression
to be composed into the input iterators.

All methods require that the lengths of the input iterators be
known, as if they were `ExactSizeIterator`s.  (It
does not require `ExactSizeIterator` only because that trait is
broken).

The type of point to be multiplied, e.g., `RistrettoPoint`.

Given the static points $ B_i $, perform precomputation
and return the precomputation data.

Return the number of static points in the precomputation.

Determine if the precomputation is empty.

Given `static_scalars`, an iterator of public scalars
$b_i$, compute
$$
Q = b_1 B_1 + \cdots + b_m B_m,
$$
where the $B_j$ are the points that were supplied to `new`.

It is valid for $b_i$ to have a shorter length than $B_j$.
In this case, any "unused" points are ignored in the computation.
It is an error to call this function if $b_i$ has a longer
length than $B_j$.

The trait bound aims for maximum flexibility: the input must
be convertible to iterators (`I: IntoIter`), and the
iterator's items must be `Borrow<Scalar>`, to allow iterators
returning either `Scalar`s or `&Scalar`s.

Given `static_scalars`, an iterator of public scalars
$b_i$, `dynamic_scalars`, an iterator of public scalars
$a_i$, and `dynamic_points`, an iterator of points
$A_i$, compute
$$
Q = a_1 A_1 + \cdots + a_n A_n + b_1 B_1 + \cdots + b_m B_m,
$$
where the $B_j$ are the points that were supplied to `new`.

It is valid for $b_i$ to have a shorter length than $B_j$.
In this case, any "unused" points are ignored in the computation.
It is an error to call this function if $b_i$ has a longer
length than $B_j$, or if $a_i$ and $A_i$ do not have
the same length.

The trait bound aims for maximum flexibility: the inputs must be
convertible to iterators (`I: IntoIter`), and the iterator's items
must be `Borrow<Scalar>` (or `Borrow<Point>`), to allow
iterators returning either `Scalar`s or `&Scalar`s.

Given `static_scalars`, an iterator of public scalars
$b_i$, `dynamic_scalars`, an iterator of public scalars
$a_i$, and `dynamic_points`, an iterator of points
$A_i$, compute
$$
Q = a_1 A_1 + \cdots + a_n A_n + b_1 B_1 + \cdots + b_m B_m,
$$
where the $B_j$ are the points that were supplied to `new`.

If any of the dynamic points were `None`, return `None`.

It is valid for $b_i$ to have a shorter length than $B_j$.
In this case, any "unused" points are ignored in the computation.
It is an error to call this function if $b_i$ has a longer
length than $B_j$, or if $a_i$ and $A_i$ do not have
the same length.

This function is particularly useful when verifying statements
involving compressed points.  Accepting `Option<Point>` allows
inlining point decompression into the multiscalar call,
avoiding the need for temporary buffers.

### Private Traits

Trait for checking whether a point is on the curve.

This trait is only for debugging/testing, since it should be
impossible for a `curve25519-dalek` user to construct an invalid
point.
Checks whether the point is on the curve. Not CT.

## src/window.rs


This file is part of curve25519-dalek.
Copyright (c) 2016-2021 isis lovecruft
Copyright (c) 2016-2019 Henry de Valence
See LICENSE for licensing information.

Authors:
- isis agora lovecruft <isis@patternsinthevoid.net>
- Henry de Valence <hdevalence@hdevalence.ca>

Code for fixed- and sliding-window functionality
A lookup table of precomputed multiples of a point $P$, used to
compute $ xP $ for $ -8 \leq x \leq 8 $.

The computation of $ xP $ is done in constant time by the `select` function.

Since `LookupTable` does not implement `Index`, it's more difficult
to accidentally use the table directly.  Unfortunately the table is
only `pub(crate)` so that we can write hardcoded constants, so it's
still technically possible.  It would be nice to prevent direct
access to the table.
Given $-8 \leq x \leq 8$, return $xP$ in constant time.

Compute xabs = |x|

Set t = 0 * P = identity
Copy `points[j-1] == j*P` onto `t` in constant time if `|x| == j`.
Now t == |x| * P.
Now t == x * P.
XXX batch inversion would be good if perf mattered here

The first one has to be named "LookupTable" because it's used as a constructor for consts.
This is radix-16

The rest only get used to make basepoint tables
radix-32
radix-64
radix-128
radix-256

For homogeneity we then alias it to "LookupTableRadix16".

Holds odd multiples 1A, 3A, ..., 15A of a point A.
Given public, odd $ x $ with $ 0 < x < 2^4 $, return $xA$.
Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]

Holds stuff up to 8. The only time we use tables this big is for precomputed basepoint tables
and multiscalar multiplication (which requires alloc).
Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A, ..., 127A]
Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A, ..., 127A]

