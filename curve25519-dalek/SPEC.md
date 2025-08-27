# Specifications

Montgomery/Edwards defs:
- Take some field `F`, e.g. `Z/pZ` for some prime `p`.
- A Montgomery curve over `F` is given by `By^2 = x^3 + Ax^2 + x`, `B(A^2 - 4) /= 0`
- A twisted Edwards curve over `F` is given by `a * x^2 + y^2 = 1 + d * x^2 * y^2`
- For `Curve25519`, `B = 1` and `A = 486662`
- For `Ed25519`, `a = -1` and `d = 121665 / 121666`

Overall idea:
- Basepoint `x = 9` (100% arbitrary, but almost any point works) generates a cyclic subgroup on `Curve25519` (Montgomery).
- The Montgomery curve is birationally equivalent to the Edwards curve. Not an isomorphism.
- `y = 4/5` is the generator on `Ed25519` (Edwards) mapped from the basepoint (by the relation `y_edwards = (x_montgomery - 1) / (x_montgomery + 1) = 8/10 = 4/5`)
- `y = 4/5` then generates a cyclic subgroup on `Ed25519` of the same order (`2^252 + 27742317777372353535851937790883648493`)

Why use both:
- X25519 provides a very simple, constant time, and fast variable-base (when the input point of the scalar multiplication is not known in advance) scalar multiplication algorithms
- Ed25519 instead provides a very fast fixed-base (when the input point of the scalar multiplication is known at design time) scalar multiplication

Conclusions: 
- `Curve25519` for key share, `Ed25519` for signatures, 
- const-time is unnecessary for signature verification
- see [this discussion](https://crypto.stackexchange.com/questions/27866/why-curve25519-for-encryption-but-ed25519-for-signatures)


Why do `field` and `scalar` use different primes?
- `field` defines the field the Montgomery/Edwards curves are defined over. We use `Z/pZ` for the prime `p = 2^255 - 19`. These are our curve coordinates.
- On the curves, we're taking cyclic groups, i.e. groups of multiples of some basepoint `B`, `<k * B>`. These groups have order `l = 2^252 + 27742317777372353535851937790883648493`, meaning `l * B = 0`. Thus, if `x == y (mod l)` then `x * B = y * B`. Note that `k * (x, y)` is not, in general, `(k * x, k * y)`.

TODO: Ristretto

## `curve25519-dalek/curve25519-dalek/src/constants.rs`

### `ED25519_BASEPOINT_COMPRESSED`
- The Ed25519 basepoint `B`, in `CompressedEdwardsY` format
- `B` is the unique curve point `(x,4/5)` (`mod p`) for which `x` is positive 
- This stores the `Y`-coordinate (in projective coordinates)

```rust
ED25519_BASEPOINT_COMPRESSED.decompress() == Some(ED25519_BASEPOINT_POINT)

P.to_montgomery() == X25519_BASEPOINT
```

### `X25519_BASEPOINT`
- The X25519 basepoint, in `MontgomeryPoint` format
- `x = 9`
- Generates cyclic subgroup of order `as_nat_32_u8(BASEPOINT_ORDER)`

```rust

X25519_BASEPOINT.to_edwards(0) == ED25519_BASEPOINT_POINT

```

### `RISTRETTO_BASEPOINT_COMPRESSED`
- The Ristretto basepoint, in `CompressedRistretto` format

```rust
RISTRETTO_BASEPOINT_COMPRESSED.decompress() == Some(RISTRETTO_BASEPOINT_POINT)
```

### `BASEPOINT_ORDER`
- `BASEPOINT_ORDER` is the order of the Ristretto group and of the Ed25519 basepoint

```rust
as_nat_32_u8(BASEPOINT_ORDER) == pow2(252) + 27742317777372353535851937790883648493
```

## `curve25519-dalek/curve25519-dalek/src/edwards.rs`

### `compress/decompress`
```rust
e: EdwardsPoint
e.compress().decompress() == Some(e)

e: CompressedEdwardsY
e.decompress() == Some(P)
P.compress() == e
```

### `to_montgomery`

```rust
e.to_montgomery().to_edwards() == Some(e)
```

### `double`

```rust
e.double() == e.add(e)
```

### `neg`

```rust
e.neg().neg() == e

e.add(b.neg()) == e.sub(b)
```

### `mul`

```rust
mul(2, e) == e.double()
```

### `mul_clamped`

```rust
e.mul_clamped(bts) == TODO
```



