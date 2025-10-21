# Verus Style Guide

In order to ensure a readable and maintainable Verus codebase we adopt a number of conventions regarding the presentation of Verus code and our module management.

## Minimal Rust-source deviation

In order to use Verus it may sometimes be necessary to modify the underlying Rust code. The most simple example is `requres/ensures`, as well as naming the return value, so that it may be used in `ensures` statements, e.g.

```rust
fn foo(...) -> T
{ ... }
```

becomes
```rust
fn foo(...) -> (r: T)
    requires
        ...
    ensures
        bar(r)
{ ... }
```

We strongly advise adhering to the principle of minimal interference beyond the above. Concretely, whenever possible,
```rust
fn foo(...) -> T
{ 
    A;
    B;
    C;
    ...
}
```
should become 
```rust
fn foo(...) -> (r: T)
    ensures
        ...
{ 
    proof {
        proof_foo(...);
    }

    A;
    B;
    C;
    ...
}
```
with its proof delegated to a lemma, instead of interspersed proof statements

```rust
fn foo(...) -> (r: T)
    ensures
        ...
{ 
    A;

    proof {
        ...
    }

    B;

    proof {
        ...
    }

    C;

    proof {
        ...
    }

    ...
}
```

Sometimes, mostly in the presence of loops and loop invariants, such straightforward decomposition may not be possible. 
In those cases, use your judgement to determine what "minimal modifications" mean for the purposes of your particular function.

Given a module `foo.rs`, we generally recommend creating a directory `foo_lemmas` populated with various lemmas about the functions defined in `foo.rs` (or `foo_lemmas.rs` if additional granularity is unnecessary).

## Explicit proof statements

It is generally recommended to use `assert ... by` whenever possible.

Instead of 
```rust
// x / 1 = x
lemma_div_basics_2(x);
```
consider 
```rust
assert(x / 1 == x) by {
    lemma_div_basics_2(x);
}
```

This approach has a twofold benefit. First, it makes the flow of a proof easy to follow for any non-author reading the proof afterwards (notably, PR reviewers).
Second, it provides much greater proof stability, since the global scope only contains the statements inside `assume`, and not every possible consequence of all lemmas used to prove them.
Consider the following scenario:
```rust
proof {
    lemma1(...); // Directly implies P
    lemma2(...); // Directly implies Q, but R _can_ be derived from P /\ Q
    ...
    assert(...); // <- critically requires R
}
```
If `R` is a nontrivial consequence of `P` and `Q` the above proof may be unstable under the addition or removal of other code, since the implicit derivation of `R` may depend on solver nondeterminsim.
Instead, use
```rust
proof {
    assert(P) by { 
        lemma1(...);
    }
    assert(Q) by {
        lemma2(...);
    }
    ...
    assert(...) by {
        assert(R) by {
            ...
        }
    }
}
```
This way, the proof structure makes it clear that `R` is an explicitly considered consequence of `P` and `Q`, and necessary to the proof of the `assert`.

## Broadcast frugality

It may be tempting to leverage `broadcast use` liberally for proof brevity. 
However, depending on the lemma being broadcast, or more specifically, the commonality of its triggers, this may be a poor idea from the point of view of proof stability or resource consumption.
When deciding whether to simplify a proof via `broadcast use`, consider only doing so if you are reasonably certain that the trigger is not overly general. For example
```rust
broadcast use lemma_div_basics_2
```
is likely fine, since `lemma_div_basics_2` triggers only on expressions of the form `x / 1`, whereas
```rust
broadcast use lemma_mul_is_associative
```
is likely not a good idea, since the associativity trigger is _any_ multiplication of 3 terms:
```
#![trigger x * (y * z)]
#![trigger (x * y) * z]
```
which may have hundreds or thousands of matching patterns for longer proofs.

## Reminder `asserts`

It is sometimes helpful, though by no means necessary or required, to introduce "spurious" asserts, to remind a reader of a property already proven elsewhere, but relevant to a sub-goal in a later part of the proof. Consider
```
proof {
    let k: nat = ...;
    assert(k > 2) by {
        ...
    }
    ...
    assert(r < 3) by {
        assert(k > 2); // known
        ...
    }
}
```













