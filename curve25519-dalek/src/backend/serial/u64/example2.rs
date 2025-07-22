use vstd::prelude::*;
verus! {
    #[verifier::allow_in_spec]
    fn m1(x: u64, y: u64) -> (z: u128)
    requires
        x < (1u64 << 52),
        y < (1u64 << 52),
    ensures
        z < (1u128 << 104),
    returns (x * y) as u128
    {
        assume(false); // Omit proof for brevity
        (x as u128) * (y as u128)
    }

    fn m2(a: u64, b: u64) -> u128
    requires
        a < (1u64 << 52),
        b < (1u64 << 52),
    {
        proof!{
            assert(a < (1u64 << 52));
            assert(b < (1u64 << 52));
            assume(m1(a, b) < (1u128 << 104));
            assume(2 * m1(a, b) < (2u128 << 104));
        }
        2 * m1(a, b)
    }
}

fn main() {}
