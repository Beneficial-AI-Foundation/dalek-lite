use vstd::prelude::*;

verus!{

#[verifier::allow_in_spec]
fn sum(a: u64, b: u64) -> u64
    requires a < 10 && b < 10
    returns (a+b) as u64
{
  return a+b;
}

fn sum2(a: u64, b: u64) -> (z: u64)
    requires a < 10 && b < 10
    //ensures z == sum(a, b)
    //ensures 4 == sum(2, 2)
{
    let z = a + b;
    assert(z == sum(a, b));
    //assert(4 == sum(2, 2));
    //return z;
    return 0;
}

}

fn main()
{}
