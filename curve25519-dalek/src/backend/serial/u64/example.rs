// So far it seems like the fix is always to put in
// the preconditions in the ensures clause, and then
// the panic stops. But this doesn't seem to work for mul
use vstd::prelude::*;

verus!{

#[verifier::allow_in_spec]
fn sum(a: u64, b: u64) -> u64
    requires a < 10 && b < 10
    returns (a+b) as u64
{
  return a+b;
}

#[verifier::allow_in_spec]
fn first(a: u64, b: u64) -> u64
    returns a
{
  return a;
}

fn sum4(a: u64, b: u64) -> (z: u64)
{
    let z = first(a, b);
    assert(z == first(a, b));
    return 0;
}

fn sum2(a: u64, b: u64) -> (z: u64)
    requires a < 10 && b < 10
    //ensures z == sum(a, b)
    //ensures 4 == sum(2, 2)
{
    let z = a + b;
    //assert(z == sum(a, 12));
    //assert(4 == sum(2, 2));
    //return z;
    return 0;
}

fn sum3(a: [u64; 5]) -> (z: u64)
    requires forall|i: int| a[i] < 10
    //ensures a[0] < 10,
    //        a[1] < 10
    //ensures 4 == sum(2, 2)
{
    let z = a[0] + a[1];
    assert(z == sum(a[0], a[1]));
    //assert(4 == sum(2, 2));
    //return z;
    return 0;
}

}

fn main()
{}
