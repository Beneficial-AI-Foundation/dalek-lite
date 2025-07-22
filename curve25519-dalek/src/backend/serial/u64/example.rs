use vstd::prelude::*;

verus!{
fn sum(a: u64, b: u64) -> u64
    requires a < 10 && b < 10
    returns (a+b) as u64
{
  return a+b;
}


}

fn main()
{}
