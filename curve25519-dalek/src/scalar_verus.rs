use vstd::prelude::*;

verus! {

pub struct Scalar {
}

impl Scalar {
    pub const ONE: Self = Self {  };

    pub fn invert(&self) -> Scalar {
        Scalar::ONE
    }
}

fn main() {
}

} // verus!
