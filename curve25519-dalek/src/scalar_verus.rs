use vstd::prelude::*;

verus! {

pub struct Scalar {
    pub bytes: [u8; 1],
}

impl Scalar {
    pub const ONE: Self = Self { bytes: [1] };

    pub fn invert(&self) -> Scalar {
        Scalar::ONE
    }
}

fn main() {
}

} // verus!
