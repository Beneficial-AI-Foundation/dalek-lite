use vstd::prelude::*;

verus! {

pub struct Foo {
}

impl Foo {
    pub const BAR: Self = Self {  };

    pub fn get_bar(&self) -> Foo {
        Foo::BAR
    }
}

fn main() {
}

} // verus!
