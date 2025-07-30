use vstd::prelude::*;
verus! {
    pub proof fn obviously()
        ensures
            1 < 2
    {
    }
}
