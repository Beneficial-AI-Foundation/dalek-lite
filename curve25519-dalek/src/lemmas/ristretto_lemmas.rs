#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::backend::serial::u64::constants::spec_eight_torsion;
#[allow(unused_imports)]
use crate::edwards::EdwardsPoint;
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[allow(unused_imports)]
use crate::specs::ristretto_specs::*;

use vstd::prelude::*;

verus! {

/// Given P and the 4-torsion elements T\[2\], T\[4\], T\[6\] from E\[8\],
/// proves that \[P, P+T\[2\], P+T\[4\], P+T\[6\]\] forms the Ristretto coset P + E\[4\].
pub proof fn lemma_coset4_correct(
    base: EdwardsPoint,
    t2: EdwardsPoint,
    t4: EdwardsPoint,
    t6: EdwardsPoint,
    p1: EdwardsPoint,
    p2: EdwardsPoint,
    p3: EdwardsPoint,
)
    requires
        t2 == spec_eight_torsion()[2],
        t4 == spec_eight_torsion()[4],
        t6 == spec_eight_torsion()[6],
        ({
            let (x1, y1) = edwards_point_as_affine(base);
            let (x2, y2) = edwards_point_as_affine(t2);
            edwards_point_as_affine(p1) == edwards_add(x1, y1, x2, y2)
        }),
        ({
            let (x1, y1) = edwards_point_as_affine(base);
            let (x2, y2) = edwards_point_as_affine(t4);
            edwards_point_as_affine(p2) == edwards_add(x1, y1, x2, y2)
        }),
        ({
            let (x1, y1) = edwards_point_as_affine(base);
            let (x2, y2) = edwards_point_as_affine(t6);
            edwards_point_as_affine(p3) == edwards_add(x1, y1, x2, y2)
        }),
    ensures
        is_ristretto_coset([base, p1, p2, p3], base),
{
    // proof follows directly.
    // block extracted as lemma to reduce Z3 context.
}

} // verus!
