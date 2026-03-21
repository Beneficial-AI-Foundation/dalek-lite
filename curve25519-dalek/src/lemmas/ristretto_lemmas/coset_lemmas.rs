//! Ristretto coset edge-case lemmas.
//!
//! Proves that when x = 0 or y = 0, the Ristretto coset contains
//! the identity, 2-torsion, and both 4-torsion points.
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::ristretto_specs::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::sqrt_m1_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::torsion_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::number_theory_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

/// When x = 0 or y = 0, the Ristretto coset contains
/// the identity (0, 1), the 2-torsion (0, −1), and both 4-torsion points.
///
/// This follows from the bridge axiom `axiom_four_torsion_affine` plus
/// algebraic properties of edwards_add with E[4] elements.
pub proof fn lemma_edge_coset_contains_e4(x: nat, y: nat)
    requires
        x == 0 || y == 0,
        x < p(),
        y < p(),
        x == 0 ==> (y == 1 || y == field_neg(1)),
        y == 0 ==> field_square(x) == field_neg(1),
    ensures
        ({
            let coset = ristretto_coset_affine(x, y);
            let id = (0nat, 1nat);
            let i_pt = (sqrt_m1(), 0nat);
            let neg1_pt = (0nat, field_neg(1));
            let neg_i_pt = (field_neg(sqrt_m1()), 0nat);
            (id == coset[0] || id == coset[1] || id == coset[2] || id == coset[3]) && (i_pt
                == coset[0] || i_pt == coset[1] || i_pt == coset[2] || i_pt == coset[3]) && (
            neg_i_pt == coset[0] || neg_i_pt == coset[1] || neg_i_pt == coset[2] || neg_i_pt
                == coset[3])
        }),
{
    axiom_four_torsion_affine();
    p_gt_2();
    let i_val = sqrt_m1();
    let neg_i = field_neg(sqrt_m1());
    let neg_one = field_neg(1);
    let coset = ristretto_coset_affine(x, y);

    // Establish field_square(i_val) == field_neg(1)
    lemma_small_mod(1nat, p());
    lemma_small_mod((p() - 1) as nat, p());
    assert(field_square(i_val) == field_neg(1)) by {
        axiom_sqrt_m1_squared();
    };
    assert(i_val < p()) by {
        lemma_mod_bound(i_val as int, p() as int);
    };
    assert(neg_i < p()) by {
        lemma_mod_bound(neg_i as int, p() as int);
    };

    if x == 0 && y == 1 {
        // Identity: coset = [(0,1), (i,0), ..., (neg_i,0)]
        assert(coset[0] == (0nat, 1nat));
        assert(coset[1] == (i_val % p(), 0nat % p())) by {
            lemma_edwards_add_identity_left(i_val, 0);
        };
        assert(coset[3] == (neg_i % p(), 0nat % p())) by {
            lemma_edwards_add_identity_left(neg_i, 0);
        };
        lemma_small_mod(i_val, p());
        lemma_small_mod(neg_i, p());
        lemma_small_mod(0nat, p());
    } else if x == 0 && y == neg_one {
        // 2-torsion: coset = [(0,neg1), (neg_i,0), (0,1), (i,0)]
        assert(coset[0] == (0nat, neg_one));
        assert(coset[2] == (0nat, 1nat)) by {
            lemma_edwards_add_two_torsion_self();
        };
        assert(coset[1] == (neg_i, 0nat)) by {
            lemma_edwards_add_two_torsion_four_torsion(i_val);
        };
        assert(coset[3] == (i_val % p(), 0nat)) by {
            lemma_edwards_add_two_torsion_four_torsion_neg(i_val);
        };
        lemma_small_mod(i_val, p());
    } else {
        // y == 0 and x != 0: 4-torsion point (x, 0) with x² = -1
        assert(y == 0);

        // coset[2] = edwards_add(x, 0, 0, neg_one) = (neg(x), 0)
        assert(coset[2] == (field_neg(x), 0nat)) by {
            lemma_edwards_add_four_torsion_with_two_torsion(x);
        };

        // x is sqrt_m1() or neg(sqrt_m1()) (only square roots of -1 in GF(p))
        assert(x == i_val || x == neg_i) by {
            lemma_sqrt_m1_nonzero();
            assert((x * x) % p() == (p() - 1) as nat) by {
                lemma_small_mod((p() - 1) as nat, p());
            };
            lemma_square_root_of_neg_one(x, i_val);
            lemma_small_mod(x, p());
            lemma_small_mod(i_val, p());
        };

        if x == i_val {
            assert(coset[3] == (0nat, 1nat)) by {
                lemma_edwards_add_four_torsion_with_neg(x);
            };
        } else {
            // x == neg_i
            assert(field_neg(neg_i) == i_val % p()) by {
                lemma_field_neg_neg(i_val);
            };
            lemma_small_mod(i_val, p());
            assert(field_square(neg_i) == field_neg(1)) by {
                lemma_neg_square_eq(i_val);
                lemma_small_mod(i_val, p());
            };
            assert(coset[1] == (0nat, 1nat)) by {
                lemma_edwards_add_four_torsion_with_neg(neg_i);
            };
        }
    }
}

} // verus!
