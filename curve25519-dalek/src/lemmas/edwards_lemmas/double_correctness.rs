//! Correctness of the projective doubling formula for twisted Edwards curves.
//!
//! Proves that `ProjectivePoint::double()` correctly computes the Edwards
//! group doubling and produces a valid `CompletedPoint`.
//!
//! Given a projective point P = (X:Y:Z) with affine (x,y) = (X/Z, Y/Z):
//!
//!   XX = X²,  YY = Y²,  ZZ2 = 2·Z²
//!   XpY_sq = (X+Y)²,  YYpXX = YY+XX,  YYmXX = YY-XX
//!   result.X = XpY_sq - YYpXX = 2XY
//!   result.Y = YYpXX = Y²+X²
//!   result.Z = YYmXX = Y²-X²
//!   result.T = ZZ2 - YYmXX = 2Z²-(Y²-X²)
//!
//! Proof strategy:
//!   1. Factor: all result components share the projective factor Z²
//!   2. Curve eq: use y²-x² = 1+d·x²y² to identify result.Z, result.T as Z²·(1±t)
//!   3. Nonzero: axiom_edwards_add_complete(x,y,x,y) gives 1+t ≠ 0, 1-t ≠ 0
//!   4. Cancel: divide out Z² to get affine ratios matching edwards_add(x,y,x,y)
#[allow(unused_imports)]
use crate::backend::serial::curve_models::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::constants::EDWARDS_D;
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::niels_addition_correctness::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Bridge lemma: the projective doubling formulas produce a valid CompletedPoint
/// whose affine projection equals `edwards_double(x, y)`.
pub proof fn lemma_double_projective_completed_valid(
    self_point: ProjectivePoint,
    result: CompletedPoint,
    xx_val: nat,
    yy_val: nat,
    zz2_val: nat,
    xpy_sq_val: nat,
)
    requires
        is_valid_projective_point(self_point),
        xx_val == field_square(fe51_as_canonical_nat(&self_point.X)),
        yy_val == field_square(fe51_as_canonical_nat(&self_point.Y)),
        zz2_val == field_mul(2, field_square(fe51_as_canonical_nat(&self_point.Z))),
        xpy_sq_val == field_square(
            field_add(fe51_as_canonical_nat(&self_point.X), fe51_as_canonical_nat(&self_point.Y)),
        ),
        fe51_as_canonical_nat(&result.X) == field_sub(xpy_sq_val, field_add(yy_val, xx_val)),
        fe51_as_canonical_nat(&result.Y) == field_add(yy_val, xx_val),
        fe51_as_canonical_nat(&result.Z) == field_sub(yy_val, xx_val),
        fe51_as_canonical_nat(&result.T) == field_sub(zz2_val, field_sub(yy_val, xx_val)),
    ensures
        is_valid_completed_point(result),
        completed_point_as_affine_edwards(result) == edwards_double(
            projective_point_as_affine_edwards(self_point).0,
            projective_point_as_affine_edwards(self_point).1,
        ),
{
    let pX = fe51_as_canonical_nat(&self_point.X);
    let pY = fe51_as_canonical_nat(&self_point.Y);
    let pZ = fe51_as_canonical_nat(&self_point.Z);
    let p = p();
    let p_i = p as int;

    assert(p > 2) by {
        p_gt_2();
    };

    assert(pX < p) by {
        lemma_mod_bound(u64_5_as_nat(self_point.X.limbs) as int, p_i);
    }
    assert(pY < p) by {
        lemma_mod_bound(u64_5_as_nat(self_point.Y.limbs) as int, p_i);
    }
    assert(pZ < p) by {
        lemma_mod_bound(u64_5_as_nat(self_point.Z.limbs) as int, p_i);
    }

    // Z is nonzero (from is_valid_projective_point)
    assert(pZ != 0);
    assert(pZ % p != 0) by {
        lemma_field_element_reduced(pZ);
    };

    // Affine coordinates
    let z_inv = field_inv(pZ);
    let x = field_mul(pX, z_inv);
    let y = field_mul(pY, z_inv);

    // (x, y) is on the curve
    assert(math_on_edwards_curve(x, y)) by {
        lemma_projective_implies_affine_on_curve(pX, pY, pZ);
    };

    // Field values we'll use throughout
    let z2 = field_square(pZ);
    let x2 = field_square(x);
    let y2 = field_square(y);
    let xy = field_mul(x, y);
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let t = field_mul(d, field_mul(x2, y2));

    // Bounds (all field values are < p)
    assert(x < p) by {
        lemma_mod_bound((pX * z_inv) as int, p_i);
    }
    assert(y < p) by {
        lemma_mod_bound((pY * z_inv) as int, p_i);
    }
    assert(z2 < p) by {
        lemma_mod_bound((pZ * pZ) as int, p_i);
    }
    assert(x2 < p) by {
        lemma_mod_bound((x * x) as int, p_i);
    }
    assert(y2 < p) by {
        lemma_mod_bound((y * y) as int, p_i);
    }
    assert(xy < p) by {
        lemma_mod_bound((x * y) as int, p_i);
    }

    // -----------------------------------------------------------------------
    // STEP 1: Factor projective squares through Z²
    //   X·X = (X/Z)·(X/Z)·Z·Z, i.e. X² = x²·Z²
    // -----------------------------------------------------------------------
    assert(xx_val == field_mul(x2, z2)) by {
        lemma_projective_product_factor(pX, pZ, pX, pZ);
    };
    assert(yy_val == field_mul(y2, z2)) by {
        lemma_projective_product_factor(pY, pZ, pY, pZ);
    };
    assert(field_mul(pX, pY) == field_mul(xy, z2)) by {
        lemma_projective_product_factor(pX, pZ, pY, pZ);
    };

    // -----------------------------------------------------------------------
    // STEP 2: result.X = (X+Y)² - (Y²+X²) = 2·X·Y via binomial expansion
    // -----------------------------------------------------------------------
    assert(fe51_as_canonical_nat(&result.X) == field_mul(2, field_mul(pX, pY))) by {
        lemma_square_sum_expansion(pX, pY);
    };

    // 2·(xy·Z²) = Z²·(2·xy)
    assert(fe51_as_canonical_nat(&result.X) == field_mul(z2, field_mul(2, xy))) by {
        lemma_reassociate_2_z_num(z2, xy);
    };

    // -----------------------------------------------------------------------
    // STEP 3: result.Y = Y²+X² = y²·Z² + x²·Z² = Z²·(y²+x²)
    // -----------------------------------------------------------------------
    assert(fe51_as_canonical_nat(&result.Y) == field_mul(z2, field_add(y2, x2))) by {
        lemma_factor_result_component_add(y2, x2, z2);
    };

    // -----------------------------------------------------------------------
    // STEP 4: result.Z = Y²-X² = Z²·(y²-x²)
    // -----------------------------------------------------------------------
    assert(fe51_as_canonical_nat(&result.Z) == field_mul(z2, field_sub(y2, x2))) by {
        lemma_factor_result_component_sub(y2, x2, z2);
    };

    // Curve equation: y²-x² = 1+t
    assert(field_sub(y2, x2) == field_add(1, t));
    assert(fe51_as_canonical_nat(&result.Z) == field_mul(z2, field_add(1, t)));

    // -----------------------------------------------------------------------
    // STEP 5: result.T = 2Z² - (Y²-X²) = Z²·(2-(y²-x²)) = Z²·(1-t)
    // -----------------------------------------------------------------------
    assert(field_mul(2, z2) == field_mul(z2, 2nat)) by {
        lemma_field_mul_comm(2nat, z2);
    };
    assert(fe51_as_canonical_nat(&result.T) == field_mul(z2, field_sub(2nat, field_sub(y2, x2))))
        by {
        lemma_factor_result_component_sub(2nat, field_sub(y2, x2), z2);
    };

    // 2 - (1+t) = 1 - t   (cancel common addend 1)
    assert(field_sub(2nat, field_add(1, t)) == field_sub(1, t)) by {
        assert(field_add(1nat, 1nat) == 2nat) by {
            lemma_small_mod(2nat, p);
        };
        assert(field_add(t, 1nat) == field_add(1nat, t)) by {
            lemma_field_add_comm(t, 1nat);
        };
        assert(1nat < p) by {
            lemma_small_mod(1nat, p);
        };
        assert(t < p) by {
            lemma_mod_bound((d * field_mul(x2, y2)) as int, p_i);
        };
        lemma_field_sub_add_common_right(1nat, t, 1nat);
    };
    assert(fe51_as_canonical_nat(&result.T) == field_mul(z2, field_sub(1, t)));

    // -----------------------------------------------------------------------
    // STEP 6: Nonzero denominators via axiom_edwards_add_complete
    // -----------------------------------------------------------------------
    axiom_edwards_add_complete(x, y, x, y);
    // Gives: field_add(1, t) != 0 && field_sub(1, t) != 0

    // Z² != 0
    assert(z2 != 0) by {
        lemma_nonzero_product(pZ, pZ);
    };
    assert(z2 % p != 0) by {
        lemma_field_element_reduced(z2);
    };

    assert(field_add(1, t) % p != 0) by {
        lemma_field_element_reduced(field_add(1, t));
    };
    assert(field_sub(1, t) % p != 0) by {
        assert(field_sub(1, t) < p) by {
            lemma_mod_bound((field_canonical(1) + p - field_canonical(t)) as int, p_i);
        };
        lemma_field_element_reduced(field_sub(1, t));
    };

    // result.Z != 0 and result.T != 0
    assert(fe51_as_canonical_nat(&result.Z) != 0) by {
        lemma_nonzero_product(z2, field_add(1, t));
    };
    assert(fe51_as_canonical_nat(&result.T) != 0) by {
        lemma_nonzero_product(z2, field_sub(1, t));
    };

    // -----------------------------------------------------------------------
    // STEP 7: Cancel Z² from ratios to get affine coordinates
    //   (Z²·a) / (Z²·b) = a/b
    // -----------------------------------------------------------------------
    assert(field_mul(fe51_as_canonical_nat(&result.X), field_inv(fe51_as_canonical_nat(&result.Z)))
        == field_mul(field_mul(2, xy), field_inv(field_add(1, t)))) by {
        lemma_cancel_common_factor(field_mul(2, xy), field_add(1, t), z2);
    };
    assert(field_mul(fe51_as_canonical_nat(&result.Y), field_inv(fe51_as_canonical_nat(&result.T)))
        == field_mul(field_add(y2, x2), field_inv(field_sub(1, t)))) by {
        lemma_cancel_common_factor(field_add(y2, x2), field_sub(1, t), z2);
    };

    // -----------------------------------------------------------------------
    // STEP 8: Connect to edwards_add(x, y, x, y)
    //   In edwards_add: x1y2 = x·y = xy, y1x2 = y·x = xy
    //   so num_x = x1y2 + y1x2 = xy + xy = 2·xy
    //   and num_y = y1y2 + x1x2 = y² + x²
    //   and denom_x = 1+t, denom_y = 1-t
    // -----------------------------------------------------------------------
    assert(field_mul(y, x) == xy) by {
        lemma_field_mul_comm(y, x);
    };
    assert(field_add(xy, xy) == field_mul(2, xy)) by {
        lemma_add_self_eq_double(xy);
    };

    // Now the ratios match edwards_add(x, y, x, y):
    //   completed_point_as_affine_edwards(result).0 = 2xy/(1+t) = edwards_add(x,y,x,y).0
    //   completed_point_as_affine_edwards(result).1 = (y²+x²)/(1-t) = edwards_add(x,y,x,y).1

    // On-curve from axiom_edwards_add_complete
    assert(math_on_edwards_curve(
        field_mul(fe51_as_canonical_nat(&result.X), field_inv(fe51_as_canonical_nat(&result.Z))),
        field_mul(fe51_as_canonical_nat(&result.Y), field_inv(fe51_as_canonical_nat(&result.T))),
    )) by {
        axiom_edwards_add_complete(x, y, x, y);
    };

    // -----------------------------------------------------------------------
    // CONCLUSION: is_valid_completed_point and affine projection matches
    // -----------------------------------------------------------------------
    assert(is_valid_completed_point(result));
    assert(completed_point_as_affine_edwards(result) == edwards_double(
        projective_point_as_affine_edwards(self_point).0,
        projective_point_as_affine_edwards(self_point).1,
    ));
}

} // verus!
