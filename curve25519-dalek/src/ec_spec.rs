use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {
// ===== Elliptic Curve Point Specifications =====
// https://en.wikipedia.org/wiki/Curve25519 gives the curve in Montgomery form
// Hence use formulas from https://en.wikipedia.org/wiki/Montgomery_curve#Addition
// and https://en.wikipedia.org/wiki/Montgomery_curve#Doubling
// Might be better to use https://eprint.iacr.org/2017/212.pdf as a reference

// Field prime for curve25519: p = 2^255 - 19
pub open spec fn field_prime() -> nat {
    (pow2(255) - 19) as nat
}

// Montgomery curve coefficient A = 486662 for curve25519
pub open spec fn curve_a() -> nat {
    486662
}

// Montgomery curve coefficient B = 1 for curve25519
pub open spec fn curve_b() -> nat {
    1
}

// Point representation on the elliptic curve
pub enum PointSpec {
    Zero,  // Point at infinity / identity element
    Affine(nat, nat),  // (x, y) coordinates as naturals
}

// Field operations modulo p
pub open spec fn field_add(a: nat, b: nat) -> nat {
    (a + b) % field_prime()
}

pub open spec fn field_sub(a: nat, b: nat) -> nat {
    if a >= b {
        ((a - b) % field_prime() as int) as nat
    } else {
        (((field_prime() - b) + a) % field_prime() as int) as nat
    }
}

pub open spec fn field_mul(a: nat, b: nat) -> nat {
    (a * b) % field_prime()
}

// Extended GCD for computing modular inverse
// TODO This looks plausible but could be wrong.
// Add a lemma proving that it finds the gcd
// and that it finds the correct coefficients for
// g = ax+by, i.e. https://en.wikipedia.org/wiki/B%C3%A9zout%27s_identity
pub open spec fn extended_gcd(a: int, b: int) -> (int, int, int)
    decreases if b >= 0 { b } else { -b }
{
    if b == 0 {
        (a, 1, 0)
    } else {
        let (g, x1, y1) = extended_gcd(b, a % b);
        (g, y1, x1 - (a / b) * y1)
    }
}

// Modular inverse using extended GCD
// TODO Add a lemma proving that a * a^-1 = 1
pub open spec fn field_inv(a: nat) -> nat
    recommends a % field_prime() != 0
{
    let (g, x, y) = extended_gcd(a as int, field_prime() as int);
    if x >= 0 {
        x as nat % field_prime()
    } else {
        ((x + field_prime() as int) as nat) % field_prime()
    }
}

pub open spec fn field_div(a: nat, b: nat) -> nat
    recommends b % field_prime() != 0
{
    field_mul(a, field_inv(b))
}

// Check if a point is on the Montgomery curve: B*y^2 = x^3 + A*x^2 + x
pub open spec fn is_on_curve(p: PointSpec) -> bool {
    match p {
        PointSpec::Zero => true,
        PointSpec::Affine(x, y) => {
            let x_mod = x % field_prime();
            let y_mod = y % field_prime();
            let lhs = field_mul(curve_b(), field_mul(y_mod, y_mod));
            let x_squared = field_mul(x_mod, x_mod);
            let x_cubed = field_mul(x_squared, x_mod);
            let ax_squared = field_mul(curve_a(), x_squared);
            let rhs = field_add(field_add(x_cubed, ax_squared), x_mod);
            lhs == rhs
        }
    }
}

// TODO We could prove a lemma saying that p+q also lies on the curve,
// and that p+q is on the same line as p and q (up to negation, which
// maybe Montgomery form doesn't care about?)

// Elliptic curve point addition for Montgomery curves
// For curve By² = x³ + Ax² + x
// Addition formula: x₃ = B(y₂-y₁)²/(x₂-x₁)² - A - x₁ - x₂
//                   y₃ = (2x₁+x₂+A)(y₂-y₁)/(x₂-x₁) - B(y₂-y₁)³/(x₂-x₁)³ - y₁
// Doubling formula: slope l = (3x₁²+2Ax₁+1)/(2By₁)
//                   x₃ = Bl² - A - 2x₁
//                   y₃ = (3x₁+A)l - Bl³ - y₁
pub open spec fn ec_add(p: PointSpec, q: PointSpec) -> PointSpec
    recommends is_on_curve(p) && is_on_curve(q)
{
    match (p, q) {
        (PointSpec::Zero, _) => q,
        (_, PointSpec::Zero) => p,
        (PointSpec::Affine(x_p, y_p), PointSpec::Affine(x_q, y_q)) => {
            let x_p_mod = x_p % field_prime();
            let y_p_mod = y_p % field_prime();
            let x_q_mod = x_q % field_prime();
            let y_q_mod = y_q % field_prime();

            if x_p_mod == x_q_mod {
                if y_p_mod == y_q_mod {
                    // Point doubling case (P = Q)
                    if y_p_mod == 0 {
                        PointSpec::Zero
                    } else {
                        // Slope: l = (3x₁² + 2Ax₁ + 1) / (2By₁)
                        let x_p_squared = field_mul(x_p_mod, x_p_mod);
                        let three_x_p_squared = field_mul(3, x_p_squared);
                        let two_a_x_p = field_mul(field_mul(2, curve_a()), x_p_mod);
                        let numerator = field_add(field_add(three_x_p_squared, two_a_x_p), 1);
                        let two_b_y_p = field_mul(field_mul(2, curve_b()), y_p_mod);
                        let l = field_div(numerator, two_b_y_p);

                        // x₃ = Bl² - A - 2x₁
                        let l_squared = field_mul(l, l);
                        let b_l_squared = field_mul(curve_b(), l_squared);
                        let two_x_p = field_mul(2, x_p_mod);
                        let x_r = field_sub(field_sub(b_l_squared, curve_a()), two_x_p);

                        // y₃ = (3x₁ + A)l - Bl³ - y₁
                        let three_x_p = field_mul(3, x_p_mod);
                        let three_x_p_plus_a = field_add(three_x_p, curve_a());
                        let term1 = field_mul(three_x_p_plus_a, l);
                        let l_cubed = field_mul(l_squared, l);
                        let b_l_cubed = field_mul(curve_b(), l_cubed);
                        let y_r = field_sub(field_sub(term1, b_l_cubed), y_p_mod);

                        PointSpec::Affine(x_r, y_r)
                    }
                } else {
                    // y_p = -y_q (mod p), so P + Q = O
                    PointSpec::Zero
                }
            } else {
                // General case: P != Q
                // x₃ = B(y₂-y₁)²/(x₂-x₁)² - A - x₁ - x₂
                let y_diff = field_sub(y_q_mod, y_p_mod);
                let x_diff = field_sub(x_q_mod, x_p_mod);
                let y_diff_squared = field_mul(y_diff, y_diff);
                let x_diff_squared = field_mul(x_diff, x_diff);
                let fraction = field_div(y_diff_squared, x_diff_squared);
                let b_fraction = field_mul(curve_b(), fraction);
                let x_sum = field_add(x_p_mod, x_q_mod);
                let x_r = field_sub(field_sub(b_fraction, curve_a()), x_sum);

                // y₃ = (2x₁+x₂+A)(y₂-y₁)/(x₂-x₁) - B(y₂-y₁)³/(x₂-x₁)³ - y₁
                let two_x_p = field_mul(2, x_p_mod);
                let sum_term = field_add(field_add(two_x_p, x_q_mod), curve_a());
                let slope_term = field_div(y_diff, x_diff);
                let term1 = field_mul(sum_term, slope_term);

                let y_diff_cubed = field_mul(y_diff_squared, y_diff);
                let x_diff_cubed = field_mul(x_diff_squared, x_diff);
                let fraction2 = field_div(y_diff_cubed, x_diff_cubed);
                let b_fraction2 = field_mul(curve_b(), fraction2);

                let y_r = field_sub(field_sub(term1, b_fraction2), y_p_mod);

                PointSpec::Affine(x_r, y_r)
            }
        }
    }
}

// Scalar multiplication (repeated addition)
// The inefficient but easy-to-read way
pub open spec fn ec_scalar_mul(k: nat, p: PointSpec) -> PointSpec
    recommends is_on_curve(p)
    decreases k
{
    if k == 0 {
        PointSpec::Zero
    } else if k == 1 {
        p
    } else {
        ec_add(p, ec_scalar_mul((k - 1) as nat, p))
    }
}

// TODO Add conversion functions from_montgomery_point,
// from_edwards_point, and from any other representation used by curve-dalek

} // verus!

fn main() {}
