#[allow(unused_imports)]
use crate::specs::primality_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs_u64::p;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power::*;

use vstd::prelude::*;

verus! {

// =============================================================================
// GCD Definition and Basic Properties
// =============================================================================

/// Specification: Greatest Common Divisor using Euclidean algorithm
/// gcd(a, 0) = a
/// gcd(a, b) = gcd(b, a % b) for b > 0
pub open spec fn gcd(a: nat, b: nat) -> nat
    decreases b,
{
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

/// GCD is positive when at least one input is positive
pub proof fn lemma_gcd_positive(a: nat, b: nat)
    requires
        a > 0 || b > 0,
    ensures
        gcd(a, b) > 0,
    decreases b,
{
    if b == 0 {
        // gcd(a, 0) = a > 0
    } else {
        // gcd(a, b) = gcd(b, a % b)
        // b > 0, so at least one input to recursive call is positive
        lemma_gcd_positive(b, a % b);
    }
}

/// g divides a means a % g == 0 (for g > 0)
pub open spec fn divides(g: nat, a: nat) -> bool {
    g > 0 && a % g == 0
}

/// GCD divides both arguments (when gcd > 0)
pub proof fn lemma_gcd_divides_both(a: nat, b: nat)
    requires
        a > 0 || b > 0,
    ensures
        divides(gcd(a, b), a),
        divides(gcd(a, b), b),
    decreases b,
{
    lemma_gcd_positive(a, b);
    let g = gcd(a, b);

    if b == 0 {
        // gcd(a, 0) = a, need to show a % a == 0 and 0 % a == 0
        assert(g == a);
        lemma_mod_self_0(a as int);  // a % a == 0
        lemma_small_mod(0nat, a);  // 0 % a == 0
    } else {
        // Recursive case: gcd(a, b) = gcd(b, a % b)
        // By induction, g divides b and g divides (a % b)
        lemma_gcd_divides_both(b, a % b);

        // g divides b: directly from induction
        // g divides (a % b): directly from induction
        // Need to show g divides a

        // Use: a = (a / b) * b + (a % b)
        // If g | b and g | (a % b), then g | a
        let q = a / b;
        let r = a % b;

        assert(a == q * b + r) by {
            lemma_fundamental_div_mod(a as int, b as int);
        };

        // g | b means b = k * g for some k, i.e., b % g == 0
        // g | r means r = m * g for some m, i.e., r % g == 0
        // a = q * b + r = q * k * g + m * g = (q*k + m) * g
        // So a % g == 0

        // First show (q * b) % g == 0 from b % g == 0
        lemma_divisibility_of_multiple(q, b, g);
        lemma_divisibility_of_sum(q * b, r, g);
    }
}

/// If g divides x and g divides y, then g divides (x + y)
proof fn lemma_divisibility_of_sum(x: nat, y: nat, g: nat)
    requires
        g > 0,
        x % g == 0,
        y % g == 0,
    ensures
        (x + y) % g == 0,
{
    lemma_mod_adds(x as int, y as int, g as int);
    assert((x % g + y % g) % g == (x + y) % g);
    lemma_small_mod(0nat, g);
}

/// If g divides b, then g divides (q * b)
proof fn lemma_divisibility_of_multiple(q: nat, b: nat, g: nat)
    requires
        g > 0,
        b % g == 0,
    ensures
        (q * b) % g == 0,
{
    lemma_mul_mod_noop_right(q as int, b as int, g as int);
    assert((q * (b % g)) % g == (q * b) % g);
    assert((q * 0) % g == 0) by {
        lemma_mul_basics(q as int);
        lemma_small_mod(0nat, g);
    };
}

// =============================================================================
// Bézout's Identity
// =============================================================================

/// Bézout coefficients: there exist integers x, y such that a*x + b*y = gcd(a, b)
/// We prove existence by construction using Extended Euclidean Algorithm
pub open spec fn bezout_coeffs_exist(a: nat, b: nat) -> bool {
    exists|x: int, y: int| #[trigger] (a as int * x + b as int * y) == gcd(a, b) as int
}

/// Extended GCD: returns (g, x, y) such that a*x + b*y = g = gcd(a, b)
/// This is a spec function that computes the Bézout coefficients
pub open spec fn extended_gcd(a: nat, b: nat) -> (nat, int, int)
    decreases b,
{
    if b == 0 {
        (a, 1, 0)  // a * 1 + 0 * 0 = a = gcd(a, 0)
    } else {
        let (g, x1, y1) = extended_gcd(b, a % b);
        // b * x1 + (a % b) * y1 = g
        // a % b = a - (a / b) * b
        // b * x1 + (a - (a/b)*b) * y1 = g
        // b * x1 + a * y1 - (a/b) * b * y1 = g
        // a * y1 + b * (x1 - (a/b) * y1) = g
        let q = (a / b) as int;
        (g, y1, x1 - q * y1)
    }
}

/// The first component of extended_gcd is gcd
pub proof fn lemma_extended_gcd_is_gcd(a: nat, b: nat)
    ensures
        extended_gcd(a, b).0 == gcd(a, b),
    decreases b,
{
    if b == 0 {
        // extended_gcd(a, 0) = (a, 1, 0), gcd(a, 0) = a
    } else {
        lemma_extended_gcd_is_gcd(b, a % b);
    }
}

/// Extended GCD satisfies Bézout's identity
pub proof fn lemma_extended_gcd_bezout(a: nat, b: nat)
    ensures
        ({
            let (g, x, y) = extended_gcd(a, b);
            a as int * x + b as int * y == g as int
        }),
    decreases b,
{
    if b == 0 {
        // extended_gcd(a, 0) = (a, 1, 0)
        // a * 1 + 0 * 0 = a ✓
        assert(a as int * 1 + 0int * 0 == a as int) by {
            lemma_mul_basics(a as int);
        };
    } else {
        // Induction hypothesis
        lemma_extended_gcd_bezout(b, a % b);
        let (g, x1, y1) = extended_gcd(b, a % b);
        // IH: b * x1 + (a % b) * y1 = g

        let q = (a / b) as int;
        let r = (a % b) as int;

        // We need to show: a * y1 + b * (x1 - q * y1) = g
        // Expand: a * y1 + b * x1 - b * q * y1
        //       = a * y1 + b * x1 - (a - r) * y1    [since a = b*q + r]
        //       = a * y1 + b * x1 - a * y1 + r * y1
        //       = b * x1 + r * y1
        //       = g  [by IH]

        // First establish a = b * q + r
        assert(a as int == b as int * q + r) by {
            lemma_fundamental_div_mod(a as int, b as int);
        };

        // Now the algebra
        let new_x = y1;
        let new_y = x1 - q * y1;

        // We want to show: a * y1 + b * (x1 - q * y1) == g
        // By IH: b * x1 + r * y1 == g
        // So we need: a * y1 + b * (x1 - q * y1) == b * x1 + r * y1

        // Step 1: Expand b * (x1 - q * y1) = b * x1 - b * (q * y1)
        assert(b as int * new_y == b as int * x1 - b as int * (q * y1)) by {
            lemma_mul_is_distributive_sub(b as int, x1, q * y1);
        };

        // Step 2: b * (q * y1) = (b * q) * y1
        assert(b as int * (q * y1) == (b as int * q) * y1) by {
            lemma_mul_is_associative(b as int, q, y1);
        };

        // Step 3: b * q = a - r (from a = b * q + r)
        assert(b as int * q == a as int - r);

        // Step 4: (b * q) * y1 = (a - r) * y1
        assert((b as int * q) * y1 == (a as int - r) * y1);

        // Step 5: (a - r) * y1 = a * y1 - r * y1
        assert((a as int - r) * y1 == a as int * y1 - r * y1) by {
            lemma_mul_is_distributive_sub_other_way(y1, a as int, r);
        };

        // Now chain: b * (x1 - q * y1) = b * x1 - b * (q * y1)
        //                              = b * x1 - (b * q) * y1
        //                              = b * x1 - (a - r) * y1
        //                              = b * x1 - (a * y1 - r * y1)
        //                              = b * x1 - a * y1 + r * y1

        // So: a * y1 + b * (x1 - q * y1) = a * y1 + b * x1 - a * y1 + r * y1
        //                                = b * x1 + r * y1 = g

        assert(a as int * new_x + b as int * new_y == g as int);
    }
}

/// Bézout's identity: for any a, b, there exist x, y such that a*x + b*y = gcd(a, b)
pub proof fn lemma_bezout(a: nat, b: nat)
    ensures
        bezout_coeffs_exist(a, b),
{
    lemma_extended_gcd_bezout(a, b);
    lemma_extended_gcd_is_gcd(a, b);
    let (g, x, y) = extended_gcd(a, b);
    assert(a as int * x + b as int * y == gcd(a, b) as int);
}

// =============================================================================
// Prime GCD Properties
// =============================================================================

/// If p is prime and a is not divisible by p, then gcd(a, p) = 1
pub proof fn lemma_prime_coprime(a: nat, prime: nat)
    requires
        is_prime(prime),
        a % prime != 0,
    ensures
        gcd(a, prime) == 1,
{
    let g = gcd(a, prime);

    // g divides both a and prime
    lemma_gcd_positive(a, prime);
    lemma_gcd_divides_both(a, prime);

    // Since g divides prime and prime is prime, g is either 1 or prime
    // g divides prime means prime % g == 0

    // prime > 1 (from is_prime)
    // g divides prime, so g <= prime
    // By definition of prime: any d with 1 < d < prime does not divide prime
    // So if g divides prime, either g == 1 or g == prime

    // Case analysis: g can't be prime because g divides a but a % prime != 0
    // If g == prime, then a % g == 0, i.e., a % prime == 0, contradiction

    if g == prime {
        // g divides a means a % g == 0
        // But a % prime != 0, contradiction
        assert(a % g == 0);  // from lemma_gcd_divides_both
        assert(false);
    }

    // So g != prime. Since g divides prime and g > 0, we need g == 1
    // g divides prime means prime % g == 0
    // By definition of prime: forall d. 1 < d < prime ==> prime % d != 0
    // Contrapositive: prime % g == 0 ==> g <= 1 or g >= prime
    // Since g > 0 and g != prime and g divides prime (prime % g == 0),
    // we need g == 1 or g == prime. Since g != prime, g == 1.

    lemma_divisor_of_prime(g, prime);
}

/// If g > 0 divides a prime p, then g == 1 or g == p
proof fn lemma_divisor_of_prime(g: nat, prime: nat)
    requires
        is_prime(prime),
        g > 0,
        prime % g == 0,
    ensures
        g == 1 || g == prime,
{
    // is_prime(prime) means: prime > 1 && forall d. 1 < d < prime ==> prime % d != 0
    // Contrapositive of the forall: prime % g == 0 ==> !(1 < g < prime)
    // i.e., prime % g == 0 ==> g <= 1 || g >= prime

    if g > 1 && g < prime {
        // This contradicts is_prime
        assert(prime % g != 0);  // from is_prime definition
        assert(false);
    }

    // So g <= 1 or g >= prime
    // Since g > 0, g <= 1 means g == 1
    // g >= prime and prime % g == 0 with g, prime > 0:
    //   prime = k * g for some k >= 1
    //   If g > prime, then k * g > prime, contradiction
    //   So g <= prime, combined with g >= prime gives g == prime

    if g > prime {
        // prime % g == 0 means prime = k * g for some k >= 0
        // prime > 0 and g > prime > 0 means k >= 1
        // But k * g >= g > prime, so prime >= k * g > prime, contradiction
        assert(prime < g);
        lemma_mod_of_smaller(prime, g);
        assert(prime % g == prime);  // since prime < g
        // But we assumed prime % g == 0, so prime == 0
        assert(prime == 0);
        assert(false);  // prime > 1 from is_prime
    }
}

/// If a < b, then a % b == a
proof fn lemma_mod_of_smaller(a: nat, b: nat)
    requires
        a < b,
        b > 0,
    ensures
        a % b == a,
{
    lemma_small_mod(a, b);
}

// =============================================================================
// Modular Inverse Existence from Bézout
// =============================================================================

/// If gcd(a, m) = 1, then a has a multiplicative inverse mod m
pub proof fn lemma_coprime_has_inverse(a: nat, m: nat)
    requires
        m > 1,
        gcd(a, m) == 1,
    ensures
        exists|w: nat| w < m && #[trigger] ((a * w) % m) == 1,
{
    // By Bézout: there exist x, y such that a * x + m * y = 1
    lemma_extended_gcd_bezout(a, m);
    lemma_extended_gcd_is_gcd(a, m);
    let (g, x, y) = extended_gcd(a, m);

    assert(g == 1);
    assert(a as int * x + m as int * y == 1);

    // Taking mod m: (a * x) % m = 1
    // a * x ≡ 1 - m * y ≡ 1 (mod m)

    // But x might be negative, so we need w = x % m (as positive)
    let w = mod_positive(x, m as int);

    assert(w < m) by {
        lemma_mod_bound(x, m as int);
    };

    // First prove (a * x) % m == 1
    assert((a as int * x) % m as int == 1) by {
        // Since a * x + m * y = 1, we have a * x = 1 - m * y
        // (a * x) % m = (1 - m * y) % m = (1 + m * (-y)) % m = 1 % m = 1

        lemma_mod_multiples_vanish(-y, 1int, m as int);
        // (1 + m * (-y)) % m = 1 % m
        assert((1int + m as int * (-y)) % m as int == 1int % m as int);

        // Show 1 - m * y == 1 + m * (-y)
        assert(m as int * (-y) == -(m as int * y)) by {
            lemma_mul_unary_negation(m as int, y);
        };
        assert(1int + (-(m as int * y)) == 1int - m as int * y);
        assert(a as int * x == 1int - m as int * y);
        lemma_small_mod(1nat, m);
    };

    // Now show (a * w) % m == 1
    // w = mod_positive(x, m) = ((x % m + m) % m) as nat
    // We need: (a * w) % m == 1

    // Key insight: w % m == x % m (they're congruent)
    // mod_positive ensures w is in [0, m) and w ≡ x (mod m)

    // (a * w) % m = (a * (w % m)) % m = (a * (x % m)) % m = (a * x) % m = 1
    assert((a * w) % m == 1) by {
        // w = ((x % m + m) % m)
        // w % m = ((x % m + m) % m) % m = (x % m + m) % m
        // But also (x % m + m) % m = x % m (since adding m doesn't change mod m)
        lemma_mod_adds(x % m as int, m as int, m as int);
        lemma_mod_self_0(m as int);
        // (x % m + m) % m = (x % m + 0) % m = x % m % m = x % m
        lemma_mod_mod(x, m as int);

        // So w as int % m == x % m
        // Therefore (a * w) % m = (a * (w % m)) % m = (a * (x % m)) % m = (a * x) % m = 1
        lemma_mul_mod_noop_right(a as int, w as int, m as int);
        lemma_mul_mod_noop_right(a as int, x, m as int);
    };
}

/// Helper: (x % m) % m == x % m
proof fn lemma_mod_mod(x: int, m: int)
    requires
        m > 0,
    ensures
        (x % m) % m == x % m,
{
    lemma_mod_bound(x, m);
    lemma_small_mod((x % m) as nat, m as nat);
}

/// Convert an int to its positive representative mod m
pub open spec fn mod_positive(x: int, m: int) -> nat
    recommends
        m > 0,
{
    ((x % m + m) % m) as nat
}

/// mod_positive gives a value in [0, m)
pub proof fn lemma_mod_positive_bound(x: int, m: int)
    requires
        m > 0,
    ensures
        0 <= mod_positive(x, m) < m,
{
    lemma_mod_bound(x % m + m, m);
}

/// mod_positive is congruent to x mod m
pub proof fn lemma_mod_positive_congruent(x: int, m: int)
    requires
        m > 0,
    ensures
        mod_positive(x, m) as int % m == x % m,
{
    // mod_positive(x, m) = (x % m + m) % m
    // Need: ((x % m + m) % m) % m == x % m

    // First: (x % m + m) % m == x % m
    // Because (a + m) % m == a % m when a is in canonical form
    lemma_mod_adds(x % m, m, m);
    // This gives us (x % m + m) % m == (x % m % m + m % m) % m
    lemma_mod_self_0(m);
    assert(m % m == 0);
    lemma_mod_mod(x, m);
    // x % m % m == x % m
    // So (x % m + m) % m == (x % m + 0) % m == x % m % m == x % m

    // Now: mod_positive(x, m) = (x % m + m) % m, which is in [0, m)
    // So mod_positive(x, m) % m == mod_positive(x, m) == (x % m + m) % m == x % m
    let w = mod_positive(x, m);
    lemma_mod_positive_bound(x, m);
    // w < m, so w % m == w
    lemma_small_mod(w, m as nat);
}

/// Lemma: Fermat's Little Theorem
///
/// For any prime p and any integer x not divisible by p,
/// we have x^(p-1) ≡ 1 (mod p).
///
/// This is one of the fundamental theorems in number theory and the basis
/// for many cryptographic constructions, including:
/// - Computing multiplicative inverses: x^(-1) ≡ x^(p-2) (mod p)
/// - Primality testing
/// - Public-key cryptography
///
/// **Proof Status**: Currently admitted. A complete proof would require:
/// 1. Defining the multiplicative group (ℤ/pℤ)*
/// 2. Proving Lagrange's theorem (order of element divides order of group)
/// 3. Showing |（ℤ/pℤ)*| = p - 1 (Euler's totient for primes)
///
/// While provable from the is_prime definition, this would require substantial
/// group theory infrastructure that is currently beyond the scope of this
/// verification effort.
pub proof fn lemma_fermat_little_theorem(x: nat, prime: nat)
    requires
        is_prime(prime),
        x % prime != 0,
    ensures
        (pow(x as int, (prime - 1) as nat) as nat) % prime == 1,
{
    admit();
}

} // verus!
