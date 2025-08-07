#![allow(non_snake_case)]

use crate::backend::serial::curve_models::ProjectiveNielsPoint;
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::Identity;
use crate::window::LookupTable;

#[cfg(feature = "verus")]
use vstd::prelude::*;

#[cfg(feature = "verus")]
verus! {
    /// NAF property specifications for radix-16 representation
    /// Used in variable-base scalar multiplication with fixed window size 4
    
    spec fn radix16_digit_valid(digit: i8) -> bool {
        // Radix-16 digits are in range [-8, 8] as per scalar decomposition
        -8 <= digit && digit <= 8
    }
    
    spec fn radix16_properties(radix16_digits: &[i8]) -> bool {
        // Radix-16 representation has exactly 64 coefficients for 256-bit scalars
        radix16_digits.len() == 64 &&
        // Each digit must be in valid range for lookup table operations
        forall|i: int| 0 <= i < 64 ==> radix16_digit_valid(radix16_digits[i])
    }
    
    spec fn lookup_table_compatibility(digit: i8) -> bool {
        // Lookup table select() requires digits in [-8, 8] for safe table access
        // Covers both positive and negative multiples: -8P, -7P, ..., 7P, 8P
        radix16_digit_valid(digit) &&
        // Additional safety for table indexing (x as usize conversions)
        (digit >= 0 ==> digit as usize <= 8) &&
        (digit < 0 ==> (-digit) as usize <= 8)
    }
}

/// Perform constant-time, variable-base scalar multiplication.
/// 
/// # Preconditions (for verification)
/// - scalar.as_radix_16() returns exactly 64 i8 values
/// - Each digit in scalar.as_radix_16() is in range [-8, 8] 
/// - Array accesses at indices [0..63] and [63] are safe
#[rustfmt::skip] // keep alignment of explanatory comments
pub(crate) fn mul(point: &EdwardsPoint, scalar: &Scalar) -> EdwardsPoint {
    // Construct a lookup table of [P,2P,3P,4P,5P,6P,7P,8P]
    let lookup_table = LookupTable::<ProjectiveNielsPoint>::from(point);
    // Setting s = scalar, compute
    //
    //    s = s_0 + s_1*16^1 + ... + s_63*16^63,
    //
    // with `-8 ≤ s_i < 8` for `0 ≤ i < 63` and `-8 ≤ s_63 ≤ 8`.
    // This decomposition requires s < 2^255, which is guaranteed by Scalar invariant #1.
    let scalar_digits = scalar.as_radix_16();
    
    #[cfg(feature = "verus")]
    assume(
        // NAF property verification: radix-16 digit properties
        radix16_properties(&scalar_digits)
    );
    
    // Compute s*P as
    //
    //    s*P = P*(s_0 +   s_1*16^1 +   s_2*16^2 + ... +   s_63*16^63)
    //    s*P =  P*s_0 + P*s_1*16^1 + P*s_2*16^2 + ... + P*s_63*16^63
    //    s*P = P*s_0 + 16*(P*s_1 + 16*(P*s_2 + 16*( ... + P*s_63)...))
    //
    // We sum right-to-left.

    // Unwrap first loop iteration to save computing 16*identity
    let mut tmp2;
    let mut tmp3 = EdwardsPoint::identity();
    let mut tmp1 = &tmp3 + &lookup_table.select(scalar_digits[63]);
    // Now tmp1 = s_63*P in P1xP1 coords
    for i in (0..63).rev() {
        #[cfg(feature = "verus")]
        assert([
            i < scalar_digits.len(),  // Verify safe scalar_digits[i] access
            scalar_digits.len() == 64,  // Array size consistency for [0..63] access
            // NAF property verification for current digit
            radix16_digit_valid(scalar_digits[i]),
            lookup_table_compatibility(scalar_digits[i]),
        ]);
        
        tmp2 = tmp1.as_projective(); // tmp2 =    (prev) in P2 coords
        tmp1 = tmp2.double();        // tmp1 =  2*(prev) in P1xP1 coords
        tmp2 = tmp1.as_projective(); // tmp2 =  2*(prev) in P2 coords
        tmp1 = tmp2.double();        // tmp1 =  4*(prev) in P1xP1 coords
        tmp2 = tmp1.as_projective(); // tmp2 =  4*(prev) in P2 coords
        tmp1 = tmp2.double();        // tmp1 =  8*(prev) in P1xP1 coords
        tmp2 = tmp1.as_projective(); // tmp2 =  8*(prev) in P2 coords
        tmp1 = tmp2.double();        // tmp1 = 16*(prev) in P1xP1 coords
        tmp3 = tmp1.as_extended();   // tmp3 = 16*(prev) in P3 coords
        tmp1 = &tmp3 + &lookup_table.select(scalar_digits[i]);
        // Now tmp1 = s_i*P + 16*(prev) in P1xP1 coords
    }
    tmp1.as_extended()
}
