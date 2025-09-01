use vstd::prelude::*;
use core::arch::x86_64::{__m128i, _mm_extract_epi32};

verus! {

// External type specification for __m128i
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExM128i(__m128i);

// Assume specification for _mm_extract_epi32
// Note: imm8 must be a compile-time constant 0-3, returns signed i32
pub assume_specification<const IMM8: i32> [core::arch::x86_64::_mm_extract_epi32::<IMM8>] (a: __m128i) -> (result: i32)
    requires 0 <= IMM8 < 4
    ensures result == extract_i32(a, IMM8 as int)
;

// Helper function to abstractly represent extracting 32-bit signed integers from __m128i
pub uninterp spec fn extract_i32(v: __m128i, i: int) -> i32;

// Assume specification for _mm_add_epi32
// This intrinsic adds corresponding 32-bit integers from two 128-bit vectors
pub assume_specification [core::arch::x86_64::_mm_add_epi32] (a: __m128i, b: __m128i) -> (result: __m128i)
    ensures
        forall|i: int| #![auto] 0 <= i < 4 ==>
            extract_i32(result, i) == extract_i32(a, i).wrapping_add(extract_i32(b, i)),
;

// Example usage with the assumed specifications
pub fn add_vectors(a: __m128i, b: __m128i) -> (result: __m128i)
    ensures
        forall|i: int| #![auto] 0 <= i < 4 ==>
            extract_i32(result, i) == extract_i32(a, i).wrapping_add(extract_i32(b, i)),
{
    core::arch::x86_64::_mm_add_epi32(a, b)
}

// Example function demonstrating extraction of individual elements
pub fn get_first_element(v: __m128i) -> (result: i32)
    ensures result == extract_i32(v, 0)
{
    _mm_extract_epi32::<0>(v)
}

} // verus!

fn main() {
    // Empty main function for compilation
}
