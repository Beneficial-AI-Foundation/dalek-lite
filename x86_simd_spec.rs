use vstd::prelude::*;
use core::arch::x86_64::{__m128i, _mm_extract_epi32};

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExM128i(__m128i);

// imm8 must be a compile-time constant 0-3
pub assume_specification<const IMM8: i32> [core::arch::x86_64::_mm_extract_epi32::<IMM8>] (a: __m128i) -> (result: i32)
    requires 0 <= IMM8 < 4
    ensures result == extract_i32(a, IMM8 as int)
;

// A spec fn that does the same thing as _mm_extract_epi32
pub uninterp spec fn extract_i32(v: __m128i, i: int) -> i32;

pub assume_specification [core::arch::x86_64::_mm_add_epi32] (a: __m128i, b: __m128i) -> (result: __m128i)
    ensures
        forall|i: int| #![auto] 0 <= i < 4 ==>
            extract_i32(result, i) == extract_i32(a, i).wrapping_add(extract_i32(b, i)),
;

pub fn example_add_vectors(a: __m128i, b: __m128i) -> (result: __m128i)
    ensures
        forall|i: int| #![auto] 0 <= i < 4 ==>
            extract_i32(result, i) == extract_i32(a, i).wrapping_add(extract_i32(b, i)),
{
    core::arch::x86_64::_mm_add_epi32(a, b)
}

pub fn example_get_first_element(v: __m128i) -> (result: i32)
    ensures result == extract_i32(v, 0)
{
    _mm_extract_epi32::<0>(v)
}

} // verus!

fn main() {}
