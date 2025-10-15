#!/usr/bin/env python3
"""Test script for comment_out_functions.py"""

import sys
import tempfile
from pathlib import Path

# Import the functions we want to test
sys.path.insert(0, str(Path(__file__).parent))
from comment_out_functions import find_functions_and_impls, comment_out_lines

TEST_CODE = """impl EdwardsPoint {
    #[cfg(feature = "digest")]
    /// Maps the digest of the input bytes to the curve. This is NOT a hash-to-curve function, as
    /// it produces points with a non-uniform distribution. Rather, it performs something that
    /// resembles (but is not) half of the
    /// [`hash_to_curve`](https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-16.html#section-3-4.2.1)
    /// function from the Elligator2 spec.
    #[deprecated(
        since = "4.0.0",
        note = "previously named `hash_from_bytes`, this is not a secure hash function"
    )]
    pub fn nonspec_map_to_curve<D>(bytes: &[u8]) -> EdwardsPoint
    where
        D: Digest<OutputSize = U64> + Default,
    {
        let mut hash = D::new();
        hash.update(bytes);
        let h = hash.finalize();
        let mut res = [0u8; 32];
        res.copy_from_slice(&h[..32]);

        let sign_bit = (res[31] & 0x80) >> 7;

        let fe = FieldElement::from_bytes(&res);

        let M1 = crate::montgomery::elligator_encode(&fe);
        let E1_opt = M1.to_edwards(sign_bit);

        E1_opt
            .expect("Montgomery conversion to Edwards point in Elligator failed")
            .mul_by_cofactor()
    }
}
"""

EXPECTED_COMMENTED = """impl EdwardsPoint {
//     #[cfg(feature = "digest")]
//     /// Maps the digest of the input bytes to the curve. This is NOT a hash-to-curve function, as
//     /// it produces points with a non-uniform distribution. Rather, it performs something that
//     /// resembles (but is not) half of the
//     /// [`hash_to_curve`](https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-16.html#section-3-4.2.1)
//     /// function from the Elligator2 spec.
//     #[deprecated(
//         since = "4.0.0",
//         note = "previously named `hash_from_bytes`, this is not a secure hash function"
//     )]
//     pub fn nonspec_map_to_curve<D>(bytes: &[u8]) -> EdwardsPoint
//     where
//         D: Digest<OutputSize = U64> + Default,
//     {
//         let mut hash = D::new();
//         hash.update(bytes);
//         let h = hash.finalize();
//         let mut res = [0u8; 32];
//         res.copy_from_slice(&h[..32]);
//
//         let sign_bit = (res[31] & 0x80) >> 7;
//
//         let fe = FieldElement::from_bytes(&res);
//
//         let M1 = crate::montgomery::elligator_encode(&fe);
//         let E1_opt = M1.to_edwards(sign_bit);
//
//         E1_opt
//             .expect("Montgomery conversion to Edwards point in Elligator failed")
//             .mul_by_cofactor()
//     }
}
"""

def test_find_and_comment():
    # Create a temporary file with the test code
    with tempfile.NamedTemporaryFile(mode='w', suffix='.rs', delete=False) as f:
        f.write(TEST_CODE)
        temp_path = f.name

    try:
        # Find functions and impls
        items = find_functions_and_impls(temp_path)
        functions = [(s, e, n, t) for s, e, n, t in items if t == "fn"]

        print(f"Found {len(functions)} function(s)")

        if not functions:
            print("❌ FAILED: No functions found")
            return False

        # Should find exactly one function
        if len(functions) != 1:
            print(f"❌ FAILED: Expected 1 function, found {len(functions)}")
            return False

        start_line, end_line, name, _ = functions[0]
        print(f"Function: {name}")
        print(f"Lines: {start_line+1} to {end_line+1}")

        # Expected to start at line 1 (the #[cfg] attribute, 0-indexed)
        if start_line != 1:
            print(f"❌ FAILED: Expected function to start at line 2 (index 1), but got line {start_line+1} (index {start_line})")
            print("This means the attributes/doc comments are not being included properly")
            return False

        # Comment out the function
        comment_out_lines(temp_path, start_line, end_line)

        # Read the result
        with open(temp_path, 'r') as f:
            result = f.read()

        print("\n=== Result ===")
        print(result)
        print("\n=== Expected ===")
        print(EXPECTED_COMMENTED)

        # Compare
        if result == EXPECTED_COMMENTED:
            print("\n✅ PASSED: Function and all attributes/doc comments correctly commented out")
            return True
        else:
            print("\n❌ FAILED: Output doesn't match expected")
            print("\n=== Differences ===")
            result_lines = result.split('\n')
            expected_lines = EXPECTED_COMMENTED.split('\n')
            for i, (r, e) in enumerate(zip(result_lines, expected_lines)):
                if r != e:
                    print(f"Line {i+1}:")
                    print(f"  Got:      {repr(r)}")
                    print(f"  Expected: {repr(e)}")
            return False

    finally:
        # Clean up
        Path(temp_path).unlink()

if __name__ == '__main__':
    success = test_find_and_comment()
    sys.exit(0 if success else 1)
