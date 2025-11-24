use crate::edwards::EdwardsBasepointTable;
use crate::specs::montgomery_specs::*;
use crate::{EdwardsPoint, MontgomeryPoint, Scalar};
use core::ops::Mul;
use vstd::prelude::*;

/* VERIFICATION NOTE: this file contains
- inlined macro definitions for multiplicaitons between Scalar, EdwardsPoint, and MontgomeryPoint.
- their specifications as trait implementations MulSpecImpl.
*/
verus! {

// =============================================================================
// SECTION 1: EdwardsPoint * Scalar
// =============================================================================
// Specifications only - reference implementations (&EdwardsPoint * &Scalar) are in edwards.rs
/// Spec for &EdwardsPoint * &Scalar (reference implementation)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for &EdwardsPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &Scalar) -> bool {
        true
    }

    open spec fn mul_spec(self, rhs: &Scalar) -> EdwardsPoint {
        arbitrary()
    }
}

/// Spec for &EdwardsPoint * Scalar (owned scalar)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<Scalar> for &EdwardsPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: Scalar) -> bool {
        true
    }

    open spec fn mul_spec(self, rhs: Scalar) -> EdwardsPoint {
        arbitrary()
    }
}

/// Spec for EdwardsPoint * &Scalar (owned point)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for EdwardsPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &Scalar) -> bool {
        true
    }

    open spec fn mul_spec(self, rhs: &Scalar) -> EdwardsPoint {
        arbitrary()
    }
}

/// Spec for EdwardsPoint * Scalar (both owned)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<Scalar> for EdwardsPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: Scalar) -> bool {
        true
    }

    open spec fn mul_spec(self, rhs: Scalar) -> EdwardsPoint {
        arbitrary()
    }
}

// =============================================================================
// SECTION 2: Scalar * EdwardsPoint
// =============================================================================
// NOTE: Manual implementations needed because macro-generated code is outside verus! blocks
// and cannot be used from inside verus! blocks (e.g., EdwardsPoint::mul_clamped).
/// Spec for &Scalar * &EdwardsPoint
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&EdwardsPoint> for &Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &EdwardsPoint) -> bool {
        true
    }

    open spec fn mul_spec(self, rhs: &EdwardsPoint) -> EdwardsPoint {
        arbitrary()
    }
}

/// Spec for Scalar * &EdwardsPoint (owned scalar)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&EdwardsPoint> for Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &EdwardsPoint) -> bool {
        true
    }

    open spec fn mul_spec(self, rhs: &EdwardsPoint) -> EdwardsPoint {
        arbitrary()
    }
}

/// Spec for &Scalar * EdwardsPoint (owned point)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<EdwardsPoint> for &Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: EdwardsPoint) -> bool {
        true
    }

    open spec fn mul_spec(self, rhs: EdwardsPoint) -> EdwardsPoint {
        arbitrary()
    }
}

/// Spec for Scalar * EdwardsPoint (both owned)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<EdwardsPoint> for Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: EdwardsPoint) -> bool {
        true
    }

    open spec fn mul_spec(self, rhs: EdwardsPoint) -> EdwardsPoint {
        arbitrary()
    }
}

// =============================================================================
// SECTION 3: Scalar * EdwardsBasepointTable
// =============================================================================
/// External type specification for EdwardsBasepointTable
#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExEdwardsBasepointTable(EdwardsBasepointTable);

/// External type specification for EdwardsBasepointTableRadix32
#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExEdwardsBasepointTableRadix32(crate::edwards::EdwardsBasepointTableRadix32);

/// External type specification for EdwardsBasepointTableRadix64
#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExEdwardsBasepointTableRadix64(crate::edwards::EdwardsBasepointTableRadix64);

/// External type specification for EdwardsBasepointTableRadix128
#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExEdwardsBasepointTableRadix128(crate::edwards::EdwardsBasepointTableRadix128);

/// External type specification for EdwardsBasepointTableRadix256
#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExEdwardsBasepointTableRadix256(crate::edwards::EdwardsBasepointTableRadix256);

impl<'a> Mul<&'a EdwardsBasepointTable> for Scalar {
    type Output = EdwardsPoint;

    #[verifier::external_body]
    fn mul(self, basepoint_table: &'a EdwardsBasepointTable) -> EdwardsPoint {
        &self * basepoint_table
    }
}

impl<'a> Mul<EdwardsBasepointTable> for &'a Scalar {
    type Output = EdwardsPoint;

    #[verifier::external_body]  // Delegates to &Scalar * &EdwardsBasepointTable which is external
    fn mul(self, basepoint_table: EdwardsBasepointTable) -> EdwardsPoint {
        self * &basepoint_table
    }
}

impl Mul<EdwardsBasepointTable> for Scalar {
    type Output = EdwardsPoint;

    #[verifier::external_body]  // Delegates to &Scalar * &EdwardsBasepointTable which is external
    fn mul(self, basepoint_table: EdwardsBasepointTable) -> EdwardsPoint {
        &self * &basepoint_table
    }
}

// =============================================================================
// SECTION 4: MontgomeryPoint * Scalar
// =============================================================================
// Specifications only - implementations are in montgomery.rs
// Requires: MontgomeryPoint must be valid
/// Spec for &MontgomeryPoint * &Scalar (reference implementation)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for &MontgomeryPoint {
    open spec fn obeys_mul_spec() -> bool {
        false  // Set to false since we use ensures clause instead of concrete spec

    }

    open spec fn mul_req(self, rhs: &Scalar) -> bool {
        is_valid_montgomery_point(*self)
    }

    open spec fn mul_spec(self, rhs: &Scalar) -> MontgomeryPoint {
        arbitrary()  // Placeholder - actual spec is in ensures clause

    }
}

// =============================================================================
// SECTION 5: Scalar * MontgomeryPoint
// =============================================================================
// Specifications only - implementations are in montgomery.rs
// Requires: MontgomeryPoint must be valid
/// Spec for &Scalar * &MontgomeryPoint (reference implementation)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&MontgomeryPoint> for &Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false  // Set to false since we use ensures clause instead of concrete spec

    }

    open spec fn mul_req(self, rhs: &MontgomeryPoint) -> bool {
        is_valid_montgomery_point(*rhs)
    }

    open spec fn mul_spec(self, rhs: &MontgomeryPoint) -> MontgomeryPoint {
        arbitrary()  // Placeholder - actual spec is in ensures clause

    }
}

/// Spec for Scalar * &MontgomeryPoint (owned scalar)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&MontgomeryPoint> for Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &MontgomeryPoint) -> bool {
        is_valid_montgomery_point(*rhs)
    }

    open spec fn mul_spec(self, rhs: &MontgomeryPoint) -> MontgomeryPoint {
        arbitrary()
    }
}

/// Spec for &Scalar * MontgomeryPoint (owned point)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<MontgomeryPoint> for &Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: MontgomeryPoint) -> bool {
        is_valid_montgomery_point(rhs)
    }

    open spec fn mul_spec(self, rhs: MontgomeryPoint) -> MontgomeryPoint {
        arbitrary()
    }
}

/// Spec for Scalar * MontgomeryPoint (both owned)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<MontgomeryPoint> for Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: MontgomeryPoint) -> bool {
        is_valid_montgomery_point(rhs)
    }

    open spec fn mul_spec(self, rhs: MontgomeryPoint) -> MontgomeryPoint {
        arbitrary()
    }
}

} // verus!
