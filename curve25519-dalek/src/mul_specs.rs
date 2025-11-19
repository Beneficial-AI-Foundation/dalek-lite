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
// Specifications only - reference implementations (&Scalar * &EdwardsPoint) are in edwards.rs
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

impl<'b> Mul<&'b EdwardsPoint> for Scalar {
    type Output = EdwardsPoint;

    fn mul(self, rhs: &'b EdwardsPoint) -> EdwardsPoint {
        &self * rhs
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

impl<'a> Mul<EdwardsPoint> for &'a Scalar {
    type Output = EdwardsPoint;

    fn mul(self, rhs: EdwardsPoint) -> EdwardsPoint {
        self * &rhs
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

impl Mul<EdwardsPoint> for Scalar {
    type Output = EdwardsPoint;

    fn mul(self, rhs: EdwardsPoint) -> EdwardsPoint {
        &self * &rhs
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

// Owned-type implementations: delegate to &Scalar * &MontgomeryPoint
// (Reference implementation is in montgomery.rs with detailed ensures clauses)
impl<'b> Mul<&'b MontgomeryPoint> for Scalar {
    type Output = MontgomeryPoint;

    fn mul(self, rhs: &'b MontgomeryPoint) -> MontgomeryPoint {
        &self * rhs
    }
}

impl<'a> Mul<MontgomeryPoint> for &'a Scalar {
    type Output = MontgomeryPoint;

    fn mul(self, rhs: MontgomeryPoint) -> MontgomeryPoint {
        self * &rhs
    }
}

impl Mul<MontgomeryPoint> for Scalar {
    type Output = MontgomeryPoint;

    fn mul(self, rhs: MontgomeryPoint) -> MontgomeryPoint {
        &self * &rhs
    }
}

} // verus!
