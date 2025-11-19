// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// See LICENSE for licensing information.
//
// Multiplication specifications for Verus verification
//
// This module contains all the MulSpecImpl trait implementations that define
// preconditions and postconditions for scalar multiplication operations.
use crate::specs::montgomery_specs::*;
use crate::{EdwardsPoint, MontgomeryPoint, Scalar};
use vstd::prelude::*;

verus! {

// =============================================================================
// MontgomeryPoint * Scalar specifications
// =============================================================================
/// Spec for &MontgomeryPoint * &Scalar (reference implementation)
/// Requires: MontgomeryPoint must be valid
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
// Scalar * MontgomeryPoint specifications
// =============================================================================
/// Spec for &Scalar * &MontgomeryPoint (reference implementation)
/// Requires: MontgomeryPoint must be valid
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

/// Spec for Scalar * &MontgomeryPoint
/// Requires: MontgomeryPoint must be valid
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

/// Spec for &Scalar * MontgomeryPoint
/// Requires: MontgomeryPoint must be valid
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

/// Spec for Scalar * MontgomeryPoint
/// Requires: MontgomeryPoint must be valid
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

// =============================================================================
// EdwardsPoint * Scalar specifications
// =============================================================================
/// Spec for &EdwardsPoint * &Scalar
/// No precondition needed
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for &EdwardsPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &Scalar) -> bool {
        true  // No precondition for EdwardsPoint * Scalar

    }

    open spec fn mul_spec(self, rhs: &Scalar) -> EdwardsPoint {
        arbitrary()
    }
}

/// Spec for &EdwardsPoint * Scalar
/// No precondition needed
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

/// Spec for EdwardsPoint * &Scalar
/// No precondition needed
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

/// Spec for EdwardsPoint * Scalar
/// No precondition needed
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
// Scalar * EdwardsPoint specifications
// =============================================================================
/// Spec for Scalar * &EdwardsPoint
/// No precondition needed
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&EdwardsPoint> for Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &EdwardsPoint) -> bool {
        true  // No precondition for EdwardsPoint multiplication

    }

    open spec fn mul_spec(self, rhs: &EdwardsPoint) -> EdwardsPoint {
        arbitrary()
    }
}

/// Spec for &Scalar * EdwardsPoint
/// No precondition needed
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

/// Spec for Scalar * EdwardsPoint
/// No precondition needed
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

} // verus!
