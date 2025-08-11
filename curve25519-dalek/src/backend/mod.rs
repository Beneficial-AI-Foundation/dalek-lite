// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2021 isis lovecruft
// Copyright (c) 2016-2019 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! **INTERNALS:** Pluggable implementations for different architectures.
//!
//! The backend code contains the serial backend.
//!
//! The [`serial`] backend contains 32- and 64-bit implementations of
//! field arithmetic and scalar arithmetic, as well as implementations
//! of point operations using the mixed-model strategy (passing
//! between different curve models depending on the operation).

use crate::EdwardsPoint;
use crate::Scalar;

pub mod serial;


#[derive(Copy, Clone)]
enum BackendKind {
    Serial,
}

#[inline]
fn get_selected_backend() -> BackendKind {
    BackendKind::Serial
}

#[allow(missing_docs)]
#[cfg(feature = "alloc")]
pub fn pippenger_optional_multiscalar_mul<I, J>(scalars: I, points: J) -> Option<EdwardsPoint>
where
    I: IntoIterator,
    I::Item: core::borrow::Borrow<Scalar>,
    J: IntoIterator<Item = Option<EdwardsPoint>>,
{
    use crate::traits::VartimeMultiscalarMul;

    match get_selected_backend() {
        BackendKind::Serial =>
            serial::scalar_mul::pippenger::Pippenger::optional_multiscalar_mul::<I, J>(scalars, points),
    }
}

#[cfg(feature = "alloc")]
pub(crate) enum VartimePrecomputedStraus {
    Scalar(serial::scalar_mul::precomputed_straus::VartimePrecomputedStraus),
}

#[cfg(feature = "alloc")]
impl VartimePrecomputedStraus {
    pub fn new<I>(static_points: I) -> Self
    where
        I: IntoIterator,
        I::Item: core::borrow::Borrow<EdwardsPoint>,
    {
        use crate::traits::VartimePrecomputedMultiscalarMul;

        match get_selected_backend() {
            BackendKind::Serial =>
                VartimePrecomputedStraus::Scalar(serial::scalar_mul::precomputed_straus::VartimePrecomputedStraus::new(static_points))
        }
    }

    /// Return the number of static points in the precomputation.
    pub fn len(&self) -> usize {
        use crate::traits::VartimePrecomputedMultiscalarMul;

        match self {
            VartimePrecomputedStraus::Scalar(inner) => inner.len(),
        }
    }

    /// Determine if the precomputation is empty.
    pub fn is_empty(&self) -> bool {
        use crate::traits::VartimePrecomputedMultiscalarMul;

        match self {
            VartimePrecomputedStraus::Scalar(inner) => inner.is_empty(),
        }
    }

    pub fn optional_mixed_multiscalar_mul<I, J, K>(
        &self,
        static_scalars: I,
        dynamic_scalars: J,
        dynamic_points: K,
    ) -> Option<EdwardsPoint>
    where
        I: IntoIterator,
        I::Item: core::borrow::Borrow<Scalar>,
        J: IntoIterator,
        J::Item: core::borrow::Borrow<Scalar>,
        K: IntoIterator<Item = Option<EdwardsPoint>>,
    {
        use crate::traits::VartimePrecomputedMultiscalarMul;

        match self {
            VartimePrecomputedStraus::Scalar(inner) => inner.optional_mixed_multiscalar_mul(
                static_scalars,
                dynamic_scalars,
                dynamic_points,
            ),
        }
    }
}

#[allow(missing_docs)]
#[cfg(feature = "alloc")]
pub fn straus_multiscalar_mul<I, J>(scalars: I, points: J) -> EdwardsPoint
where
    I: IntoIterator,
    I::Item: core::borrow::Borrow<Scalar>,
    J: IntoIterator,
    J::Item: core::borrow::Borrow<EdwardsPoint>,
{
    use crate::traits::MultiscalarMul;

    match get_selected_backend() {
        BackendKind::Serial => {
            serial::scalar_mul::straus::Straus::multiscalar_mul::<I, J>(scalars, points)
        }
    }
}

#[allow(missing_docs)]
#[cfg(feature = "alloc")]
pub fn straus_optional_multiscalar_mul<I, J>(scalars: I, points: J) -> Option<EdwardsPoint>
where
    I: IntoIterator,
    I::Item: core::borrow::Borrow<Scalar>,
    J: IntoIterator<Item = Option<EdwardsPoint>>,
{
    use crate::traits::VartimeMultiscalarMul;

    match get_selected_backend() {
        BackendKind::Serial => {
            serial::scalar_mul::straus::Straus::optional_multiscalar_mul::<I, J>(scalars, points)
        }
    }
}

/// Perform constant-time, variable-base scalar multiplication.
pub fn variable_base_mul(point: &EdwardsPoint, scalar: &Scalar) -> EdwardsPoint {
    match get_selected_backend() {
        BackendKind::Serial => serial::scalar_mul::variable_base::mul(point, scalar),
    }
}

/// Compute \\(aA + bB\\) in variable time, where \\(B\\) is the Ed25519 basepoint.
#[allow(non_snake_case)]
pub fn vartime_double_base_mul(a: &Scalar, A: &EdwardsPoint, b: &Scalar) -> EdwardsPoint {
    match get_selected_backend() {
        BackendKind::Serial => serial::scalar_mul::vartime_double_base::mul(a, A, b),
    }
}
