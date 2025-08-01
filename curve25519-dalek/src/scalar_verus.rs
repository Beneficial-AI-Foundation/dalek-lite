// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2021 isis lovecruft
// Copyright (c) 2016-2019 Henry de Valence
// Portions Copyright 2017 Brian Smith
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>
// - Brian Smith <brian@briansmith.org>

//! Arithmetic on scalars (integers mod the group order) - Verus verification version.
//!
//! Both the Ristretto group and the Ed25519 basepoint have prime order
//! \\( \ell = 2\^{252} + 27742317777372353535851937790883648493 \\).
//!
//! This code is intended to be useful with both the Ristretto group
//! (where everything is done modulo \\( \ell \\)), and the X/Ed25519
//! setting, which mandates specific bit-twiddles that are not
//! well-defined modulo \\( \ell \\).
//!
//! All arithmetic on `Scalars` is done modulo \\( \ell \\).

#![allow(unused)]

use vstd::prelude::*;



use subtle::Choice;

use subtle::ConstantTimeEq;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

use crate::backend;
use crate::constants;

verus! {


type UnpackedScalar = backend::serial::u64::scalar::Scalar52;

/// The `Scalar` struct holds an element of \\(\mathbb Z / \ell\mathbb Z \\).
#[allow(clippy::derived_hash_with_manual_eq)]
#[derive(Copy, Clone, Hash)]
pub struct Scalar {
    /// `bytes` is a little-endian byte encoding of an integer representing a scalar modulo the
    /// group order.
    ///
    /// # Invariant #1
    ///
    /// The integer representing this scalar is less than \\(2\^{255}\\). That is, the most
    /// significant bit of `bytes[31]` is 0.
    ///
    /// This is required for `EdwardsPoint` variable- and fixed-base multiplication, because most
    /// integers above 2^255 are unrepresentable in our radix-16 NAF (see [`Self::as_radix_16`]).
    /// The invariant is also required because our `MontgomeryPoint` multiplication assumes the MSB
    /// is 0 (see `MontgomeryPoint::mul`).
    ///
    /// # Invariant #2 (weak)
    ///
    /// The integer representing this scalar is less than \\(2\^{255} - 19 \\), i.e., it represents
    /// a canonical representative of an element of \\( \mathbb Z / \ell\mathbb Z \\). This is
    /// stronger than invariant #1. It also sometimes has to be broken.
    ///
    /// This invariant is deliberately broken in the implementation of `EdwardsPoint::{mul_clamped,
    /// mul_base_clamped}`, `MontgomeryPoint::{mul_clamped, mul_base_clamped}`, and
    /// `BasepointTable::mul_base_clamped`. This is not an issue though. As mentioned above,
    /// scalar-point multiplication is defined for any choice of `bytes` that satisfies invariant
    /// #1. Since clamping guarantees invariant #1 is satisfied, these operations are well defined.
    ///
    /// Note: Scalar-point mult is the _only_ thing you can do safely with an unreduced scalar.
    /// Scalar-scalar addition and subtraction are NOT correct when using unreduced scalars.
    /// Multiplication is correct, but this is only due to a quirk of our implementation, and not
    /// guaranteed to hold in general in the future.
    ///
    /// Note: It is not possible to construct an unreduced `Scalar` from the public API unless the
    /// `legacy_compatibility` is enabled (thus making `Scalar::from_bits` public). Thus, for all
    /// public non-legacy uses, invariant #2
    /// always holds.
    ///
    pub bytes: [u8; 32],
}


impl Scalar {

    /// The scalar \\( 1 \\).
    pub const ONE: Self = Self {
        bytes: [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ],
    };


    /// Note: Stub implementation for verification module
    pub fn invert(&self) -> Scalar {
        // Stub implementation for verification module
        Scalar::ONE
    }

}

}
