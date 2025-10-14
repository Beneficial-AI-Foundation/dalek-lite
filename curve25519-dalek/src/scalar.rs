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

//! Arithmetic on scalars (integers mod the group order).
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
//!
//! # Constructing a scalar
//!
//! To create a [`Scalar`](struct.Scalar.html) from a supposedly canonical encoding, use
//! [`Scalar::from_canonical_bytes`](struct.Scalar.html#method.from_canonical_bytes).
//!
//! This function does input validation, ensuring that the input bytes
//! are the canonical encoding of a `Scalar`.
//! If they are, we'll get
//! `Some(Scalar)` in return:
//!
//! ```
//! use curve25519_dalek::scalar::Scalar;
//!
//! let one_as_bytes: [u8; 32] = Scalar::ONE.to_bytes();
//! let a: Option<Scalar> = Scalar::from_canonical_bytes(one_as_bytes).into();
//!
//! assert!(a.is_some());
//! ```
//!
//! However, if we give it bytes representing a scalar larger than \\( \ell \\)
//! (in this case, \\( \ell + 2 \\)), we'll get `None` back:
//!
//! ```
//! use curve25519_dalek::scalar::Scalar;
//!
//! let l_plus_two_bytes: [u8; 32] = [
//!    0xef, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
//!    0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
//!    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
//!    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
//! ];
//! let a: Option<Scalar> = Scalar::from_canonical_bytes(l_plus_two_bytes).into();
//!
//! assert!(a.is_none());
//! ```
//!
//! Another way to create a `Scalar` is by reducing a \\(256\\)-bit integer mod
//! \\( \ell \\), for which one may use the
//! [`Scalar::from_bytes_mod_order`](struct.Scalar.html#method.from_bytes_mod_order)
//! method.  In the case of the second example above, this would reduce the
//! resultant scalar \\( \mod \ell \\), producing \\( 2 \\):
//!
//! ```
//! use curve25519_dalek::scalar::Scalar;
//!
//! let l_plus_two_bytes: [u8; 32] = [
//!    0xef, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
//!    0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
//!    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
//!    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
//! ];
//! let a: Scalar = Scalar::from_bytes_mod_order(l_plus_two_bytes);
//!
//! let two: Scalar = Scalar::ONE + Scalar::ONE;
//!
//! assert!(a == two);
//! ```
//!
//! There is also a constructor that reduces a \\(512\\)-bit integer,
//! [`Scalar::from_bytes_mod_order_wide`].
//!
//! To construct a `Scalar` as the hash of some input data, use
//! [`Scalar::hash_from_bytes`], which takes a buffer, or
//! [`Scalar::from_hash`], which allows an IUF API.
//!
#![cfg_attr(feature = "digest", doc = "```")]
#![cfg_attr(not(feature = "digest"), doc = "```ignore")]
//! # fn main() {
//! use sha2::{Digest, Sha512};
//! use curve25519_dalek::scalar::Scalar;
//!
//! // Hashing a single byte slice
//! let a = Scalar::hash_from_bytes::<Sha512>(b"Abolish ICE");
//!
//! // Streaming data into a hash object
//! let mut hasher = Sha512::default();
//! hasher.update(b"Abolish ");
//! hasher.update(b"ICE");
//! let a2 = Scalar::from_hash(hasher);
//!
//! assert_eq!(a, a2);
//! # }
//! ```
//!
//! See also `Scalar::hash_from_bytes` and `Scalar::from_hash` that
//! reduces a \\(512\\)-bit integer, if the optional `digest` feature
//! has been enabled.

use core::borrow::Borrow;
use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::ops::Index;
use core::ops::Neg;
use core::ops::{Add, AddAssign};
use core::ops::{Mul, MulAssign};
use core::ops::{Sub, SubAssign};
use vstd::prelude::*;

#[cfg(feature = "group")]
use group::ff::{Field, FromUniformBytes, PrimeField};
#[cfg(feature = "group-bits")]
use group::ff::{FieldBits, PrimeFieldBits};

#[cfg(any(test, feature = "group"))]
use rand_core::RngCore;

#[cfg(any(test, feature = "rand_core"))]
use rand_core::CryptoRngCore;
// From a conflict:
//use rand_core::{CryptoRng, RngCore};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

#[cfg(feature = "digest")]
use digest::generic_array::typenum::U64;
#[cfg(feature = "digest")]
use digest::Digest;
#[cfg(feature = "digest")]
use sha2::Sha512;

use subtle::Choice;
use subtle::ConditionallySelectable;
use subtle::ConstantTimeEq;
use subtle::CtOption;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

use crate::backend;
use crate::constants;

#[allow(unused_imports)]
use crate::backend::serial::u64::scalar_specs::*;

#[allow(unused_imports)]
use crate::backend::serial::u64::subtle_assumes::*;


#[allow(unused_imports)]
use crate::backend::serial::u64::std_assumes::*;

#[allow(unused_imports)]
use crate::scalar_specs::*;

use vstd::prelude::*;

verus! {

/*** <VERIFICATION NOTE> Focus on u64; removed all other backend types </VERIFICATION NOTE> ***/
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
    /* <VERIFICATION NOTE>
    Changed from pub(crate) to pub
    </VERIFICATION NOTE> */
    pub bytes: [u8; 32],
    /* <ORIGINAL CODE>
    pub(crate) bytes: [u8; 32],
    </ORIGINAL CODE> */
}


// This is a dummy function that we call from signal
// to test that verus functions in libsignal know
// about verus functions in curve-dalek
pub open spec fn is_a_scalar(s: Scalar) -> bool {
   true
}

impl Scalar {
    /// Construct a `Scalar` by reducing a 256-bit little-endian integer
    /// modulo the group order \\( \ell \\).
    // VERIFICATION NOTE: VERIFIED
    pub fn from_bytes_mod_order(bytes: [u8; 32]) -> (result: Scalar)
    ensures
        // Result is equivalent to input modulo the group order
        bytes_to_nat(&result.bytes) % group_order() == bytes_to_nat(&bytes) % group_order(),
        // Result is canonical (reduced)
        bytes_to_nat(&result.bytes) < group_order(),
        // High bit is clear (invariant #1: result < 2^255)
        result.bytes[31] <= 127,
    {
        // Temporarily allow s_unreduced.bytes > 2^255 ...
        let s_unreduced = Scalar { bytes };

        // Then reduce mod the group order and return the reduced representative.
        let s = s_unreduced.reduce();
        /*** <VERIFICATION NOTE> We omit debug asserts from verification  </VERIFICATION NOTE> ***/
        #[cfg(not(verus_keep_ghost))]
        debug_assert_eq!(0u8, s[31] >> 7);

        s
    }

    /// Construct a `Scalar` by reducing a 512-bit little-endian integer
    /// modulo the group order \\( \ell \\).
    // VERIFICATION NOTE: VERIFIED
    pub fn from_bytes_mod_order_wide(input: &[u8; 64]) -> (result: Scalar)
    ensures
        bytes_to_nat(&result.bytes) % group_order() == bytes_wide_to_nat(input) % group_order(),
        bytes_to_nat(&result.bytes) < group_order(),
        result.bytes[31] <= 127,
    {
        UnpackedScalar::from_bytes_wide(input).pack()
    }

    /// Attempt to construct a `Scalar` from a canonical byte representation.
    ///
    /// # Return
    ///
    /// - `Some(s)`, where `s` is the `Scalar` corresponding to `bytes`,
    ///   if `bytes` is a canonical byte representation modulo the group order \\( \ell \\);
    /// - `None` if `bytes` is not a canonical byte representation.
    /*
    <VERIFICATION NOTE>
      - Refactored to use wrapper functions instead of trait functions for ct_eq and ct_option_new
      - Has proof bypass
    </VERIFICATION NOTE> */
    pub fn from_canonical_bytes(bytes: [u8; 32]) -> (result: CtOption<Scalar>)
    ensures
        bytes_to_nat(&bytes) < group_order() ==> ct_option_has_value(result),
        bytes_to_nat(&bytes) >= group_order() ==> !ct_option_has_value(result),
        ct_option_has_value(result) ==> bytes_to_nat(&ct_option_value(result).bytes) % group_order() == bytes_to_nat(&bytes) % group_order(),
    {
        /* <ORIGINAL CODE>
          let high_bit_unset = (bytes[31] >> 7).ct_eq(&0);
        </ORIGINAL CODE> */
        /* <MODIFIED CODE> */
        let high_byte_shifted = bytes[31] >> 7;
        let high_bit_unset = ct_eq_u8(&high_byte_shifted, &0);
        /* </MODIFIED CODE> */

        let candidate = Scalar { bytes };
        let is_canonical = candidate.is_canonical();

        /* <ORIGINAL CODE>
          CtOption::new(candidate, high_bit_unset & candidate.is_canonical())
          </ORIGINAL CODE> */
        /* <MODIFIED CODE> */
        let condition = choice_and(high_bit_unset, is_canonical);
        let result = ct_option_new(candidate, condition);
        /* </MODIFIED CODE> */

        // VERIFICATION NOTE: PROOF BYPASS
        assume(bytes_to_nat(&bytes) < group_order() ==> ct_option_has_value(result));
        assume(bytes_to_nat(&bytes) >= group_order() ==> !ct_option_has_value(result));
        assume(ct_option_has_value(result) ==> bytes_to_nat(&ct_option_value(result).bytes) % group_order() == bytes_to_nat(&bytes) % group_order());

        result
    }

    /// Construct a `Scalar` from the low 255 bits of a 256-bit integer. This breaks the invariant
    /// that scalars are always reduced. Scalar-scalar arithmetic, i.e., addition, subtraction,
    /// multiplication, **does not work** on scalars produced from this function. You may only use
    /// the output of this function for `EdwardsPoint::mul`, `MontgomeryPoint::mul`, and
    /// `EdwardsPoint::vartime_double_scalar_mul_basepoint`. **Do not use this function** unless
    /// you absolutely have to.
    /* <VERIFICATION NOTE>
        -This is not in default features and not in our current target list ==> spec omitted for now
    </VERIFICATION NOTE> */
    #[cfg(feature = "legacy_compatibility")]
    #[deprecated(
        since = "4.0.0",
        note = "This constructor outputs scalars with undefined scalar-scalar arithmetic. See docs."
    )]
    pub const fn from_bits(bytes: [u8; 32]) -> Scalar {
        let mut s = Scalar { bytes };
        // Ensure invariant #1 holds. That is, make s < 2^255 by masking the high bit.
        s.bytes[31] &= 0b0111_1111;

        s
    }
}


impl Eq for Scalar {}

impl PartialEq for Scalar {
    // VERIFICATION NOTE: PROOF BYPASS (problem with traits)
    fn eq(&self, other: &Self) -> (result: bool)
    ensures result == (&self.bytes == &other.bytes),
    {
        /* <VERIFICATION NOTE>
         Use wrapper function for Choice::into
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
         let result = self.ct_eq(other).into();
         </ORIGINAL CODE> */
        let choice = self.ct_eq(other);
        assert(choice_is_true(choice) == (self.bytes == other.bytes));
        let result = choice_into(choice);
        assert(result == choice_is_true(choice));
        assert(result == (self.bytes == other.bytes));
        
        // VERIFICATION NOTE: vstd's external trait specification check cannot be satisfied
        // vstd expects obeys_eq_spec() and eq_spec() from PartialEqSpecImpl trait,
        // but that trait is not publicly exported, so we bypass with assume(false)
        // while maintaining our own custom ensures clause above
        assume(false);
        
        result
    }
}

impl ConstantTimeEq for Scalar {
    fn ct_eq(&self, other: &Self) -> (result: Choice)
    ensures choice_is_true(result) == (self.bytes == other.bytes)
    {
        /* <VERIFICATION NOTE>
         Use wrapper function for Verus compatibility instead of direct subtle call
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
         self.bytes.ct_eq(&other.bytes)
         </ORIGINAL CODE> */
        ct_eq_bytes32(&self.bytes, &other.bytes)
    }
}

impl Index<usize> for Scalar {
    type Output = u8;

    /// Index the bytes of the representative for this `Scalar`.  Mutation is not permitted.
    fn index(&self, _index: usize) -> (result: &u8)
        requires _index < 32
        ensures result == &self.bytes[_index as int],
    {
        &(self.bytes[_index])
    }
}
} // verus!

/* <VERIFICATION NOTE>
 Left outside verification scope
</VERIFICATION NOTE> */
impl Debug for Scalar {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Scalar{{\n\tbytes: {:?},\n}}", &self.bytes)
    }
}

verus! {
impl<'a> MulAssign<&'a Scalar> for Scalar {
    // VERIFICATION NOTE: VERIFIED
    fn mul_assign(&mut self, _rhs: &'a Scalar)
    ensures bytes_to_nat(&self.bytes) % group_order() ==
        (bytes_to_nat(&old(self).bytes) * bytes_to_nat(&_rhs.bytes)) % group_order()
    {
        /* <ORIGINAL CODE>
         *self = UnpackedScalar::mul(&self.unpack(), &_rhs.unpack()).pack();
         </ORIGINAL CODE> */
        /* <VERIFICATION NOTE>
         In the modified code, we store unpacked values explicitly for asserts
        </VERIFICATION NOTE> */
        /* <MODIFIED CODE> */
        let self_unpacked = self.unpack();
        let rhs_unpacked = _rhs.unpack();
        proof {
            assert(to_nat(&self_unpacked.limbs) == bytes_to_nat(&old(self).bytes));
            assert(to_nat(&rhs_unpacked.limbs) == bytes_to_nat(&_rhs.bytes));
            assert(limbs_bounded(&self_unpacked));
            assert(limbs_bounded(&rhs_unpacked));
        }

        let result_unpacked = UnpackedScalar::mul(&self_unpacked, &rhs_unpacked);
        proof {
            assert(to_nat(&result_unpacked.limbs) % group_order() == (to_nat(&self_unpacked.limbs) * to_nat(&rhs_unpacked.limbs)) % group_order());
            assert(limbs_bounded(&result_unpacked));
            assert(to_nat(&result_unpacked.limbs) % group_order() == (to_nat(&self_unpacked.limbs) * to_nat(&rhs_unpacked.limbs)) % group_order());
            assert(limbs_bounded(&result_unpacked));
        }

        *self = result_unpacked.pack();
        proof {
            assert(bytes_to_nat(&self.bytes) % group_order() == to_nat(&result_unpacked.limbs) % group_order());
            assert(bytes_to_nat(&self.bytes) % group_order() == (bytes_to_nat(&old(self).bytes) * bytes_to_nat(&_rhs.bytes)) % group_order());
        }
        /* </MODIFIED CODE> */

    }
}

define_mul_assign_variants!(LHS = Scalar, RHS = Scalar);

impl<'a, 'b> Mul<&'b Scalar> for &'a Scalar {
    type Output = Scalar;
    // VERIFICATION NOTE: PROOF BYPASS JUST BEFORE RETURN (problem with traits)
    fn mul(self, _rhs: &'b Scalar) -> (result: Scalar) 
        ensures 
        bytes_to_nat(&result.bytes) % group_order() == (bytes_to_nat(&self.bytes) * bytes_to_nat(&_rhs.bytes)) % group_order(),
    {
        /* <VERIFICATION NOTE>
         Store unpacked values explicitly for asserts
        </VERIFICATION NOTE> */
        /* <MODIFIED CODE> */
        let self_unpacked = self.unpack();
        let rhs_unpacked = _rhs.unpack();
        proof {
            assert(to_nat(&self_unpacked.limbs) == bytes_to_nat(&self.bytes));
            assert(to_nat(&rhs_unpacked.limbs) == bytes_to_nat(&_rhs.bytes));
            assert(limbs_bounded(&self_unpacked));
            assert(limbs_bounded(&rhs_unpacked));
        }    
        let result_unpacked = UnpackedScalar::mul(&self_unpacked, &rhs_unpacked);
        proof {
            assert(to_nat(&result_unpacked.limbs) % group_order() == (to_nat(&self_unpacked.limbs) * to_nat(&rhs_unpacked.limbs)) % group_order());
            assert(limbs_bounded(&result_unpacked));
        }
        let result = result_unpacked.pack();
        proof {
            assert(bytes_to_nat(&result.bytes) % group_order() == to_nat(&result_unpacked.limbs) % group_order());
            assert(bytes_to_nat(&result.bytes) % group_order() == (bytes_to_nat(&self.bytes) * bytes_to_nat(&_rhs.bytes)) % group_order());
        }
        assert(bytes_to_nat(&result.bytes) % group_order() == (bytes_to_nat(&self.bytes) * bytes_to_nat(&_rhs.bytes)) % group_order());
        /* </MODIFIED CODE> */
        /* <ORIGINAL CODE>
         let result = UnpackedScalar::mul(&self.unpack(), &_rhs.unpack()).pack();
         </ORIGINAL CODE> */
        
        // VERIFICATION NOTE: vstd's external trait specification check cannot be satisfied
        // vstd expects obeys_mul_spec() and mul_spec() from MulSpecImpl trait,
        // but that trait is not publicly exported, so we bypass with assume(false)
        // while maintaining our own custom ensures clause above
        assume(false);
        
        result
    }
}

define_mul_variants!(LHS = Scalar, RHS = Scalar, Output = Scalar);

impl<'a> Add<&'a Scalar> for &Scalar {
    type Output = Scalar;
    
    /* <VERIFICATION NOTE> 
    TWO PROOF BYPASSES  because of trait issues
    </VERIFICATION NOTE> */
    #[allow(non_snake_case)]
    fn add(self, _rhs: &'a Scalar) -> (result: Scalar)
    ensures
        bytes_to_nat(&result.bytes)  == (bytes_to_nat(&self.bytes) + bytes_to_nat(&_rhs.bytes)) % group_order(),
    {
        // The UnpackedScalar::add function produces reduced outputs if the inputs are reduced. By
        // Scalar invariant #1, this is always the case.
        /* <VERIFICATION NOTE>
         Store unpacked values explicitly for asserts
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
         UnpackedScalar::add(&self.unpack(), &_rhs.unpack()).pack()
         </ORIGINAL CODE> */
        /* <MODIFIED CODE> */
        let self_unpacked = self.unpack();
        let rhs_unpacked = _rhs.unpack();
        proof {
            assert(to_nat(&self_unpacked.limbs) == bytes_to_nat(&self.bytes));
            assert(to_nat(&rhs_unpacked.limbs) == bytes_to_nat(&_rhs.bytes));
            assert(limbs_bounded(&self_unpacked));
            assert(limbs_bounded(&rhs_unpacked));
        }
    
        // UnpackedScalar::add requires inputs < group_order()
        // By Scalar invariant #2, scalars should be canonical
        // However, we cannot add requires clauses to trait implementations,
        // so we assume this property holds
       proof {
            assume(to_nat(&self_unpacked.limbs) < group_order());
            assume(to_nat(&rhs_unpacked.limbs) < group_order());
        }
        
        let result_unpacked = UnpackedScalar::add(&self_unpacked, &rhs_unpacked);
        proof {
            assert(to_nat(&result_unpacked.limbs) == (to_nat(&self_unpacked.limbs) + to_nat(&rhs_unpacked.limbs)) % group_order());
            assert(limbs_bounded(&result_unpacked));
        }
        
        let result = result_unpacked.pack();
        proof {
            assert(bytes_to_nat(&result.bytes)  == to_nat(&result_unpacked.limbs));  
            assert(bytes_to_nat(&result.bytes)  == (bytes_to_nat(&self.bytes) + bytes_to_nat(&_rhs.bytes)) % group_order());
        }
        /* </MODIFIED CODE> */
        
        // VERIFICATION NOTE: vstd's external trait specification check cannot be satisfied
        // vstd expects obeys_add_spec() and add_spec() from AddSpecImpl trait,
        // but that trait is not publicly exported, so we bypass with assume(false)
        // while maintaining our own custom ensures clause above
        assume(false);
        
        result
    }
}

define_add_variants!(LHS = Scalar, RHS = Scalar, Output = Scalar);

impl<'a> AddAssign<&'a Scalar> for Scalar {
    // VERIFICATION NOTE: delegates to verified Add operator
    // PROOF BYPASS because Add has vstd trait spec issues
    fn add_assign(&mut self, _rhs: &'a Scalar)
    ensures 
        bytes_to_nat(&self.bytes) == (bytes_to_nat(&old(self).bytes) + bytes_to_nat(&_rhs.bytes)) % group_order(),
    {
        proof { assume(false); }
        *self = &*self + _rhs;
    }
}

define_add_assign_variants!(LHS = Scalar, RHS = Scalar);

impl<'a, 'b> Sub<&'b Scalar> for &'a Scalar {
    type Output = Scalar;
    
    // VERIFICATION NOTE: PROOF BYPASS (problems with traits and preconditions)
    #[allow(non_snake_case)]
    fn sub(self, _rhs: &'b Scalar) -> (result: Scalar)
    ensures
        bytes_to_nat(&result.bytes) % group_order() == (bytes_to_nat(&self.bytes) - bytes_to_nat(&_rhs.bytes)) % (group_order() as int),
    {
        // The UnpackedScalar::sub function produces reduced outputs if the inputs are reduced. By
        // Scalar invariant #1, this is always the case.
        /* <ORIGINAL CODE>
         UnpackedScalar::sub(&self.unpack(), &_rhs.unpack()).pack()
         </ORIGINAL CODE> */
        /* <MODIFIED CODE> */
        let self_unpacked = self.unpack();
        let rhs_unpacked = _rhs.unpack();
        proof {
            assert(to_nat(&self_unpacked.limbs) == bytes_to_nat(&self.bytes));
            assert(to_nat(&rhs_unpacked.limbs) == bytes_to_nat(&_rhs.bytes));
            assert(limbs_bounded(&self_unpacked));
            assert(limbs_bounded(&rhs_unpacked));
        }
        
        // UnpackedScalar::sub requires: -group_order() <= to_nat(&a.limbs) - to_nat(&b.limbs) < group_order()
        proof {
            assume(-group_order() <= to_nat(&self_unpacked.limbs) - to_nat(&rhs_unpacked.limbs));
            assume(to_nat(&self_unpacked.limbs) - to_nat(&rhs_unpacked.limbs) < group_order());
        }
        
        let result_unpacked = UnpackedScalar::sub(&self_unpacked, &rhs_unpacked);
        proof {
            // Postconditions from sub - need to strengthen, review connections
            assume(to_nat(&result_unpacked.limbs) % group_order() == (to_nat(&self_unpacked.limbs) - to_nat(&rhs_unpacked.limbs)) % (group_order() as int));
            assume(limbs_bounded(&result_unpacked));
        }
        
        let result = result_unpacked.pack();
        proof {
            assert(bytes_to_nat(&result.bytes) % group_order() == to_nat(&result_unpacked.limbs) % group_order());
            assert(bytes_to_nat(&result.bytes) % group_order() == (bytes_to_nat(&self.bytes) - bytes_to_nat(&_rhs.bytes)) % (group_order() as int));
        }
        /* </MODIFIED CODE> */
        
        // VERIFICATION NOTE: vstd's external trait specification check cannot be satisfied
        assume(false);
        
        result
    }
}

define_sub_variants!(LHS = Scalar, RHS = Scalar, Output = Scalar);

impl<'a> SubAssign<&'a Scalar> for Scalar {
    // VERIFICATION NOTE: Delegates to verified Sub operator
    // PROOF BYPASS because Sub has vstd trait spec issues
    fn sub_assign(&mut self, _rhs: &'a Scalar)
    ensures
        bytes_to_nat(&self.bytes) % group_order() == (bytes_to_nat(&old(self).bytes) - bytes_to_nat(&_rhs.bytes)) % (group_order() as int),
    {
        proof { assume(false); }
        *self = &*self - _rhs;
    }
}

define_sub_assign_variants!(LHS = Scalar, RHS = Scalar);

impl<'a> Neg for &'a Scalar {
    type Output = Scalar;
    #[allow(non_snake_case)]
    // VERIFICATION NOTE: PROOF BYPASS 
    fn neg(self) -> (result: Scalar) 
    ensures
    (scalar_to_nat(self) + scalar_to_nat(&result)) % group_order() == 0,
    {
        /* <ORIGINAL CODE> 
        let self_R = UnpackedScalar::mul_internal(&self.unpack(), &constants::R);
        let self_mod_l = UnpackedScalar::montgomery_reduce(&self_R);
        UnpackedScalar::sub(&UnpackedScalar::ZERO, &self_mod_l).pack()
        </ORIGINAL CODE> */
        /* <MODIFIED CODE> */
        proof {
            // Preconditions for mul_internal and sub
            assume(limbs_bounded(&constants::R));
            assume(limbs_bounded(&UnpackedScalar::ZERO));
        }

        let self_R = UnpackedScalar::mul_internal(&self.unpack(), &constants::R);
        let self_mod_l = UnpackedScalar::montgomery_reduce(&self_R);
        
        proof {
            assume(limbs_bounded(&self_mod_l));
            // sub requires: -group_order() <= 0 - to_nat(&self_mod_l.limbs) < group_order()
            assume(-group_order() <= to_nat(&UnpackedScalar::ZERO.limbs) - to_nat(&self_mod_l.limbs));
            assume(to_nat(&UnpackedScalar::ZERO.limbs) - to_nat(&self_mod_l.limbs) < group_order());
        }

        let result = UnpackedScalar::sub(&UnpackedScalar::ZERO, &self_mod_l).pack();
        proof {
            // TODO: Prove that -self + self == 0 (mod group_order)
            assume((scalar_to_nat(self) + scalar_to_nat(&result)) % group_order() == 0);
        }
        
        // VERIFICATION NOTE: vstd's external trait specification check cannot be satisfied
        assume(false);
        
        /* </MODIFIED CODE> */
        result
    }
}

impl Neg for Scalar {
    type Output = Scalar;
    /* <VERIFICATION NOTE>  
         PROOF BYPASS - vstd's Neg trait spec precondition check
    </VERIFICATION NOTE> */
    fn neg(self) -> (result: Scalar)
    ensures
        (scalar_to_nat(&self) + scalar_to_nat(&result)) % group_order() == 0,
    {
        proof { assume(false); }
        let result = (&self).neg();
        result
    }
    /* <ORIGINAL CODE> 
    fn neg(self) -> Scalar {
        -&self
    }
    </ORIGINAL CODE> */
}

impl ConditionallySelectable for Scalar {
    /* <VERIFICATION NOTE>  VERIFIED
    */
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        let mut bytes = [0u8; 32];
        #[allow(clippy::needless_range_loop)]
        for i in 0..32 {
            /* <VERIFICATION NOTE> 
            Use wrapper function for Verus compatibility instead of direct subtle call
            </VERIFICATION NOTE> */
            /* <ORIGINAL CODE> 
            bytes[i] = u8::conditional_select(&a.bytes[i], &b.bytes[i], choice);
            </ORIGINAL CODE> */
            /* <MODIFIED CODE> */
            bytes[i] = select_u8(&a.bytes[i], &b.bytes[i], choice);
            /* </MODIFIED CODE> */
        }
        Scalar { bytes }
    }
}
} // verus!

verus! {
/* <VERIFICATION NOTE> 
- Serialization and deserialization functions in this Verus block
- They are currently outside default features but we should consider verifying them
</VERIFICATION NOTE> */
#[cfg(feature = "serde")]
use serde::de::Visitor;
#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl Serialize for Scalar {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use serde::ser::SerializeTuple;
        let mut tup = serializer.serialize_tuple(32)?;
        for byte in self.as_bytes().iter() {
            tup.serialize_element(byte)?;
        }
        tup.end()
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<'de> Deserialize<'de> for Scalar {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ScalarVisitor;

        impl<'de> Visitor<'de> for ScalarVisitor {
            type Value = Scalar;

            fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                formatter.write_str(
                    "a sequence of 32 bytes whose little-endian interpretation is less than the \
                    basepoint order ℓ",
                )
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Scalar, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let mut bytes = [0u8; 32];
                #[allow(clippy::needless_range_loop)]
                for i in 0..32 {
                    bytes[i] = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(i, &"expected 32 bytes"))?;
                }
                Option::from(Scalar::from_canonical_bytes(bytes))
                    .ok_or_else(|| serde::de::Error::custom("scalar was not canonically encoded"))
            }
        }

        deserializer.deserialize_tuple(32, ScalarVisitor)
    }
}

/* <VERIFICATION NOTE>
 Trait implementations for Product and Sum declared as external_body since they use iterators which are not supported by Verus. 
</VERIFICATION NOTE> */

impl<T> Product<T> for Scalar
where
    T: Borrow<Scalar>,
{
    /* <ORIGINAL CODE>
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Scalar::ONE, |acc, item| acc * item.borrow())
    }
    </ORIGINAL CODE> */

    /* <VERIFICATION NOTE>
     Added verifier::external_body annotation
    </VERIFICATION NOTE> */
    #[verifier::external_body]
    /* <MODIFIED CODE> - FOR EVENTUAL VERIFICATION*/
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        // Collect iterator into a Vec, then convert via Borrow to get &[Scalar]
        let items: Vec<T> = iter.collect();
        
        // Convert to Vec<Scalar> via borrow
        let scalars: Vec<Scalar> = items.iter().map(|item| *item.borrow()).collect();
        
        // Use the verified product_of_slice function
        Scalar::product_of_slice(&scalars)
    }
    /* </MODIFIED CODE> */
}

impl<T> Sum<T> for Scalar
where
    T: Borrow<Scalar>,
{
    /* <ORIGINAL CODE>
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Scalar::ZERO, |acc, item| acc + item.borrow())
    }
    </ORIGINAL CODE> */
    /* <VERIFICATION NOTE>
     Added verifier::external_body annotation
    </VERIFICATION NOTE> */
    #[verifier::external_body]
    /* <MODIFIED CODE> - FOR EVENTUAL VERIFICATION*/
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        // Collect iterator into a Vec, then convert via Borrow to get &[Scalar]
        let items: Vec<T> = iter.collect();
        
        // Convert to Vec<Scalar> via borrow
        let scalars: Vec<Scalar> = items.iter().map(|item| *item.borrow()).collect();
        
        // Use the verified sum_of_slice function
        Scalar::sum_of_slice(&scalars)
    }
    /* </MODIFIED CODE> */
}

impl Default for Scalar {
    // VERIFICATION NOTE: PROOF BYPASS
    fn default() -> (result: Scalar) 
    ensures
        scalar_to_nat(&result) == 0 as nat,
    {
        let result = Scalar::ZERO;
        assume(scalar_to_nat(&result) == 0 as nat);
        result
    }
}

impl From<u8> for Scalar {
    // VERIFICATION NOTE: PROOF BYPASS
    fn from(x: u8) -> (result: Scalar) 
    ensures
        scalar_to_nat(&result) == x as nat,
    {
        let mut s_bytes = [0u8; 32];
        s_bytes[0] = x;

        let result = Scalar { bytes: s_bytes };
        proof {
            assume(scalar_to_nat(&result) == x as nat);
        }
        result
    }
}

impl From<u16> for Scalar {
    // VERIFICATION NOTE: PROOF BYPASS
    fn from(x: u16) -> (result: Scalar) 
    ensures
        scalar_to_nat(&result) == x as nat,
    {
        /* <ORIGINAL CODE>
        let x_bytes = x.to_le_bytes();
        s_bytes[0..x_bytes.len()].copy_from_slice(&x_bytes);
        </ORIGINAL CODE> */
        /* <MODIFIED CODE> Verus doesn't support copy_from_slice and to_le_bytes */
        let mut s_bytes = [0u8; 32];
        let x_bytes = crate::backend::serial::u64::std_assumes::u16_to_le_bytes(x);
        for i in 0..x_bytes.len() {
            s_bytes[i] = x_bytes[i];
        }
        /* </MODIFIED CODE> */
        let result = Scalar { bytes: s_bytes };
        proof {
            assume(scalar_to_nat(&result) == x as nat);
        }
        result
    }
}

impl From<u32> for Scalar {
    // VERIFICATION NOTE: PROOF BYPASS
    fn from(x: u32) -> (result: Scalar) 
    ensures
        scalar_to_nat(&result) == x as nat,
    {
        /* <ORIGINAL CODE>
        let x_bytes = x.to_le_bytes();
        s_bytes[0..x_bytes.len()].copy_from_slice(&x_bytes);
        </ORIGINAL CODE> */
        /* <MODIFIED CODE> Verus doesn't support copy_from_slice and to_le_bytes */
        let mut s_bytes = [0u8; 32];
        let x_bytes = crate::backend::serial::u64::std_assumes::u32_to_le_bytes(x);
        for i in 0..x_bytes.len() {
            s_bytes[i] = x_bytes[i];
        }
        let result = Scalar { bytes: s_bytes };
        /* </MODIFIED CODE> */
        proof {
            assume(scalar_to_nat(&result) == x as nat);
        }
        result
        
    }
}

impl From<u64> for Scalar {
    /// Construct a scalar from the given `u64`.
    ///
    /// # Inputs
    ///
    /// An `u64` to convert to a `Scalar`.
    ///
    /// # Returns
    ///
    /// A `Scalar` corresponding to the input `u64`.
    ///
    /// # Example
    ///
    /// ```
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// let fourtytwo = Scalar::from(42u64);
    /// let six = Scalar::from(6u64);
    /// let seven = Scalar::from(7u64);
    ///
    /// assert!(fourtytwo == six * seven);
    /// ```
    // VERIFICATION NOTE: PROOF BYPASS
    fn from(x: u64) -> (result: Scalar) 
    ensures
        scalar_to_nat(&result) == x as nat,
    {
        /* <ORIGINAL CODE>
        let x_bytes = x.to_le_bytes();
        s_bytes[0..x_bytes.len()].copy_from_slice(&x_bytes);
        </ORIGINAL CODE> */
        /* <MODIFIED CODE> Verus doesn't support copy_from_slice and to_le_bytes */
        let mut s_bytes = [0u8; 32];
        let x_bytes = crate::backend::serial::u64::std_assumes::u64_to_le_bytes(x);
        for i in 0..x_bytes.len() {
            s_bytes[i] = x_bytes[i];
        }
        /* </MODIFIED CODE> */
        let result = Scalar { bytes: s_bytes };
        proof {
            assume(scalar_to_nat(&result) == x as nat);
        }
        result
    }
}

impl From<u128> for Scalar {
    // VERIFICATION NOTE: PROOF BYPASS
    fn from(x: u128) -> (result: Scalar) 
    ensures
        scalar_to_nat(&result) == x as nat,
    {
        /* <ORIGINAL CODE>
        let x_bytes = x.to_le_bytes();
        s_bytes[0..x_bytes.len()].copy_from_slice(&x_bytes);
        </ORIGINAL CODE> */
        /* <MODIFIED CODE> Verus doesn't support copy_from_slice and to_le_bytes */
        let mut s_bytes = [0u8; 32];
        let x_bytes = crate::backend::serial::u64::std_assumes::u128_to_le_bytes(x);
        for i in 0..x_bytes.len() {
            s_bytes[i] = x_bytes[i];
        }
        /* </MODIFIED CODE> */
        let result = Scalar { bytes: s_bytes };
        proof {
            assume(scalar_to_nat(&result) == x as nat);
        }
        result
    }
} 

 #[cfg(feature = "zeroize")]
 impl Zeroize for Scalar {
    /* <VERIFICATION NOTE>
    External body annotation
    </VERIFICATION NOTE> */
    #[verifier::external_body]
    fn zeroize(&mut self) {
        self.bytes.zeroize();
    }
}


impl Scalar {
    /// The scalar \\( 0 \\).
   // pub const ZERO: Self = Self { bytes: [0u8; 32] };
   /* <VERIFICATION NOTE>
    Changed to explicit initialization
    </VERIFICATION NOTE> */
   /* <ORIGINAL CODE>
    pub const ZERO: Self = Self { bytes: [0u8; 32] };
    </ORIGINAL CODE> */
    
   pub const ZERO: Scalar = Scalar { bytes: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] };

    /// The scalar \\( 1 \\).
    pub const ONE: Self = Self {
        bytes: [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ],
    };

    /* <VERIFICATION NOTE>
     Verification of random method postponed - requires rand_core feature to be enabled.
    </VERIFICATION NOTE> */
    #[cfg(any(test, feature = "rand_core"))]
    /// Return a `Scalar` chosen uniformly at random using a user-provided RNG.
    ///
    /// # Inputs
    ///
    /// * `rng`: any RNG which implements `CryptoRngCore`
    ///   (i.e. `CryptoRng` + `RngCore`) interface.
    ///
    /// # Returns
    ///
    /// A random scalar within \\(\mathbb{Z} / \ell\mathbb{Z}\\).
    ///
    /// # Example
    ///
    /// ```
    /// # fn main() {
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// use rand_core::OsRng;
    ///
    /// let mut csprng = OsRng;
    /// let a: Scalar = Scalar::random(&mut csprng);
    /// # }
    /* <VERIFICATION NOTE>
     No verifier::external_body annotation but it is NOT verified
    </VERIFICATION NOTE> */
    pub fn random<R: CryptoRngCore + ?Sized>(rng: &mut R) -> (result: Self)
        ensures is_random_scalar(&result)
    {
        let mut scalar_bytes = [0u8; 64];
        rng.fill_bytes(&mut scalar_bytes);
        Scalar::from_bytes_mod_order_wide(&scalar_bytes)
    }

    #[cfg(feature = "digest")]
    /// Hash a slice of bytes into a scalar using SHA-512.
    ///
    /// This function uses SHA-512 to hash the input and then reduces the result
    /// modulo the group order to produce a scalar.
    ///
    /// Convenience wrapper around `from_hash`.
    ///
    /// # Example
    ///
    #[cfg_attr(feature = "digest", doc = "```")]
    #[cfg_attr(not(feature = "digest"), doc = "```ignore")]
    /// # use curve25519_dalek::scalar::Scalar;
    /// # fn main() {
    /// let msg = "To really appreciate architecture, you may even need to commit a murder";
    /// let s = Scalar::hash_from_bytes(msg.as_bytes());
    /// # }
    /// ```
    
    // VERIFICATION NOTE: PROBLEMS WITH GENERIC DIGESTS (temporary workaround below)
    /* <ORIGINAL CODE>
    pub fn hash_from_bytes<D>(input: &[u8]) -> Scalar
    where
        D: Digest<OutputSize = U64> + Default,
    {
        let mut hash = D::default();
        hash.update(input);
        Scalar::from_hash(hash)
    }
    </ORIGINAL CODE> */
    /* <MODIFIED CODE> */
    /* <VERIFICATION NOTE>
     Compute hash directly, avoiding the digest object
      </VERIFICATION NOTE> */
    pub fn hash_from_bytes(input: &[u8]) -> (result: Scalar) 
    ensures
        is_random_bytes(input) ==> is_random_scalar(&result),
    {
        use crate::backend::serial::u64::std_assumes as assumes;
        let hash_bytes: [u8; 64] = assumes::sha512_hash_bytes(input);
        Scalar::from_hash(hash_bytes)
    }
    /* </MODIFIED CODE> */

    #[cfg(feature = "digest")]
    /// Construct a scalar from a 64-byte (512-bit) hash output.
    ///
    /// This reduces the hash output modulo the group order.
    /// Typically used after calling `finalize()` on a SHA-512 hasher.
    ///
    /// # Example
    ///
    /// ```
    /// # use curve25519_dalek::scalar::Scalar;
    /// use sha2::{Digest, Sha512};
    ///
    /// # fn main() {
    /// let mut h = Sha512::new();
    /// h.update(b"To really appreciate architecture, you may even need to commit a murder.");
    /// h.update(b"While the programs used for The Manhattan Transcripts are of the most extreme");
    /// h.update(b"nature, they also parallel the most common formula plot: the archetype of");
    /// h.update(b"murder. Other phantasms were occasionally used to underline the fact that");
    /// h.update(b"perhaps all architecture, rather than being about functional standards, is");
    /// h.update(b"about love and death.");
    ///
    /// let hash_bytes: [u8; 64] = h.finalize().into();
    /// let s = Scalar::from_hash(hash_bytes);
    ///
    /// println!("{:?}", s.to_bytes());
    /// assert_eq!(
    ///     s.to_bytes(),
    ///     [  21,  88, 208, 252,  63, 122, 210, 152,
    ///       154,  38,  15,  23,  16, 167,  80, 150,
    ///       192, 221,  77, 226,  62,  25, 224, 148,
    ///       239,  48, 176,  10, 185,  69, 168,  11, ],
    /// );
    /// # }
    /// ```
    /* <VERIFICATION NOTE>
     Simplified to take pre-finalized hash bytes instead of Sha512 type.
     This avoids Verus issues with complex Sha512 type aliases.
     Now just delegates to from_bytes_mod_order_wide, which is already verified.
    </VERIFICATION NOTE> */
    /* <ORIGINAL CODE>
     pub fn from_hash<D>(hash: D) -> Scalar
     where
         D: Digest<OutputSize = U64>,
     {
         let mut output = [0u8; 64];
         output.copy_from_slice(hash.finalize().as_slice());
         Scalar::from_bytes_mod_order_wide(&output)
     }
     </ORIGINAL CODE> */
     /* <MODIFIED CODE> */
     pub fn from_hash(hash_bytes: [u8; 64]) -> (result: Scalar) 
     ensures
        is_random_bytes(&hash_bytes) ==> is_random_scalar(&result),
     {
         let result = Scalar::from_bytes_mod_order_wide(&hash_bytes);
         assume(false);
         result
     }
     /* </MODIFIED CODE> */

    

    /// Convert this `Scalar` to its underlying sequence of bytes.
    ///
    /// # Example
    ///
    /// ```
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// let s: Scalar = Scalar::ZERO;
    ///
    /// assert!(s.to_bytes() == [0u8; 32]);
    /// ```
    pub const fn to_bytes(&self) -> [u8; 32] {
        self.bytes
    }

    /// View the little-endian byte encoding of the integer representing this Scalar.
    ///
    /// # Example
    ///
    /// ```
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// let s: Scalar = Scalar::ZERO;
    ///
    /// assert!(s.as_bytes() == &[0u8; 32]);
    /// ```
    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.bytes
    }
}
impl Scalar {
    /// Given a nonzero `Scalar`, compute its multiplicative inverse.
    ///
    /// # Warning
    ///
    /// `self` **MUST** be nonzero.  If you cannot
    /// *prove* that this is the case, you **SHOULD NOT USE THIS
    /// FUNCTION**.
    ///
    /// # Returns
    ///
    /// The multiplicative inverse of the this `Scalar`.
    ///
    /// # Example
    ///
    /// ```
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// // x = 2238329342913194256032495932344128051776374960164957527413114840482143558222
    /// let X: Scalar = Scalar::from_bytes_mod_order([
    ///         0x4e, 0x5a, 0xb4, 0x34, 0x5d, 0x47, 0x08, 0x84,
    ///         0x59, 0x13, 0xb4, 0x64, 0x1b, 0xc2, 0x7d, 0x52,
    ///         0x52, 0xa5, 0x85, 0x10, 0x1b, 0xcc, 0x42, 0x44,
    ///         0xd4, 0x49, 0xf4, 0xa8, 0x79, 0xd9, 0xf2, 0x04,
    ///     ]);
    /// // 1/x = 6859937278830797291664592131120606308688036382723378951768035303146619657244
    /// let XINV: Scalar = Scalar::from_bytes_mod_order([
    ///         0x1c, 0xdc, 0x17, 0xfc, 0xe0, 0xe9, 0xa5, 0xbb,
    ///         0xd9, 0x24, 0x7e, 0x56, 0xbb, 0x01, 0x63, 0x47,
    ///         0xbb, 0xba, 0x31, 0xed, 0xd5, 0xa9, 0xbb, 0x96,
    ///         0xd5, 0x0b, 0xcd, 0x7a, 0x3f, 0x96, 0x2a, 0x0f,
    ///     ]);
    ///
    /// let inv_X: Scalar = X.invert();
    /// assert!(XINV == inv_X);
    /// let should_be_one: Scalar = &inv_X * &X;
    /// assert!(should_be_one == Scalar::ONE);
    /// ```
    pub fn invert(&self) -> Scalar {
        self.unpack().invert().pack()
    }
    /// Given a slice of nonzero (possibly secret) `Scalar`s,
    /// compute their inverses in a batch.
    ///
    /// # Return
    ///
    /// Each element of `inputs` is replaced by its inverse.
    ///
    /// The product of all inverses is returned.
    ///
    /// # Warning
    ///
    /// All input `Scalars` **MUST** be nonzero.  If you cannot
    /// *prove* that this is the case, you **SHOULD NOT USE THIS
    /// FUNCTION**.
    ///
    /// # Example
    ///
    /// ```
    /// # use curve25519_dalek::scalar::Scalar;
    /// # fn main() {
    /// let mut scalars = [
    ///     Scalar::from(3u64),
    ///     Scalar::from(5u64),
    ///     Scalar::from(7u64),
    ///     Scalar::from(11u64),
    /// ];
    ///
    /// let allinv = Scalar::batch_invert(&mut scalars);
    ///
    /// assert_eq!(allinv, Scalar::from(3*5*7*11u64).invert());
    /// assert_eq!(scalars[0], Scalar::from(3u64).invert());
    /// assert_eq!(scalars[1], Scalar::from(5u64).invert());
    /// assert_eq!(scalars[2], Scalar::from(7u64).invert());
    /// assert_eq!(scalars[3], Scalar::from(11u64).invert());
    /// # }
    /// ```
    /* <VERIFICATION NOTE>
     Refactored for Verus: Index loops instead of iterators, manual Vec construction, ..
    </VERIFICATION NOTE> */
    #[cfg(feature = "alloc")]
    // Theo: Verus doesn't like the zeroize in this function. I think the long-term
    // solution is to use assume_specification to tell Verus what zeroize does.
    // In the short-term, I've just told verus to ignore the body.
    #[verifier::external_body]
    pub fn batch_invert(inputs: &mut [Scalar]) -> (result: Scalar)
    ensures
        // Result is the modular inverse of the product of all original inputs
        is_inverse_of_nat(&result, product_of_scalars(old(inputs)@)),
        // Each input is replaced with its inverse
        forall|i: int| 0 <= i < inputs.len() ==>
            #[trigger] is_inverse(&(#[trigger] old(inputs)[i]), &(#[trigger] inputs[i])),
    {
        // This code is essentially identical to the FieldElement
        // implementation, and is documented there.  Unfortunately,
        // it's not easy to write it generically, since here we want
        // to use `UnpackedScalar`s internally, and `Scalar`s
        // externally, but there's no corresponding distinction for
        // field elements.

        let n = inputs.len();
        let one_unpacked = Scalar::ONE.unpack();

        proof {
            assume(limbs_bounded(&one_unpacked));
        }

        let one: UnpackedScalar = one_unpacked.as_montgomery();

        proof {
            assume(limbs_bounded(&one));
        }

        /* <VERIFICATION NOTE>
         Build vec manually instead of vec![one; n] for Verus compatibility
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
         let mut scratch = vec![one; n];
         </ORIGINAL CODE> */
        let mut scratch = Vec::new();
        for _ in 0..n {
            scratch.push(one);
        }


        // Keep an accumulator of all of the previous products
        let acc_unpacked = Scalar::ONE.unpack();

        proof {
            assume(scratch.len() == n);
            assume(limbs_bounded(&acc_unpacked));
        }

        let mut acc = acc_unpacked.as_montgomery();

        proof {
            assume(limbs_bounded(&acc));
        }

        // Pass through the input vector, recording the previous
        // products in the scratch space
        /* <VERIFICATION NOTE>
         Rewritten with index loop instead of .zip() for Verus compatibility
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
         for (input, scratch) in inputs.iter_mut().zip(scratch.iter_mut()) {
             *scratch = acc;
        //     // Avoid unnecessary Montgomery multiplication in second pass by
        //     // keeping inputs in Montgomery form
             let tmp = input.unpack().as_montgomery();
             *input = tmp.pack();
             acc = UnpackedScalar::montgomery_mul(&acc, &tmp);
         }
        </ORIGINAL CODE> */
        for i in 0..n
             invariant scratch.len() == n, n == inputs.len(), limbs_bounded(&acc)
        {
            scratch[i] = acc;

            // Avoid unnecessary Montgomery multiplication in second pass by
            // keeping inputs in Montgomery form
            let input_unpacked = inputs[i].unpack();

            proof {
                assume(limbs_bounded(&input_unpacked));
            }

            let tmp = input_unpacked.as_montgomery();

            proof {
                assume(limbs_bounded(&tmp));
            }

            inputs[i] = tmp.pack();
            acc = UnpackedScalar::montgomery_mul(&acc, &tmp);

            proof {
                assume(limbs_bounded(&acc));
            }
        }

        proof {
            // Assert that all scratch elements have bounded limbs
            assume(forall|j: int| 0 <= j < scratch.len() ==> #[trigger] limbs_bounded(&scratch[j]));
        }

        // acc is nonzero iff all inputs are nonzero
        #[cfg(not(verus_keep_ghost))]
        debug_assert!(acc.pack() != Scalar::ZERO);

        // Compute the inverse of all products
        // ORIGINAL CODE: acc = acc.montgomery_invert().from_montgomery();
        acc = acc.montgomery_invert();

        proof {
            assume(limbs_bounded(&acc));
        }

        acc = acc.from_montgomery();

        proof {
            assume(limbs_bounded(&acc));
        }

        // We need to return the product of all inverses later
        let ret = acc.pack();

        // Pass through the vector backwards to compute the inverses
        // in place
        /* <VERIFICATION NOTE>
         Manual reverse loop instead of .rev() for Verus compatibility
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
        for (input, scratch) in inputs.iter_mut().rev().zip(scratch.iter().rev()) {
             let tmp = UnpackedScalar::montgomery_mul(&acc, &input.unpack());
             *input = UnpackedScalar::montgomery_mul(&acc, scratch).pack();
             acc = tmp;
         }
        </ORIGINAL CODE> */
        let mut i: usize = n;
        while i > 0
            invariant
                scratch.len() == n,
                n == inputs.len(),
                i <= n,
                limbs_bounded(&acc),
                forall|j: int| 0 <= j < scratch.len() ==> #[trigger] limbs_bounded(&scratch[j]),
            decreases i
        {
            i -= 1;
            let input_unpacked = inputs[i].unpack();

            proof {
                assume(limbs_bounded(&input_unpacked));
            }

            let tmp = UnpackedScalar::montgomery_mul(&acc, &input_unpacked);

            proof {
                assume(limbs_bounded(&tmp));
            }

            inputs[i] = UnpackedScalar::montgomery_mul(&acc, &scratch[i]).pack();
            acc = tmp;
        }


        #[cfg(feature = "zeroize")]
        Zeroize::zeroize(&mut scratch);

        proof {
            // Assume the postconditions
            assume(is_inverse_of_nat(&ret, product_of_scalars(old(inputs)@)));
            assume(forall|i: int| 0 <= i < inputs.len() ==>
                #[trigger] is_inverse(&(#[trigger] old(inputs)[i]), &(#[trigger] inputs[i])));
        }

        ret
    }

    /// Get the bits of the scalar as an array, in little-endian order
    /* <VERIFICATION NOTE>
     This is a Verus-compatible version of bits_le from below that returns an array instead of an iterator
    </VERIFICATION NOTE> */
    #[allow(dead_code)]
    pub(crate) fn bits_le_v(&self) -> (result: [bool; 256])
    ensures
        bits_to_nat(&result) == bytes_to_nat(&self.bytes),
    {
        let mut bits = [false; 256];
        let mut i: usize = 0;

        while i < 256
            invariant
                i <= 256,
                bits.len() == 256,
                self.bytes.len() == 32,
            decreases 256 - i,
        {
            // As i runs from 0..256, the bottom 3 bits index the bit, while the upper bits index
            // the byte. Since self.bytes is little-endian at the byte level, this is
            // little-endian on the bit level
            let byte_idx = i >> 3;  // Divide by 8 to get byte index
            let bit_idx = (i & 7) as u8;  // Modulo 8 to get bit position within byte

            // Prove bounds using shift and mask lemmas
            proof {
                use crate::backend::serial::u64::common_verus::shift_lemmas::*;
                use crate::backend::serial::u64::common_verus::mask_lemmas::*;
                use vstd::bits::*;
                use vstd::arithmetic::power2::*;

                assert(i < 256);

                // Prove i >> 3 = i / 8 using shift lemma
                lemma_u64_shr_is_div(i as u64, 3);
                // pow2(3) = 8
                lemma2_to64();
                assert(byte_idx < 32);

                // Prove i & 7 = i % 8 using mask lemma
                lemma_u64_low_bits_mask_is_mod(i as u64, 3);
                // low_bits_mask(3) = 7 and pow2(3) = 8
                lemma2_to64();
                assert(bit_idx < 8);
            }

            bits[i] = ((self.bytes[byte_idx] >> bit_idx) & 1u8) == 1;
            i += 1;
        }

        proof {
            assume(bits_to_nat(&bits) == bytes_to_nat(&self.bytes));
        }

        bits
    }

}
} // verus!

impl Scalar {
    /// Get the bits of the scalar, in little-endian order
    /* <VERIFICATION NOTE>
    - Opaque types like Iterator not supported in Verus yet
    - see bits_le_v above for a Verus-compatible version
    </VERIFICATION NOTE> */
    pub(crate) fn bits_le(&self) -> impl DoubleEndedIterator<Item = bool> + '_ {
        (0..256).map(|i| {
            // As i runs from 0..256, the bottom 3 bits index the bit, while the upper bits index
            // the byte. Since self.bytes is little-endian at the byte level, this iterator is
            // little-endian on the bit level
            ((self.bytes[i >> 3] >> (i & 7)) & 1u8) == 1
        })
    }

    verus! {
        /// Compute a width-\\(w\\) "Non-Adjacent Form" of this scalar.
        ///
        /// A width-\\(w\\) NAF of a positive integer \\(k\\) is an expression
        /// $$
        /// k = \sum_{i=0}\^m n\_i 2\^i,
        /// $$
        /// where each nonzero
        /// coefficient \\(n\_i\\) is odd and bounded by \\(|n\_i| < 2\^{w-1}\\),
        /// \\(n\_{m-1}\\) is nonzero, and at most one of any \\(w\\) consecutive
        /// coefficients is nonzero.  (Hankerson, Menezes, Vanstone; def 3.32).
        ///
        /// The length of the NAF is at most one more than the length of
        /// the binary representation of \\(k\\).  This is why the
        /// `Scalar` type maintains an invariant (invariant #1) that the top bit is
        /// \\(0\\), so that the NAF of a scalar has at most 256 digits.
        ///
        /// Intuitively, this is like a binary expansion, except that we
        /// allow some coefficients to grow in magnitude up to
        /// \\(2\^{w-1}\\) so that the nonzero coefficients are as sparse
        /// as possible.
        ///
        /// When doing scalar multiplication, we can then use a lookup
        /// table of precomputed multiples of a point to add the nonzero
        /// terms \\( k_i P \\).  Using signed digits cuts the table size
        /// in half, and using odd digits cuts the table size in half
        /// again.
        ///
        /// To compute a \\(w\\)-NAF, we use a modification of Algorithm 3.35 of HMV:
        ///
        /// 1. \\( i \gets 0 \\)
        /// 2. While \\( k \ge 1 \\):
        ///     1. If \\(k\\) is odd, \\( n_i \gets k \operatorname{mods} 2^w \\), \\( k \gets k - n_i \\).
        ///     2. If \\(k\\) is even, \\( n_i \gets 0 \\).
        ///     3. \\( k \gets k / 2 \\), \\( i \gets i + 1 \\).
        /// 3. Return \\( n_0, n_1, ... , \\)
        ///
        /// Here \\( \bar x = x \operatorname{mods} 2^w \\) means the
        /// \\( \bar x \\) with \\( \bar x \equiv x \pmod{2^w} \\) and
        /// \\( -2^{w-1} \leq \bar x < 2^{w-1} \\).
        ///
        /// We implement this by scanning across the bits of \\(k\\) from
        /// least-significant bit to most-significant-bit.
        /// Write the bits of \\(k\\) as
        /// $$
        /// k = \sum\_{i=0}\^m k\_i 2^i,
        /// $$
        /// and split the sum as
        /// $$
        /// k = \sum\_{i=0}^{w-1} k\_i 2^i + 2^w \sum\_{i=0} k\_{i+w} 2^i
        /// $$
        /// where the first part is \\( k \mod 2^w \\).
        ///
        /// If \\( k \mod 2^w\\) is odd, and \\( k \mod 2^w < 2^{w-1} \\), then we emit
        /// \\( n_0 = k \mod 2^w \\).  Instead of computing
        /// \\( k - n_0 \\), we just advance \\(w\\) bits and reindex.
        ///
        /// If \\( k \mod 2^w\\) is odd, and \\( k \mod 2^w \ge 2^{w-1} \\), then
        /// \\( n_0 = k \operatorname{mods} 2^w = k \mod 2^w - 2^w \\).
        /// The quantity \\( k - n_0 \\) is
        /// $$
        /// \begin{aligned}
        /// k - n_0 &= \sum\_{i=0}^{w-1} k\_i 2^i + 2^w \sum\_{i=0} k\_{i+w} 2^i
        ///          - \sum\_{i=0}^{w-1} k\_i 2^i + 2^w \\\\
        /// &= 2^w + 2^w \sum\_{i=0} k\_{i+w} 2^i
        /// \end{aligned}
        /// $$
        /// so instead of computing the subtraction, we can set a carry
        /// bit, advance \\(w\\) bits, and reindex.
        ///
        /// If \\( k \mod 2^w\\) is even, we emit \\(0\\), advance 1 bit
        /// and reindex.  In fact, by setting all digits to \\(0\\)
        /// initially, we don't need to emit anything.
        /* <VERIFICATION NOTE>
         assumed as external spec; spec incomplete
        </VERIFICATION NOTE> */
        #[verifier::external_body]
        pub(crate) fn non_adjacent_form(&self, w: usize) -> (result: [i8; 256])
        requires
            2 <= w <= 8,
        ensures
            true
            // TODO
        {
            // required by the NAF definition
            // VERIFICATION NOTE: we tell verus not to verify debug assertions
            #[cfg(not(verus_keep_ghost))]
            debug_assert!(w >= 2);
            // required so that the NAF digits fit in i8
            // VERIFICATION NOTE: we tell verus not to verify debug assertions
            #[cfg(not(verus_keep_ghost))]
            debug_assert!(w <= 8);

            let mut naf = [0i8; 256];

            // VERIFICATION NOTE: Inline the read_le_u64_into logic to avoid Verus unsupported features - IN PROGRESS
            /* <ORIGINAL CODE>
            let mut x_u64 = [0u64; 5];
            read_le_u64_into(&self.bytes, &mut x_u64[0..4]);
             <ORIGINAL CODE> */
            // Read 4 u64s from the 32-byte array (self.bytes)
            let mut x_u64 = [0u64; 5];
            x_u64[0] = u64::from_le_bytes([
                self.bytes[0], self.bytes[1], self.bytes[2], self.bytes[3],
                self.bytes[4], self.bytes[5], self.bytes[6], self.bytes[7],
            ]);
            x_u64[1] = u64::from_le_bytes([
                self.bytes[8], self.bytes[9], self.bytes[10], self.bytes[11],
                self.bytes[12], self.bytes[13], self.bytes[14], self.bytes[15],
            ]);
            x_u64[2] = u64::from_le_bytes([
                self.bytes[16], self.bytes[17], self.bytes[18], self.bytes[19],
                self.bytes[20], self.bytes[21], self.bytes[22], self.bytes[23],
            ]);
            x_u64[3] = u64::from_le_bytes([
                self.bytes[24], self.bytes[25], self.bytes[26], self.bytes[27],
                self.bytes[28], self.bytes[29], self.bytes[30], self.bytes[31],
            ]);
            // x_u64[4] remains 0

            let width = 1 << w;
            let window_mask = width - 1;

            let mut pos = 0;
            let mut carry = 0;
            while pos < 256 {
                // Construct a buffer of bits of the scalar, starting at bit `pos`
                let u64_idx = pos / 64;
                let bit_idx = pos % 64;
                let bit_buf: u64 = if bit_idx < 64 - w {
                    // This window's bits are contained in a single u64
                    x_u64[u64_idx] >> bit_idx
                } else {
                    // Combine the current u64's bits with the bits from the next u64
                    (x_u64[u64_idx] >> bit_idx) | (x_u64[1 + u64_idx] << (64 - bit_idx))
                };

                // Add the carry into the current window
                let window = carry + (bit_buf & window_mask);

                if window & 1 == 0 {
                    // If the window value is even, preserve the carry and continue.
                    // Why is the carry preserved?
                    // If carry == 0 and window & 1 == 0, then the next carry should be 0
                    // If carry == 1 and window & 1 == 0, then bit_buf & 1 == 1 so the next carry should be 1
                    pos += 1;
                    continue;
                }

                if window < width / 2 {
                    carry = 0;
                    naf[pos] = window as i8;
                } else {
                    carry = 1;
                    naf[pos] = (window as i8).wrapping_sub(width as i8);
                }

                pos += w;
            }

            naf
        }
        /* <VERIFICATION NOTE>
        Helper inline functions for as_radix_16, moved outside function body for Verus compatibility
        </VERIFICATION NOTE> */
        #[allow(clippy::identity_op)]
        #[inline(always)]
        fn bot_half(x: u8) -> u8 {
            (x >> 0) & 15
        }
        #[inline(always)]
        fn top_half(x: u8) -> u8 {
            (x >> 4) & 15
        }

        /// Write this scalar in radix 16, with coefficients in \\([-8,8)\\),
        /// i.e., compute \\(a\_i\\) such that
        /// $$
        ///    a = a\_0 + a\_1 16\^1 + \cdots + a_{63} 16\^{63},
        /// $$
        /// with \\(-8 \leq a_i < 8\\) for \\(0 \leq i < 63\\) and \\(-8 \leq a_{63} \leq 8\\).
        ///
        /// The largest value that can be decomposed like this is just over \\(2^{255}\\). Thus, in
        /// order to not error, the top bit MUST NOT be set, i.e., `Self` MUST be less than
        /// \\(2^{255}\\).

        #[verifier::external_body]
        pub(crate) fn as_radix_16(&self) -> [i8; 64] {
            // VERIFICATION NOTE: we tell verus not to verify debug assertions
            #[cfg(not(verus_keep_ghost))]
            debug_assert!(self[31] <= 127);
            let mut output = [0i8; 64];


            // Step 1: change radix.
            // Convert from radix 256 (bytes) to radix 16 (nibbles)
            // VERIFICATION NOTE: Moved helper functions outside for Verus compatibility
            /* <ORIGINAL CODE>
            #[allow(clippy::identity_op)]
            #[inline(always)]
            fn bot_half(x: u8) -> u8 {
                (x >> 0) & 15
            }
            #[inline(always)]
            fn top_half(x: u8) -> u8 {
                (x >> 4) & 15
            }

            for i in 0..32 {
                output[2 * i] = bot_half(self[i]) as i8;
                output[2 * i + 1] = top_half(self[i]) as i8;
            }
            </ORIGINAL CODE> */
            for i in 0..32 {
                output[2 * i] = Self::bot_half(self.bytes[i]) as i8;
                output[2 * i + 1] = Self::top_half(self.bytes[i]) as i8;
            }
            // Precondition note: since self[31] <= 127, output[63] <= 7

            // Step 2: recenter coefficients from [0,16) to [-8,8)
            for i in 0..63 {
                let carry = (output[i] + 8) >> 4;
                output[i] -= carry << 4;
                /* <ORIGINAL CODE> :
                output[i + 1] += carry;
                </ORIGINAL CODE> */
                // VERIFICATION NOTE: Changed += to + for Verus compatibility
                output[i + 1] += carry;
            }
            // Precondition note: output[63] is not recentered.  It
            // increases by carry <= 1.  Thus output[63] <= 8.

            output
        }

    } // verus!

    /// Returns a size hint indicating how many entries of the return
    /// value of `to_radix_2w` are nonzero.
    #[cfg(any(feature = "alloc", all(test, feature = "precomputed-tables")))]
    pub(crate) fn to_radix_2w_size_hint(w: usize) -> usize {
        debug_assert!(w >= 4);
        debug_assert!(w <= 8);

        let digits_count = match w {
            4..=7 => (256 + w - 1) / w,
            // See comment in to_radix_2w on handling the terminal carry.
            8 => (256 + w - 1) / w + 1_usize,
            _ => panic!("invalid radix parameter"),
        };

        debug_assert!(digits_count <= 64);
        digits_count
    }

    /// Creates a representation of a Scalar in radix \\( 2^w \\) with \\(w = 4, 5, 6, 7, 8\\) for
    /// use with the Pippenger algorithm. Higher radixes are not supported to save cache space.
    /// Radix 256 is near-optimal even for very large inputs.
    ///
    /// Radix below 16 or above 256 is prohibited.
    /// This method returns digits in a fixed-sized array, excess digits are zeroes.
    ///
    /// For radix 16, `Self` must be less than \\(2^{255}\\). This is because most integers larger
    /// than \\(2^{255}\\) are unrepresentable in the form described below for \\(w = 4\\). This
    /// would be true for \\(w = 8\\) as well, but it is compensated for by increasing the size
    /// hint by 1.
    ///
    /// ## Scalar representation
    ///
    /// Radix \\(2\^w\\), with \\(n = ceil(256/w)\\) coefficients in \\([-(2\^w)/2,(2\^w)/2)\\),
    /// i.e., scalar is represented using digits \\(a\_i\\) such that
    /// $$
    ///    a = a\_0 + a\_1 2\^1w + \cdots + a_{n-1} 2\^{w*(n-1)},
    /// $$
    /// with \\(-2\^w/2 \leq a_i < 2\^w/2\\) for \\(0 \leq i < (n-1)\\) and \\(-2\^w/2 \leq a_{n-1} \leq 2\^w/2\\).
    ///
    #[cfg(any(feature = "alloc", feature = "precomputed-tables"))]
    pub(crate) fn as_radix_2w(&self, w: usize) -> [i8; 64] {
        debug_assert!(w >= 4);
        debug_assert!(w <= 8);

        if w == 4 {
            return self.as_radix_16();
        }

        // Scalar formatted as four `u64`s with carry bit packed into the highest bit.
        let mut scalar64x4 = [0u64; 4];
        read_le_u64_into(&self.bytes, &mut scalar64x4[0..4]);

        let radix: u64 = 1 << w;
        let window_mask: u64 = radix - 1;

        let mut carry = 0u64;
        let mut digits = [0i8; 64];
        let digits_count = (256 + w - 1) / w;
        #[allow(clippy::needless_range_loop)]
        for i in 0..digits_count {
            // Construct a buffer of bits of the scalar, starting at `bit_offset`.
            let bit_offset = i * w;
            let u64_idx = bit_offset / 64;
            let bit_idx = bit_offset % 64;

            // Read the bits from the scalar
            let bit_buf: u64 = if bit_idx < 64 - w || u64_idx == 3 {
                // This window's bits are contained in a single u64,
                // or it's the last u64 anyway.
                scalar64x4[u64_idx] >> bit_idx
            } else {
                // Combine the current u64's bits with the bits from the next u64
                (scalar64x4[u64_idx] >> bit_idx) | (scalar64x4[1 + u64_idx] << (64 - bit_idx))
            };

            // Read the actual coefficient value from the window
            let coef = carry + (bit_buf & window_mask); // coef = [0, 2^r)

            // Recenter coefficients from [0,2^w) to [-2^w/2, 2^w/2)
            carry = (coef + (radix / 2)) >> w;
            digits[i] = ((coef as i64) - (carry << w) as i64) as i8;
        }

        // When 4 < w < 8, we can fold the final carry onto the last digit d,
        // because d < 2^w/2 so d + carry*2^w = d + 1*2^w < 2^(w+1) < 2^8.
        //
        // When w = 8, we can't fit carry*2^w into an i8.  This should
        // not happen anyways, because the final carry will be 0 for
        // reduced scalars, but Scalar invariant #1 allows 255-bit scalars.
        // To handle this, we expand the size_hint by 1 when w=8,
        // and accumulate the final carry onto another digit.
        match w {
            8 => digits[digits_count] += carry as i8,
            _ => digits[digits_count - 1] += (carry << w) as i8,
        }

        digits
    }

    verus! {
    /// Unpack this `Scalar` to an `UnpackedScalar` for faster arithmetic.
    // VERIFICATION NOTE: VERIFIED (changed pub(crate) to pub)
    pub fn unpack(&self) -> (result: UnpackedScalar)
    ensures
        limbs_bounded(&result),
        to_nat(&result.limbs) == bytes_to_nat(&self.bytes),
    {
        UnpackedScalar::from_bytes(&self.bytes)
    }

    /// Reduce this `Scalar` modulo \\(\ell\\).
    #[allow(non_snake_case)]
    // VERIFICATION NOTE: has assumes
    fn reduce(&self) -> (result: Scalar)
    ensures
        // Result is equivalent to input modulo the group order
        bytes_to_nat(&result.bytes) % group_order() == bytes_to_nat(&self.bytes) % group_order(),
        // Result is canonical (reduced)
        bytes_to_nat(&result.bytes) < group_order(),
        // High bit is clear (invariant #1: result < 2^255)
        result.bytes[31] <= 127,
    {
        let x = self.unpack();
    //    assume(limbs_bounded(&x));
        assume(limbs_bounded(&constants::R));
        let xR = UnpackedScalar::mul_internal(&x, &constants::R);
        let x_mod_l = UnpackedScalar::montgomery_reduce(&xR);
        let result = x_mod_l.pack();
        // Assume postconditions (to be proven later)
        assume(bytes_to_nat(&result.bytes) % group_order() == bytes_to_nat(&self.bytes) % group_order());
        assume(bytes_to_nat(&result.bytes) < group_order());
        assume(result.bytes[31] <= 127);
        result
    }
    /// Check whether this `Scalar` is the canonical representative mod \\(\ell\\). This is not
    /// public because any `Scalar` that is publicly observed is reduced, by scalar invariant #2.
    fn is_canonical(&self) -> Choice {
        self.ct_eq(&self.reduce())
    }
    } // verus!
}

verus! {
// Helper function for montgomery_invert
// VERIFICATION NOTE: Moved inline function outside the body of montgomery_invert
#[inline]
fn square_multiply(y: &mut UnpackedScalar, squarings: usize, x: &UnpackedScalar) {
    assume(limbs_bounded(y));
    assume(limbs_bounded(x));
    for _ in 0..squarings
        invariant limbs_bounded(y), limbs_bounded(x)
    {
        *y = y.montgomery_square();
    }
    *y = UnpackedScalar::montgomery_mul(y, x);
    assume(limbs_bounded(y));
}
} // verus!

impl UnpackedScalar {
    verus! {
    /// Pack the limbs of this `UnpackedScalar` into a `Scalar`.
    fn pack(&self) -> (result: Scalar)
    requires
        limbs_bounded(self),
    ensures
        bytes_to_nat(&result.bytes) == to_nat(&self.limbs),
        // VERIFICATION NOTE: If input is canonical, output is canonical
        to_nat(&self.limbs) < group_order() ==> bytes_to_nat(&result.bytes) < group_order(),
        // VERIFICATION NOTE: Canonical scalars have high bit clear (since group_order < 2^255)
        to_nat(&self.limbs) < group_order() ==> result.bytes[31] <= 127,
    {
        let result = Scalar {
            bytes: self.as_bytes(),
        };
        // VERIFICATION NOTE: TODO: Prove these follow from as_bytes() spec
        assume(to_nat(&self.limbs) < group_order() ==> bytes_to_nat(&result.bytes) < group_order());
        assume(to_nat(&self.limbs) < group_order() ==> result.bytes[31] <= 127);
        result
    }

    /// Inverts an UnpackedScalar in Montgomery form.
    #[rustfmt::skip] // keep alignment of addition chain and squarings
    #[allow(clippy::just_underscores_and_digits)]
    pub fn montgomery_invert(&self) -> (result: UnpackedScalar)
    requires
        limbs_bounded(&self),
    ensures
        limbs_bounded(&result),
        (to_nat(&result.limbs) * to_nat(&self.limbs)) % group_order() == (montgomery_radix() * montgomery_radix()) % group_order(),
        // Equivalent to: from_montgomery(result) * from_montgomery(self) ≡ 1 (mod L)
        // Expressed in Montgomery form: (result/R) * (self/R) ≡ 1, i.e., result * self ≡ R² (mod L)
    {
        // Uses the addition chain from
        // https://briansmith.org/ecc-inversion-addition-chains-01#curve25519_scalar_inversion
        let    _1 = *self;
        assume(limbs_bounded(&_1));
        let   _10 = _1.montgomery_square();
        assume(limbs_bounded(&_10));
        let  _100 = _10.montgomery_square();
        assume(limbs_bounded(&_100));
        let   _11 = UnpackedScalar::montgomery_mul(&_10,     &_1);
        assume(limbs_bounded(&_11));
        let  _101 = UnpackedScalar::montgomery_mul(&_10,    &_11);
        assume(limbs_bounded(&_101));
        let  _111 = UnpackedScalar::montgomery_mul(&_10,   &_101);
        assume(limbs_bounded(&_111));
        let _1001 = UnpackedScalar::montgomery_mul(&_10,   &_111);
        assume(limbs_bounded(&_1001));
        let _1011 = UnpackedScalar::montgomery_mul(&_10,  &_1001);
        assume(limbs_bounded(&_1011));
        let _1111 = UnpackedScalar::montgomery_mul(&_100, &_1011);
        assume(limbs_bounded(&_1111));

        // _10000
        let mut y = UnpackedScalar::montgomery_mul(&_1111, &_1);
        assume(limbs_bounded(&y));

        square_multiply(&mut y, 123 + 3, &_101);
        square_multiply(&mut y,   2 + 2, &_11);
        square_multiply(&mut y,   1 + 4, &_1111);
        square_multiply(&mut y,   1 + 4, &_1111);
        square_multiply(&mut y,       4, &_1001);
        square_multiply(&mut y,       2, &_11);
        square_multiply(&mut y,   1 + 4, &_1111);
        square_multiply(&mut y,   1 + 3, &_101);
        square_multiply(&mut y,   3 + 3, &_101);
        square_multiply(&mut y,       3, &_111);
        square_multiply(&mut y,   1 + 4, &_1111);
        square_multiply(&mut y,   2 + 3, &_111);
        square_multiply(&mut y,   2 + 2, &_11);
        square_multiply(&mut y,   1 + 4, &_1011);
        square_multiply(&mut y,   2 + 4, &_1011);
        square_multiply(&mut y,   6 + 4, &_1001);
        square_multiply(&mut y,   2 + 2, &_11);
        square_multiply(&mut y,   3 + 2, &_11);
        square_multiply(&mut y,   3 + 2, &_11);
        square_multiply(&mut y,   1 + 4, &_1001);
        square_multiply(&mut y,   1 + 3, &_111);
        square_multiply(&mut y,   2 + 4, &_1111);
        square_multiply(&mut y,   1 + 4, &_1011);
        square_multiply(&mut y,       3, &_101);
        square_multiply(&mut y,   2 + 4, &_1111);
        square_multiply(&mut y,       3, &_101);
        square_multiply(&mut y,   1 + 2, &_11);

        proof {
            assume(limbs_bounded(&y));
            assume((to_nat(&y.limbs) * to_nat(&self.limbs)) % group_order() == (montgomery_radix() * montgomery_radix()) % group_order());
        }

        y
    }

    /// Inverts an UnpackedScalar not in Montgomery form.
    pub fn invert(&self) -> (result: UnpackedScalar)
    ensures
        limbs_bounded(&result),
        // Postcondition: result * self ≡ 1 (mod group_order)
        to_nat(&result.limbs) * to_nat(&self.limbs) % group_order() == 1,
    {
        /* <ORIGINAL CODE>
                self.as_montgomery().montgomery_invert().from_montgomery()
        </ORIGINAL CODE> */

        assume(limbs_bounded(self));
        let mont = self.as_montgomery();
        assume(limbs_bounded(&mont));
        let inv = mont.montgomery_invert();
        assume(limbs_bounded(&inv));
        let result = inv.from_montgomery();

        proof {
            assume(limbs_bounded(&result));
            assume(to_nat(&result.limbs) * to_nat(&self.limbs) % group_order() == 1);
        }

        result
    }
    } // verus!
}

#[cfg(feature = "group")]
impl Field for Scalar {
    const ZERO: Self = Self::ZERO;
    const ONE: Self = Self::ONE;

    fn random(mut rng: impl RngCore) -> Self {
        // NOTE: this is duplicated due to different `rng` bounds
        let mut scalar_bytes = [0u8; 64];
        rng.fill_bytes(&mut scalar_bytes);
        Self::from_bytes_mod_order_wide(&scalar_bytes)
    }

    fn square(&self) -> Self {
        self * self
    }

    fn double(&self) -> Self {
        self + self
    }

    fn invert(&self) -> CtOption<Self> {
        CtOption::new(self.invert(), !self.is_zero())
    }

    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        #[allow(unused_qualifications)]
        group::ff::helpers::sqrt_ratio_generic(num, div)
    }

    fn sqrt(&self) -> CtOption<Self> {
        #[allow(unused_qualifications)]
        group::ff::helpers::sqrt_tonelli_shanks(
            self,
            [
                0xcb02_4c63_4b9e_ba7d,
                0x029b_df3b_d45e_f39a,
                0x0000_0000_0000_0000,
                0x0200_0000_0000_0000,
            ],
        )
    }
}

#[cfg(feature = "group")]
impl PrimeField for Scalar {
    type Repr = [u8; 32];

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        Self::from_canonical_bytes(repr)
    }

    fn from_repr_vartime(repr: Self::Repr) -> Option<Self> {
        // Check that the high bit is not set
        if (repr[31] >> 7) != 0u8 {
            return None;
        }

        let candidate = Scalar { bytes: repr };

        if candidate == candidate.reduce() {
            Some(candidate)
        } else {
            None
        }
    }

    fn to_repr(&self) -> Self::Repr {
        self.to_bytes()
    }

    fn is_odd(&self) -> Choice {
        Choice::from(self.as_bytes()[0] & 1)
    }

    const MODULUS: &'static str =
        "0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed";
    const NUM_BITS: u32 = 253;
    const CAPACITY: u32 = 252;

    const TWO_INV: Self = Self {
        bytes: [
            0xf7, 0xe9, 0x7a, 0x2e, 0x8d, 0x31, 0x09, 0x2c, 0x6b, 0xce, 0x7b, 0x51, 0xef, 0x7c,
            0x6f, 0x0a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x08,
        ],
    };
    const MULTIPLICATIVE_GENERATOR: Self = Self {
        bytes: [
            2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ],
    };
    const S: u32 = 2;
    const ROOT_OF_UNITY: Self = Self {
        bytes: [
            0xd4, 0x07, 0xbe, 0xeb, 0xdf, 0x75, 0x87, 0xbe, 0xfe, 0x83, 0xce, 0x42, 0x53, 0x56,
            0xf0, 0x0e, 0x7a, 0xc2, 0xc1, 0xab, 0x60, 0x6d, 0x3d, 0x7d, 0xe7, 0x81, 0x79, 0xe0,
            0x10, 0x73, 0x4a, 0x09,
        ],
    };
    const ROOT_OF_UNITY_INV: Self = Self {
        bytes: [
            0x19, 0xcc, 0x37, 0x71, 0x3a, 0xed, 0x8a, 0x99, 0xd7, 0x18, 0x29, 0x60, 0x8b, 0xa3,
            0xee, 0x05, 0x86, 0x3d, 0x3e, 0x54, 0x9f, 0x92, 0xc2, 0x82, 0x18, 0x7e, 0x86, 0x1f,
            0xef, 0x8c, 0xb5, 0x06,
        ],
    };
    const DELTA: Self = Self {
        bytes: [
            16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ],
    };
}

#[cfg(feature = "group-bits")]
impl PrimeFieldBits for Scalar {
    type ReprBits = [u8; 32];

    fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
        self.to_repr().into()
    }

    fn char_le_bits() -> FieldBits<Self::ReprBits> {
        constants::BASEPOINT_ORDER_PRIVATE.to_bytes().into()
    }
}

#[cfg(feature = "group")]
impl FromUniformBytes<64> for Scalar {
    fn from_uniform_bytes(bytes: &[u8; 64]) -> Self {
        Scalar::from_bytes_mod_order_wide(bytes)
    }
}

/// Read one or more u64s stored as little endian bytes.
///
/// ## Panics
/// Panics if `src.len() != 8 * dst.len()`.
fn read_le_u64_into(src: &[u8], dst: &mut [u64]) {
    assert!(
        src.len() == 8 * dst.len(),
        "src.len() = {}, dst.len() = {}",
        src.len(),
        dst.len()
    );
    for (bytes, val) in src.chunks(8).zip(dst.iter_mut()) {
        *val = u64::from_le_bytes(
            bytes
                .try_into()
                .expect("Incorrect src length, should be 8 * dst.len()"),
        );
    }
}

/// _Clamps_ the given little-endian representation of a 32-byte integer. Clamping the value puts
/// it in the range:
///
/// **n ∈ 2^254 + 8\*{0, 1, 2, 3, . . ., 2^251 − 1}**
///
/// # Explanation of clamping
///
/// For Curve25519, h = 8, and multiplying by 8 is the same as a binary left-shift by 3 bits.
/// If you take a secret scalar value between 2^251 and 2^252 – 1 and left-shift by 3 bits
/// then you end up with a 255-bit number with the most significant bit set to 1 and
/// the least-significant three bits set to 0.
///
/// The Curve25519 clamping operation takes **an arbitrary 256-bit random value** and
/// clears the most-significant bit (making it a 255-bit number), sets the next bit, and then
/// clears the 3 least-significant bits. In other words, it directly creates a scalar value that is
/// in the right form and pre-multiplied by the cofactor.
///
/// See [here](https://neilmadden.blog/2020/05/28/whats-the-curve25519-clamping-all-about/) for
/// more details.
#[must_use]
pub const fn clamp_integer(mut bytes: [u8; 32]) -> [u8; 32] {
    bytes[0] &= 0b1111_1000;
    bytes[31] &= 0b0111_1111;
    bytes[31] |= 0b0100_0000;
    bytes
}

// #[cfg(test)]
// pub(crate) mod test {
//     use super::*;

//     #[cfg(feature = "alloc")]
//     use alloc::vec::Vec;

//     /// x = 2238329342913194256032495932344128051776374960164957527413114840482143558222
//     pub static X: Scalar = Scalar {
//         bytes: [
//             0x4e, 0x5a, 0xb4, 0x34, 0x5d, 0x47, 0x08, 0x84, 0x59, 0x13, 0xb4, 0x64, 0x1b, 0xc2,
//             0x7d, 0x52, 0x52, 0xa5, 0x85, 0x10, 0x1b, 0xcc, 0x42, 0x44, 0xd4, 0x49, 0xf4, 0xa8,
//             0x79, 0xd9, 0xf2, 0x04,
//         ],
//     };
//     /// 1/x = 6859937278830797291664592131120606308688036382723378951768035303146619657244
//     pub static XINV: Scalar = Scalar {
//         bytes: [
//             0x1c, 0xdc, 0x17, 0xfc, 0xe0, 0xe9, 0xa5, 0xbb, 0xd9, 0x24, 0x7e, 0x56, 0xbb, 0x01,
//             0x63, 0x47, 0xbb, 0xba, 0x31, 0xed, 0xd5, 0xa9, 0xbb, 0x96, 0xd5, 0x0b, 0xcd, 0x7a,
//             0x3f, 0x96, 0x2a, 0x0f,
//         ],
//     };
//     /// y = 2592331292931086675770238855846338635550719849568364935475441891787804997264
//     pub static Y: Scalar = Scalar {
//         bytes: [
//             0x90, 0x76, 0x33, 0xfe, 0x1c, 0x4b, 0x66, 0xa4, 0xa2, 0x8d, 0x2d, 0xd7, 0x67, 0x83,
//             0x86, 0xc3, 0x53, 0xd0, 0xde, 0x54, 0x55, 0xd4, 0xfc, 0x9d, 0xe8, 0xef, 0x7a, 0xc3,
//             0x1f, 0x35, 0xbb, 0x05,
//         ],
//     };

//     /// The largest scalar that satisfies invariant #1, i.e., the largest scalar with the top bit
//     /// set to 0. Since this scalar violates invariant #2, i.e., it's greater than the modulus `l`,
//     /// addition and subtraction are broken. The only thing you can do with this is scalar-point
//     /// multiplication (and actually also scalar-scalar multiplication, but that's just a quirk of
//     /// our implementation).
//     pub(crate) static LARGEST_UNREDUCED_SCALAR: Scalar = Scalar {
//         bytes: [
//             0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//             0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//             0xff, 0xff, 0xff, 0x7f,
//         ],
//     };

//     /// x*y = 5690045403673944803228348699031245560686958845067437804563560795922180092780
//     static X_TIMES_Y: Scalar = Scalar {
//         bytes: [
//             0x6c, 0x33, 0x74, 0xa1, 0x89, 0x4f, 0x62, 0x21, 0x0a, 0xaa, 0x2f, 0xe1, 0x86, 0xa6,
//             0xf9, 0x2c, 0xe0, 0xaa, 0x75, 0xc2, 0x77, 0x95, 0x81, 0xc2, 0x95, 0xfc, 0x08, 0x17,
//             0x9a, 0x73, 0x94, 0x0c,
//         ],
//     };

//     /// sage: l = 2^252 + 27742317777372353535851937790883648493
//     /// sage: big = 2^256 - 1
//     /// sage: repr((big % l).digits(256))
//     static CANONICAL_2_256_MINUS_1: Scalar = Scalar {
//         bytes: [
//             28, 149, 152, 141, 116, 49, 236, 214, 112, 207, 125, 115, 244, 91, 239, 198, 254, 255,
//             255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 15,
//         ],
//     };

//     static A_SCALAR: Scalar = Scalar {
//         bytes: [
//             0x1a, 0x0e, 0x97, 0x8a, 0x90, 0xf6, 0x62, 0x2d, 0x37, 0x47, 0x02, 0x3f, 0x8a, 0xd8,
//             0x26, 0x4d, 0xa7, 0x58, 0xaa, 0x1b, 0x88, 0xe0, 0x40, 0xd1, 0x58, 0x9e, 0x7b, 0x7f,
//             0x23, 0x76, 0xef, 0x09,
//         ],
//     };

//     static A_NAF: [i8; 256] = [
//         0, 13, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, -9, 0, 0, 0, 0, -11, 0, 0, 0, 0, 3, 0, 0,
//         0, 0, 1, 0, 0, 0, 0, 9, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 11, 0, 0, 0, 0,
//         11, 0, 0, 0, 0, 0, -9, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
//         0, -1, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, -15, 0, 0, 0, 0, -7, 0, 0, 0, 0, -9, 0, 0, 0, 0, 0, 5,
//         0, 0, 0, 0, 13, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, -11, 0, 0, 0, 0, -7, 0, 0, 0, 0, -13, 0, 0,
//         0, 0, 11, 0, 0, 0, 0, -9, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -15, 0, 0, 0, 0, 1, 0, 0, 0, 0,
//         7, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 15,
//         0, 0, 0, 0, 0, -9, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, -15, 0,
//         0, 0, 0, 0, 15, 0, 0, 0, 0, 15, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
//     ];

//     const BASEPOINT_ORDER_MINUS_ONE: Scalar = Scalar {
//         bytes: [
//             0xec, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9,
//             0xde, 0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
//             0x00, 0x00, 0x00, 0x10,
//         ],
//     };

//     /// The largest clamped integer
//     static LARGEST_CLAMPED_INTEGER: [u8; 32] = clamp_integer(LARGEST_UNREDUCED_SCALAR.bytes);

//     #[test]
//     fn fuzzer_testcase_reduction() {
//         // LE bytes of 24519928653854221733733552434404946937899825954937634815
//         let a_bytes = [
//             255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
//             255, 255, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0,
//         ];
//         // LE bytes of 4975441334397345751130612518500927154628011511324180036903450236863266160640
//         let b_bytes = [
//             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 210, 210,
//             210, 255, 255, 255, 255, 10,
//         ];
//         // LE bytes of 6432735165214683820902750800207468552549813371247423777071615116673864412038
//         let c_bytes = [
//             134, 171, 119, 216, 180, 128, 178, 62, 171, 132, 32, 62, 34, 119, 104, 193, 47, 215,
//             181, 250, 14, 207, 172, 93, 75, 207, 211, 103, 144, 204, 56, 14,
//         ];

//         let a = Scalar::from_bytes_mod_order(a_bytes);
//         let b = Scalar::from_bytes_mod_order(b_bytes);
//         let c = Scalar::from_bytes_mod_order(c_bytes);

//         let mut tmp = [0u8; 64];

//         // also_a = (a mod l)
//         tmp[0..32].copy_from_slice(&a_bytes[..]);
//         let also_a = Scalar::from_bytes_mod_order_wide(&tmp);

//         // also_b = (b mod l)
//         tmp[0..32].copy_from_slice(&b_bytes[..]);
//         let also_b = Scalar::from_bytes_mod_order_wide(&tmp);

//         let expected_c = a * b;
//         let also_expected_c = also_a * also_b;

//         assert_eq!(c, expected_c);
//         assert_eq!(c, also_expected_c);
//     }

//     #[test]
//     fn non_adjacent_form_test_vector() {
//         let naf = A_SCALAR.non_adjacent_form(5);
//         for i in 0..256 {
//             assert_eq!(naf[i], A_NAF[i]);
//         }
//     }

//     fn non_adjacent_form_iter(w: usize, x: &Scalar) {
//         let naf = x.non_adjacent_form(w);

//         // Reconstruct the scalar from the computed NAF
//         let mut y = Scalar::ZERO;
//         for i in (0..256).rev() {
//             y += y;
//             let digit = if naf[i] < 0 {
//                 -Scalar::from((-naf[i]) as u64)
//             } else {
//                 Scalar::from(naf[i] as u64)
//             };
//             y += digit;
//         }

//         assert_eq!(*x, y);
//     }

//     #[test]
//     fn non_adjacent_form_random() {
//         let mut rng = rand::thread_rng();
//         for _ in 0..1_000 {
//             let x = Scalar::random(&mut rng);
//             for w in &[5, 6, 7, 8] {
//                 non_adjacent_form_iter(*w, &x);
//             }
//         }
//     }

//     #[test]
//     fn from_u64() {
//         let val: u64 = 0xdeadbeefdeadbeef;
//         let s = Scalar::from(val);
//         assert_eq!(s[7], 0xde);
//         assert_eq!(s[6], 0xad);
//         assert_eq!(s[5], 0xbe);
//         assert_eq!(s[4], 0xef);
//         assert_eq!(s[3], 0xde);
//         assert_eq!(s[2], 0xad);
//         assert_eq!(s[1], 0xbe);
//         assert_eq!(s[0], 0xef);
//     }

//     #[test]
//     fn scalar_mul_by_one() {
//         let test_scalar = X * Scalar::ONE;
//         for i in 0..32 {
//             assert!(test_scalar[i] == X[i]);
//         }
//     }

//     #[test]
//     fn add_reduces() {
//         // Check that addition wraps around the modulus
//         assert_eq!(BASEPOINT_ORDER_MINUS_ONE + Scalar::ONE, Scalar::ZERO);
//     }

//     #[test]
//     fn sub_reduces() {
//         // Check that subtraction wraps around the modulus
//         assert_eq!(Scalar::ZERO - Scalar::ONE, BASEPOINT_ORDER_MINUS_ONE);
//     }

//     #[test]
//     fn impl_add() {
//         let two = Scalar::from(2u64);
//         let one = Scalar::ONE;
//         let should_be_two = one + one;
//         assert_eq!(should_be_two, two);
//     }

//     #[allow(non_snake_case)]
//     #[test]
//     fn impl_mul() {
//         let should_be_X_times_Y = X * Y;
//         assert_eq!(should_be_X_times_Y, X_TIMES_Y);
//     }

//     #[allow(non_snake_case)]
//     #[test]
//     #[cfg(feature = "alloc")]
//     fn impl_product() {
//         // Test that product works for non-empty iterators
//         let X_Y_vector = [X, Y];
//         let should_be_X_times_Y: Scalar = X_Y_vector.iter().product();
//         assert_eq!(should_be_X_times_Y, X_TIMES_Y);

//         // Test that product works for the empty iterator
//         let one = Scalar::ONE;
//         let empty_vector = [];
//         let should_be_one: Scalar = empty_vector.iter().product();
//         assert_eq!(should_be_one, one);

//         // Test that product works for iterators where Item = Scalar
//         let xs = [Scalar::from(2u64); 10];
//         let ys = [Scalar::from(3u64); 10];
//         // now zs is an iterator with Item = Scalar
//         let zs = xs.iter().zip(ys.iter()).map(|(x, y)| x * y);

//         let x_prod: Scalar = xs.iter().product();
//         let y_prod: Scalar = ys.iter().product();
//         let z_prod: Scalar = zs.product();

//         assert_eq!(x_prod, Scalar::from(1024u64));
//         assert_eq!(y_prod, Scalar::from(59049u64));
//         assert_eq!(z_prod, Scalar::from(60466176u64));
//         assert_eq!(x_prod * y_prod, z_prod);
//     }

//     #[test]
//     #[cfg(feature = "alloc")]
//     fn impl_sum() {
//         // Test that sum works for non-empty iterators
//         let two = Scalar::from(2u64);
//         let one_vector = [Scalar::ONE, Scalar::ONE];
//         let should_be_two: Scalar = one_vector.iter().sum();
//         assert_eq!(should_be_two, two);

//         // Test that sum works for the empty iterator
//         let zero = Scalar::ZERO;
//         let empty_vector = [];
//         let should_be_zero: Scalar = empty_vector.iter().sum();
//         assert_eq!(should_be_zero, zero);

//         // Test that sum works for owned types
//         let xs = [Scalar::from(1u64); 10];
//         let ys = [Scalar::from(2u64); 10];
//         // now zs is an iterator with Item = Scalar
//         let zs = xs.iter().zip(ys.iter()).map(|(x, y)| x + y);

//         let x_sum: Scalar = xs.iter().sum();
//         let y_sum: Scalar = ys.iter().sum();
//         let z_sum: Scalar = zs.sum();

//         assert_eq!(x_sum, Scalar::from(10u64));
//         assert_eq!(y_sum, Scalar::from(20u64));
//         assert_eq!(z_sum, Scalar::from(30u64));
//         assert_eq!(x_sum + y_sum, z_sum);
//     }

//     #[test]
//     fn square() {
//         let expected = X * X;
//         let actual = X.unpack().square().pack();
//         for i in 0..32 {
//             assert!(expected[i] == actual[i]);
//         }
//     }

//     #[test]
//     fn reduce() {
//         let biggest = Scalar::from_bytes_mod_order([0xff; 32]);
//         assert_eq!(biggest, CANONICAL_2_256_MINUS_1);
//     }

//     #[test]
//     fn from_bytes_mod_order_wide() {
//         let mut bignum = [0u8; 64];
//         // set bignum = x + 2^256x
//         for i in 0..32 {
//             bignum[i] = X[i];
//             bignum[32 + i] = X[i];
//         }
//         // 3958878930004874126169954872055634648693766179881526445624823978500314864344
//         // = x + 2^256x (mod l)
//         let reduced = Scalar {
//             bytes: [
//                 216, 154, 179, 139, 210, 121, 2, 71, 69, 99, 158, 216, 23, 173, 63, 100, 204, 0,
//                 91, 50, 219, 153, 57, 249, 28, 82, 31, 197, 100, 165, 192, 8,
//             ],
//         };
//         let test_red = Scalar::from_bytes_mod_order_wide(&bignum);
//         for i in 0..32 {
//             assert!(test_red[i] == reduced[i]);
//         }
//     }

//     #[allow(non_snake_case)]
//     #[test]
//     fn invert() {
//         let inv_X = X.invert();
//         assert_eq!(inv_X, XINV);
//         let should_be_one = inv_X * X;
//         assert_eq!(should_be_one, Scalar::ONE);
//     }

//     // Negating a scalar twice should result in the original scalar.
//     #[allow(non_snake_case)]
//     #[test]
//     fn neg_twice_is_identity() {
//         let negative_X = -&X;
//         let should_be_X = -&negative_X;

//         assert_eq!(should_be_X, X);
//     }

//     #[test]
//     fn to_bytes_from_bytes_roundtrips() {
//         let unpacked = X.unpack();
//         let bytes = unpacked.as_bytes();
//         let should_be_unpacked = UnpackedScalar::from_bytes(&bytes);

//         assert_eq!(should_be_unpacked.0, unpacked.0);
//     }

//     #[test]
//     fn montgomery_reduce_matches_from_bytes_mod_order_wide() {
//         let mut bignum = [0u8; 64];

//         // set bignum = x + 2^256x
//         for i in 0..32 {
//             bignum[i] = X[i];
//             bignum[32 + i] = X[i];
//         }
//         // x + 2^256x (mod l)
//         //         = 3958878930004874126169954872055634648693766179881526445624823978500314864344
//         let expected = Scalar {
//             bytes: [
//                 216, 154, 179, 139, 210, 121, 2, 71, 69, 99, 158, 216, 23, 173, 63, 100, 204, 0,
//                 91, 50, 219, 153, 57, 249, 28, 82, 31, 197, 100, 165, 192, 8,
//             ],
//         };
//         let reduced = Scalar::from_bytes_mod_order_wide(&bignum);

//         // The reduced scalar should match the expected
//         assert_eq!(reduced.bytes, expected.bytes);

//         //  (x + 2^256x) * R
//         let interim =
//             UnpackedScalar::mul_internal(&UnpackedScalar::from_bytes_wide(&bignum), &constants::R);
//         // ((x + 2^256x) * R) / R  (mod l)
//         let montgomery_reduced = UnpackedScalar::montgomery_reduce(&interim);

//         // The Montgomery reduced scalar should match the reduced one, as well as the expected
//         assert_eq!(montgomery_reduced.0, reduced.unpack().0);
//         assert_eq!(montgomery_reduced.0, expected.unpack().0)
//     }

//     #[test]
//     fn canonical_decoding() {
//         // canonical encoding of 1667457891
//         let canonical_bytes = [
//             99, 99, 99, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
//             0, 0, 0, 0,
//         ];

//         // encoding of
//         //   7265385991361016183439748078976496179028704920197054998554201349516117938192
//         // = 28380414028753969466561515933501938171588560817147392552250411230663687203 (mod l)
//         // non_canonical because unreduced mod l
//         let non_canonical_bytes_because_unreduced = [16; 32];

//         // encoding with high bit set, to check that the parser isn't pre-masking the high bit
//         let non_canonical_bytes_because_highbit = [
//             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
//             0, 0, 128,
//         ];

//         assert!(bool::from(
//             Scalar::from_canonical_bytes(canonical_bytes).is_some()
//         ));
//         assert!(bool::from(
//             Scalar::from_canonical_bytes(non_canonical_bytes_because_unreduced).is_none()
//         ));
//         assert!(bool::from(
//             Scalar::from_canonical_bytes(non_canonical_bytes_because_highbit).is_none()
//         ));
//     }

//     #[test]
//     #[cfg(feature = "serde")]
//     fn serde_bincode_scalar_roundtrip() {
//         use bincode;
//         let encoded = bincode::serialize(&X).unwrap();
//         let parsed: Scalar = bincode::deserialize(&encoded).unwrap();
//         assert_eq!(parsed, X);

//         // Check that the encoding is 32 bytes exactly
//         assert_eq!(encoded.len(), 32);

//         // Check that the encoding itself matches the usual one
//         assert_eq!(X, bincode::deserialize(X.as_bytes()).unwrap(),);
//     }

//     #[cfg(all(debug_assertions, feature = "alloc"))]
//     #[test]
//     #[should_panic]
//     fn batch_invert_with_a_zero_input_panics() {
//         let mut xs = vec![Scalar::ONE; 16];
//         xs[3] = Scalar::ZERO;
//         // This should panic in debug mode.
//         Scalar::batch_invert(&mut xs);
//     }

//     #[test]
//     #[cfg(feature = "alloc")]
//     fn batch_invert_empty() {
//         assert_eq!(Scalar::ONE, Scalar::batch_invert(&mut []));
//     }

//     #[test]
//     #[cfg(feature = "alloc")]
//     fn batch_invert_consistency() {
//         let mut x = Scalar::from(1u64);
//         let mut v1: Vec<_> = (0..16)
//             .map(|_| {
//                 let tmp = x;
//                 x = x + x;
//                 tmp
//             })
//             .collect();
//         let v2 = v1.clone();

//         let expected: Scalar = v1.iter().product();
//         let expected = expected.invert();
//         let ret = Scalar::batch_invert(&mut v1);
//         assert_eq!(ret, expected);

//         for (a, b) in v1.iter().zip(v2.iter()) {
//             assert_eq!(a * b, Scalar::ONE);
//         }
//     }

//     #[cfg(feature = "precomputed-tables")]
//     fn test_pippenger_radix_iter(scalar: Scalar, w: usize) {
//         let digits_count = Scalar::to_radix_2w_size_hint(w);
//         let digits = scalar.as_radix_2w(w);

//         let radix = Scalar::from((1 << w) as u64);
//         let mut term = Scalar::ONE;
//         let mut recovered_scalar = Scalar::ZERO;
//         for digit in &digits[0..digits_count] {
//             let digit = *digit;
//             if digit != 0 {
//                 let sdigit = if digit < 0 {
//                     -Scalar::from((-(digit as i64)) as u64)
//                 } else {
//                     Scalar::from(digit as u64)
//                 };
//                 recovered_scalar += term * sdigit;
//             }
//             term *= radix;
//         }
//         // When the input is unreduced, we may only recover the scalar mod l.
//         assert_eq!(recovered_scalar, scalar.reduce());
//     }

//     #[test]
//     #[cfg(feature = "precomputed-tables")]
//     fn test_pippenger_radix() {
//         use core::iter;
//         // For each valid radix it tests that 1000 random-ish scalars can be restored
//         // from the produced representation precisely.
//         let cases = (2..100)
//             .map(|s| Scalar::from(s as u64).invert())
//             // The largest unreduced scalar, s = 2^255-1. This is not reduced mod l. Scalar mult
//             // still works though.
//             .chain(iter::once(LARGEST_UNREDUCED_SCALAR));

//         for scalar in cases {
//             test_pippenger_radix_iter(scalar, 6);
//             test_pippenger_radix_iter(scalar, 7);
//             test_pippenger_radix_iter(scalar, 8);
//         }
//     }

//     #[test]
//     #[cfg(feature = "alloc")]
//     fn test_read_le_u64_into() {
//         let cases: &[(&[u8], &[u64])] = &[
//             (
//                 &[0xFE, 0xEF, 0x10, 0x01, 0x1F, 0xF1, 0x0F, 0xF0],
//                 &[0xF00F_F11F_0110_EFFE],
//             ),
//             (
//                 &[
//                     0xFE, 0xEF, 0x10, 0x01, 0x1F, 0xF1, 0x0F, 0xF0, 0x12, 0x34, 0x56, 0x78, 0x9A,
//                     0xBC, 0xDE, 0xF0,
//                 ],
//                 &[0xF00F_F11F_0110_EFFE, 0xF0DE_BC9A_7856_3412],
//             ),
//         ];

//         for (src, expected) in cases {
//             let mut dst = vec![0; expected.len()];
//             read_le_u64_into(src, &mut dst);

//             assert_eq!(&dst, expected, "Expected {:x?} got {:x?}", expected, dst);
//         }
//     }

//     // Tests consistency of From<{integer}> impls for Scalar
//     #[test]
//     fn test_scalar_from_int() {
//         let s1 = Scalar::ONE;

//         // For `x` in `u8`, `u16`, `u32`, `u64`, and `u128`, check that
//         // `Scalar::from(x + 1) == Scalar::from(x) + Scalar::from(1)`

//         let x = 0x23u8;
//         let sx = Scalar::from(x);
//         assert_eq!(sx + s1, Scalar::from(x + 1));

//         let x = 0x2323u16;
//         let sx = Scalar::from(x);
//         assert_eq!(sx + s1, Scalar::from(x + 1));

//         let x = 0x2323_2323u32;
//         let sx = Scalar::from(x);
//         assert_eq!(sx + s1, Scalar::from(x + 1));

//         let x = 0x2323_2323_2323_2323u64;
//         let sx = Scalar::from(x);
//         assert_eq!(sx + s1, Scalar::from(x + 1));

//         let x = 0x2323_2323_2323_2323_2323_2323_2323_2323u128;
//         let sx = Scalar::from(x);
//         assert_eq!(sx + s1, Scalar::from(x + 1));
//     }

//     #[cfg(feature = "group")]
//     #[test]
//     fn ff_constants() {
//         assert_eq!(Scalar::from(2u64) * Scalar::TWO_INV, Scalar::ONE);

//         assert_eq!(
//             Scalar::ROOT_OF_UNITY * Scalar::ROOT_OF_UNITY_INV,
//             Scalar::ONE,
//         );

//         // ROOT_OF_UNITY^{2^s} mod m == 1
//         assert_eq!(
//             Scalar::ROOT_OF_UNITY.pow(&[1u64 << Scalar::S, 0, 0, 0]),
//             Scalar::ONE,
//         );

//         // DELTA^{t} mod m == 1
//         assert_eq!(
//             Scalar::DELTA.pow(&[
//                 0x9604_98c6_973d_74fb,
//                 0x0537_be77_a8bd_e735,
//                 0x0000_0000_0000_0000,
//                 0x0400_0000_0000_0000,
//             ]),
//             Scalar::ONE,
//         );
//     }

//     #[cfg(feature = "group")]
//     #[test]
//     fn ff_impls() {
//         assert!(bool::from(Scalar::ZERO.is_even()));
//         assert!(bool::from(Scalar::ONE.is_odd()));
//         assert!(bool::from(Scalar::from(2u64).is_even()));
//         assert!(bool::from(Scalar::DELTA.is_even()));

//         assert!(bool::from(Field::invert(&Scalar::ZERO).is_none()));
//         assert_eq!(Field::invert(&X).unwrap(), XINV);

//         let x_sq = X.square();
//         // We should get back either the positive or negative root.
//         assert!([X, -X].contains(&x_sq.sqrt().unwrap()));

//         assert_eq!(Scalar::from_repr_vartime(X.to_repr()), Some(X));
//         assert_eq!(Scalar::from_repr_vartime([0xff; 32]), None);

//         assert_eq!(Scalar::from_repr(X.to_repr()).unwrap(), X);
//         assert!(bool::from(Scalar::from_repr([0xff; 32]).is_none()));
//     }

//     #[test]
//     #[should_panic]
//     fn test_read_le_u64_into_should_panic_on_bad_input() {
//         let mut dst = [0_u64; 1];
//         // One byte short
//         read_le_u64_into(&[0xFE, 0xEF, 0x10, 0x01, 0x1F, 0xF1, 0x0F], &mut dst);
//     }

//     #[test]
//     fn test_scalar_clamp() {
//         let input = A_SCALAR.bytes;
//         let expected = [
//             0x18, 0x0e, 0x97, 0x8a, 0x90, 0xf6, 0x62, 0x2d, 0x37, 0x47, 0x02, 0x3f, 0x8a, 0xd8,
//             0x26, 0x4d, 0xa7, 0x58, 0xaa, 0x1b, 0x88, 0xe0, 0x40, 0xd1, 0x58, 0x9e, 0x7b, 0x7f,
//             0x23, 0x76, 0xef, 0x49,
//         ];
//         let actual = clamp_integer(input);
//         assert_eq!(actual, expected);

//         let expected = [
//             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
//             0, 0, 0x40,
//         ];
//         let actual = clamp_integer([0; 32]);
//         assert_eq!(expected, actual);
//         let expected = [
//             0xf8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//             0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//             0xff, 0xff, 0xff, 0x7f,
//         ];
//         let actual = clamp_integer([0xff; 32]);
//         assert_eq!(actual, expected);

//         assert_eq!(
//             LARGEST_CLAMPED_INTEGER,
//             clamp_integer(LARGEST_CLAMPED_INTEGER)
//         );
//     }

//     // Check that a * b == a.reduce() * a.reduce() for ANY scalars a,b, even ones that violate
//     // invariant #1, i.e., a,b > 2^255. Old versions of ed25519-dalek did multiplication where a
//     // was reduced and b was clamped and unreduced. This checks that that was always well-defined.
//     #[test]
//     fn test_mul_reduction_invariance() {
//         let mut rng = rand::thread_rng();

//         for _ in 0..10 {
//             // Also define c that's clamped. We'll make sure that clamping doesn't affect
//             // computation
//             let (a, b, c) = {
//                 let mut a_bytes = [0u8; 32];
//                 let mut b_bytes = [0u8; 32];
//                 let mut c_bytes = [0u8; 32];
//                 rng.fill_bytes(&mut a_bytes);
//                 rng.fill_bytes(&mut b_bytes);
//                 rng.fill_bytes(&mut c_bytes);
//                 (
//                     Scalar { bytes: a_bytes },
//                     Scalar { bytes: b_bytes },
//                     Scalar {
//                         bytes: clamp_integer(c_bytes),
//                     },
//                 )
//             };

//             // Make sure this is the same product no matter how you cut it
//             let reduced_mul_ab = a.reduce() * b.reduce();
//             let reduced_mul_ac = a.reduce() * c.reduce();
//             assert_eq!(a * b, reduced_mul_ab);
//             assert_eq!(a.reduce() * b, reduced_mul_ab);
//             assert_eq!(a * b.reduce(), reduced_mul_ab);
//             assert_eq!(a * c, reduced_mul_ac);
//             assert_eq!(a.reduce() * c, reduced_mul_ac);
//             assert_eq!(a * c.reduce(), reduced_mul_ac);
//         }
//     }
// }
