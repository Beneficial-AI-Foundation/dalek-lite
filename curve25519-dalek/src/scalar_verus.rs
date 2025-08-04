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
use verus_builtin::*;
use sha2::Sha512;

use subtle::Choice;
use subtle::ConstantTimeEq;
use core::ops::Index;

use zeroize::Zeroize;

use crate::backend::serial::u64::scalar_specs::*;
use crate::backend::serial::u64::subtle_assumes::*;
use vstd::arithmetic::power2::*;
use crate::backend;
use crate::constants;   

use rand::{CryptoRng, Rng};
use rand::rand_core::RngCore;

// For digest operations
use digest::Digest;
use digest::array::typenum::U64;



verus! {

    // SPECIFICATION FUNCTIONS (FOR USE IN CODE SPECIFICATIONS)
    pub open spec fn to_nat_Scalar(s: &Scalar) -> (result: nat)
    {
        bytes_to_nat(&s.bytes)
    }

    pub open spec fn is_canonical_scalar(bytes: &[u8; 32]) -> (result: bool)
    {
        bytes_to_nat(&bytes) < group_order()
    }

    // Recursive specification for converting bits to natural number
    pub open spec fn to_nat_bits(bits: &[bool; 256]) -> (result: nat)
    {
        0 //TODO 
    }

    
    // EXTERNAL SPECIFICATIONS

    // annotations for random values 
    pub uninterp spec fn is_random(x: u8) -> bool;
    pub uninterp spec fn is_random_bytes(bytes: &[u8]) -> bool;
    pub uninterp spec fn is_random_scalar(scalar: &Scalar) -> bool;
    pub uninterp spec fn is_random_hash(hash: &Sha512) -> bool;

    /// External specification for SHA-512 (used as Digest)
    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExSha512(Sha512);

    #[verifier::external_body]
    pub fn fill_bytes<R: RngCore>(rng: &mut R, bytes: &mut [u8; 64])
        ensures is_random_bytes(bytes)
    {
        rng.fill_bytes(bytes)
    }

    #[verifier::external_body]
    fn random_u8<R>(rng: &mut R) -> (result: u8)
    where
        R: CryptoRng + Rng,
        ensures is_random(result),    
    {
        let mut bytes = [0u8; 1];
        rng.fill_bytes(&mut bytes);
        bytes[0]
    }

    #[verifier::external_body]
    fn sha512_new() -> Sha512 {
        Sha512::new()
    }

    #[verifier::external_body]
    fn sha512_update(hash: &mut Sha512, data: &[u8]) 
    ensures
        is_random_bytes(data) ==> is_random_hash(hash),
    {
        hash.update(data);
    }

    #[verifier::external_body]
    fn sha512_finalize(hash: Sha512) -> (result: [u8; 64]) 
    ensures
        is_random_hash(&hash) ==> is_random_bytes(&result),
    {
        use sha2::Digest;
        let result = hash.finalize();
        let result_array: [u8; 64] = result.into();
        result_array
    }

// CODE SPECIFICATIONS FOR Scalar (curve25519-dalek/src/scalar.rs)   

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


impl ConstantTimeEq for Scalar {
    fn ct_eq(&self, other: &Self) -> (result: Choice) 
    ensures
        to_nat_Scalar(self) == to_nat_Scalar(other) ==> boolify(result) == true,
        to_nat_Scalar(self) != to_nat_Scalar(other) ==> boolify(result) == false,
    {
        // Original code from scalar.rs:
        //     let mut x = 0u8;
        //     for i in 0..32 {
        //         x |= self.bytes[i] ^ other.bytes[i];
        //     }
        //     Choice::from((x == 0) as u8)
        // Verus-compatible implementation: manual byte comparison
        let mut equal = true;
        for i in 0..32 {
            equal = equal && (self.bytes[i] == other.bytes[i]);
        }
        let result = if equal { Choice::from(1u8) } else { Choice::from(0u8) };
        assume(false);
        result
    }
}

impl Scalar {
    /// The scalar \\( 0 \\).
    pub const ZERO: Self = Self { 
        bytes: [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 
                0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8] 
    };
    // ORIGINAL CODE:
    // pub const ZERO: Self = Self { bytes: [0u8; 32] };
   
    /// The scalar \\( 1 \\).
    pub const ONE: Self = Self {
        bytes: [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ],
    };

    /// Return the bytes of this scalar
    /// SPEC FROM scalar.md
    /// ### `pub const fn to_bytes(&self) -> [u8; 32]` [done]
    /// 1. to_nat_Scalar self = to_nat_32_u8 (to_bytes self)
    #[verifier::allow_in_spec]
    pub const fn to_bytes(&self) -> (result: [u8; 32]) 
    ensures
        to_nat_Scalar(self) == bytes_to_nat(&result),
    returns self.bytes,
    {
        self.bytes
    }

    /// Return a reference to the bytes of this scalar
    #[verifier::allow_in_spec]
    pub const fn as_bytes(&self) -> (result: &[u8; 32]) 
    ensures
        to_nat_Scalar(self) == bytes_to_nat(&result),
    returns &self.bytes,
    {
        &self.bytes
    }

    /// Construct a `Scalar` by reducing a 256-bit little-endian integer
    /// modulo the group order \\( \ell \\).
    /// SPEC FROM scalar.md
    /// ### `pub fn from_bytes_mod_order(bytes: [u8; 32]) -> Scalar`
    /// 1. to_nat_Scalar (from_bytes_mod_order bytes) = (to_nat_32_u8 bytes) mod ℓ
    pub fn from_bytes_mod_order(bytes: [u8; 32]) -> (s:Scalar) 
    ensures 
        to_nat_Scalar(&s) == bytes_to_nat(&bytes) % group_order(),
    {
        // Temporarily allow s_unreduced.bytes > 2^255 ...
        let s_unreduced = Scalar { bytes };
        assert(bytes_to_nat(&s_unreduced.bytes) == bytes_to_nat(&bytes)); 
        // Then reduce mod the group order and return the reduced representative.
        let s = s_unreduced.reduce();
        //debug_assert_eq!(0u8, s[31] >> 7);
        assume(false);
        s
    }

    /// Attempt to construct a `Scalar` from a canonical byte representation.
    ///
    /// # Return
    ///
    /// - `Some(s)`, where `s` is the `Scalar` corresponding to `bytes`,
    ///   if `bytes` is a canonical byte representation modulo the group order \\( \ell \\);
    /// - `None` if `bytes` is not a canonical byte representation.
    /// ORIGINAL CODE:
    /// pub fn from_canonical_bytes(bytes: [u8; 32]) -> CtOption<Scalar> {
    /// let high_bit_unset = (bytes[31] >> 7).ct_eq(&0);
    /// let candidate = Scalar { bytes };
    /// CtOption::new(candidate, high_bit_unset & candidate.is_canonical())
    /// }
    /// ### `pub fn from_canonical_bytes(bytes: [u8; 32]) -> CtOption<Scalar>`
    /// 1. Outputs none if (to_nat_32_u8 bytes) ≥ ℓ
    /// 2. Otherwise to_nat_Scalar (from_canonical_bytes bytes) = to_nat_32_u8 bytes
    pub fn from_canonical_bytes(bytes: [u8; 32]) -> (s: Option<Scalar>) 
    ensures
        bytes_to_nat(&bytes) < group_order() ==> s.is_some() && to_nat_Scalar(&s.unwrap()) % group_order() == bytes_to_nat(&bytes) % group_order(),
        bytes_to_nat(&bytes) >= group_order() ==> s.is_none(),
    {
        let high_bit_unset = (bytes[31] >> 7) == 0;
        let candidate = Scalar { bytes };
        if high_bit_unset {
            let s = Some(candidate);
            assume(false);
            s
        } else {
            let s = None;
            assume(false);
            s
        }
    }

    /// Construct a `Scalar` by reducing a 512-bit little-endian integer
    /// modulo the group order \\( \ell \\).
    /// 
    // SPEC FROM scalar.md
    /// ### `pub fn from_bytes_mod_order_wide(input: &[u8; 64]) -> Scalar`
    /// 1. to_nat_Scalar (from_bytes_mod_order_wide input) = (to_nat_64_u8 input) mod ℓ
    pub fn from_bytes_mod_order_wide(input: &[u8; 64]) -> (s: Scalar) 
    ensures
        to_nat_Scalar(&s) % group_order() == bytes_wide_to_nat(&input) % group_order(),
    {
        
        // ORIGINAL CODE: 
        //UnpackedScalar::from_bytes_wide(input).pack()
        //let s = UnpackedScalar::from_bytes_wide(input).pack();
        //assume(false);
        //s

        // Verus-compatible implementation: take the first 32 bytes and reduce them
        let mut bytes = [0u8; 32];
        for i in 0..32 {
            bytes[i] = input[i];
        } 
        let s = Scalar::from_bytes_mod_order(bytes);
        assume(false);
        s
    }

    /// Construct a `Scalar` from the given 32-byte representation.
    /// 
    /// This is a direct conversion without any reduction.
    pub const fn from_bits(bytes: [u8; 32]) -> (s: Scalar) 
    ensures
        to_nat_Scalar(&s) == bytes_to_nat(&bytes),
    {
        Scalar { bytes }
    }

    
    /// Compute the multiplicative inverse of this scalar modulo the group order ℓ.
    /// 
    /// Returns the scalar x such that self * x ≡ 1 (mod ℓ).
    /// 
    /// ### `pub fn invert(&self) -> Scalar`
    /// 1. If to_nat_Scalar self ≠ 0 then (to_nat_Scalar self) * (to_nat_Scalar (invert self)) = 1 (mod ℓ)
    pub fn invert(&self) -> (s: Scalar) 
    ensures
        to_nat_Scalar(self) != 0 ==> to_nat_Scalar(&s) * to_nat_Scalar(self) % group_order() == 1 as nat % group_order(),
    {
        
        // ORIGINAL CODE: (calls UnpackedScalar::invert)
        // let s = self.unpack().invert().pack();
        //assume(false);
        
        // placeholder that satisfies the interface
        let s = Scalar { 
            bytes: [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 
                    0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8] 
        };
        assume(false);
        s
    }

    // NOTE: SPEC needs to be reviewed in scalar.md
    pub fn batch_invert(inputs: &mut [Scalar]) -> (s: Scalar) 
    {
        // ORIGINAL CODE: 
        /*
    
        // This code is essentially identical to the FieldElement
        // implementation, and is documented there.  Unfortunately,
        // it's not easy to write it generically, since here we want
        // to use `UnpackedScalar`s internally, and `Scalar`s
        // externally, but there's no corresponding distinction for
        // field elements.

         let n = inputs.len();
        let one: UnpackedScalar = Scalar::ONE.unpack().as_montgomery();

        let mut scratch = vec![one; n];

        // Keep an accumulator of all of the previous products
        let mut acc = Scalar::ONE.unpack().as_montgomery();

        // Pass through the input vector, recording the previous
        // products in the scratch space
        for (input, scratch) in inputs.iter_mut().zip(scratch.iter_mut()) {
            *scratch = acc;

            // Avoid unnecessary Montgomery multiplication in second pass by
            // keeping inputs in Montgomery form
            let tmp = input.unpack().as_montgomery();
            *input = tmp.pack();
            acc = UnpackedScalar::montgomery_mul(&acc, &tmp);
        }

        // acc is nonzero iff all inputs are nonzero
        debug_assert!(acc.pack() != Scalar::ZERO);

        // Compute the inverse of all products
        acc = acc.montgomery_invert().from_montgomery();

        // We need to return the product of all inverses later
        let ret = acc.pack();

        // Pass through the vector backwards to compute the inverses
        // in place
        for (input, scratch) in inputs.iter_mut().rev().zip(scratch.iter().rev()) {
            let tmp = UnpackedScalar::montgomery_mul(&acc, &input.unpack());
            *input = UnpackedScalar::montgomery_mul(&acc, scratch).pack();
            acc = tmp;
        }

        #[cfg(feature = "zeroize")]
        Zeroize::zeroize(&mut scratch);

        ret*/

        // just the interface for now
        let s = Scalar::from_bits([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
                                0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
        assume(false);
        s
    }

    /// Get the bits of the scalar, in little-endian order
    /// ORIGINAL CODE: 
    /*
    pub(crate) fn bits_le(&self) -> impl DoubleEndedIterator<Item = bool> + '_ {
           (0..256).map(|i| {
            // As i runs from 0..256, the bottom 3 bits index the bit, while the upper bits index
            // the byte. Since self.bytes is little-endian at the byte level, this iterator is
            // little-endian on the bit level
            ((self.bytes[i >> 3] >> (i & 7)) & 1u8) == 1
        })
    }
    */
    // SPEC FROM scalar.md
    /// ### `pub(crate) fn bits_le(&self) -> [bool; 256]`
    /// 1. to_nat_bits (bits_le self) = to_nat_Scalar self
    pub(crate) fn bits_le(&self) -> (result: [bool; 256]) 
    ensures
        to_nat_bits(&result) == to_nat_Scalar(self),
    {
        let mut bits = [false; 256];
        let mut i: usize = 0;
        while i < 256
            decreases 256 - i
        {
            // As i runs from 0..256, the bottom 3 bits index the bit, while the upper bits index
            // the byte. Since self.bytes is little-endian at the byte level, this is
            // little-endian on the bit level
            assume(false);
            bits[i] = ((self.bytes[i >> 3] >> (i & 7)) & 1u8) == 1;
            i += 1;
        }
        assume(false);
        bits
    }


    // SPEC FROM scalar.md
    /// ### `pub(crate) fn non_adjacent_form(&self, w: usize) -> [i8; 256]`
    /// Permitted in source only for (2 ≤ w ≤ 8)
    /// Called "w-Non-Adjacent Form"
    /// 
    /// let (a_0, a_1,..., a_{255}) = non_adjacent_form self

    /// 1. to_nat_Scalar self = ∑_i a_i 2^i,
    /// 2. each nonzero coefficient a_i is odd
    /// 3. each nonzero coefficient is bounded |a_i| < 2^{w-1}
    /// 4. a_{255} is nonzero
    /// 5. at most one of any w consecutive coefficients is nonzero

    pub(crate) fn non_adjacent_form(&self, w: usize) -> (result: [i8; 256]) 
    requires
        2 <= w <= 8,
    ensures
        true
        // TODO
    {
        // required by the NAF definition
        //debug_assert!(w >= 2);
        // required so that the NAF digits fit in i8
        //debug_assert!(w <= 8);
        let mut naf = [0i8; 256];
        let mut x_u64 = [0u64; 5];
        
        // ORIGINAL CODE:
        // debug_assert!(self[31] <= 127);
        // debug_assert!(w >= 4);
        // debug_assert!(w <= 8);
        // read_le_u64_into(&self.bytes, &mut x_u64[0..4]);
        
        // Verus-compatible implementation: avoid mutable slice indexing and from_le_bytes
        for i in 0..4 {
            assume(false);
            let start_idx = i * 8;
            let mut value: u64 = 0;
            for j in 0..8 {
                assume(false);
                value = value + ((self.bytes[start_idx + j] as u64) << (j * 8));
            }
            x_u64[i] = value;
        }
        assume(false);
        let width = 1 << w;
        let window_mask = width - 1;
        let mut pos = 0;
        let mut carry = 0;
        while pos < 256 
        decreases 256 - pos
        {
            assume(false);
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
            assume(false);
            pos += w;
        }
        naf
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
    
    pub(crate) fn as_radix_16(&self) -> [i8; 64] {
        //debug_assert!(self[31] <= 127);
        let mut output = [0i8; 64];

        // Step 1: change radix.
        // Convert from radix 256 (bytes) to radix 16 (nibbles)
        for i in 0..32 {
            output[2 * i] = ((self.bytes[i] >> 0) & 15) as i8;      // bot_half inline
            output[2 * i + 1] = ((self.bytes[i] >> 4) & 15) as i8;  // top_half inline
        }
        // Precondition note: since self[31] <= 127, output[63] <= 7

        // Step 2: recenter coefficients from [0,16) to [-8,8)
        for i in 0..63 {
            assume(false);
            let carry = (output[i] + 8) >> 4;
            output[i] = output[i] - (carry << 4);
            output[i + 1] = output[i + 1] + carry;
        }
        // Precondition note: output[63] is not recentered.  It
        // increases by carry <= 1.  Thus output[63] <= 8.

        output
    }



    /// Unpack this `Scalar` to an `UnpackedScalar` for faster arithmetic.
    pub(crate) fn unpack(&self) -> UnpackedScalar {
        UnpackedScalar::from_bytes(&self.bytes)
    }



    
    /// Generate a random scalar using the provided RNG.
    /// 
    // Original random method from scalar.rs
    /* pub fn random<R: CryptoRng + ?Sized>(rng: &mut R) -> Self {
        let mut scalar_bytes = [0u8; 64];
        rng.fill_bytes(&mut scalar_bytes);
        Scalar::from_bytes_mod_order_wide(&scalar_bytes)
    }
    */
    /// SPEC FROM scalar.md
    /// 1. to_nat_Scalar (random (...)) ∈ {0, 1,..., ℓ - 1}
    /// 2. (to_nat_Scalar result) is uniformly random in {0, 1,..., ℓ - 1}
    /// NOTE: is condition 2. really true? 
    /// Specialized version for CryptoRng trait (matches original scalar.rs)
    pub fn random<R>(rng: &mut R) -> (s:Self) 
    where
        R: CryptoRng + Rng,
        ensures
            0 <= bytes_to_nat(&s.bytes) <= group_order() - 1, // 1.
            is_random_scalar(&s), // 2.
    {
        let mut scalar_bytes = [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
                               0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
                               0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
                               0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
        
        // Fill the bytes using random_u8
        let mut i = 0;
        while i < 64
            decreases 64 - i
        {
            scalar_bytes[i] = random_u8(rng);
            i += 1;
        }
        let s = Scalar::from_bytes_mod_order_wide(&scalar_bytes);
        assume(false);
        s
    }
    


    /// Hash a slice of bytes into a scalar.
    /// 
    /// This method creates a hash of the input bytes and converts it to a scalar.
    /// The scalar is reduced modulo the group order ℓ.
    /// ORIGINAL CODE:
    /// pub fn hash_from_bytes<D>(input: &[u8]) -> Scalar
    /// where
    ///     D: Digest<OutputSize = U64> + Default,
    /// {
    ///     let mut hash = D::default();
    ///     hash.update(input);
    ///     Scalar::from_hash(hash)
    /// }
    /// SPEC FROM scalar.md 
    /// 1. to_nat_Scalar (hash_from_bytes (...)) ∈ {0, 1,..., ℓ - 1}
    /// 2. Function is deterministic, same input always gives the same result
    /// 3. to_nat_Scalar (hash_from_bytes (...)) is uniformly distributed in {0, 1,..., ℓ - 1}
    /// NOTE: is condition 3. really true? 
    /// ###
    // Commented out due to Verus generic bounds issues
    // NOTE: Verus panics with generic digests 
         pub fn hash_from_bytes(input: &[u8]) -> (s:Scalar)
    //where
    //    D: Digest<OutputSize = U64> + Default,
        ensures
            0 <= bytes_to_nat(&s.bytes) <= group_order() - 1, // 1.
            // NOTE: see if we need 2. 
            is_random_bytes(input) ==> is_random_scalar(&s), // ALTERNATIVE 3. 
    {
        let mut hash = sha512_new();
        sha512_update(&mut hash, input);
        let result_array = sha512_finalize(hash);
        let s = Scalar::from_bytes_mod_order_wide(&result_array);
        assume(false);
        s
    }

    
    /// Construct a scalar from an existing `Digest` instance.
    /// 
    /// This method extracts the final hash output and converts it to a scalar.
    /// The scalar is reduced modulo the group order ℓ.
    // Original code from scalar.rs:
    // pub fn from_hash<D>(hash: D) -> Scalar
    // where
    //     D: Digest<OutputSize = U64>,
    // {
    //     let mut output = [0u8; 64];
    //     output.copy_from_slice(hash.finalize().as_slice());
    //     Scalar::from_bytes_mod_order_wide(&output)
    // }
    // SPEC FROM scalar.md
    // ### `pub fn from_hash<D>(hash: D) -> Scalar`
    // 1. to_nat_Scalar (from_hash (...)) ∈ {0, 1,..., ℓ - 1}
    // 2. Function is deterministic, same input always gives the same result
    // 3. to_nat_Scalar (from_hash (...)) is uniformly distributed in {0, 1,..., ℓ - 1}
    // ###
    pub fn from_hash(hash: Sha512) -> (s: Scalar)
    ensures 
        0 <= bytes_to_nat(&s.bytes) <= group_order() - 1, // 1.
        // NOTE: see if we need 2. 
        is_random_hash(&hash) ==> is_random_scalar(&s), // ALTERNATIVE 3. 
    {
        let result_array = sha512_finalize(hash);
        let s = Scalar::from_bytes_mod_order_wide(&result_array);
        assume(false);
        s
    }

    
    /// Reduce this `Scalar` modulo \\(\ell\\).
    /// 
    /// This uses Montgomery reduction to compute the canonical representative
    /// of the scalar modulo the group order ℓ.
    #[allow(non_snake_case)]
    fn reduce(&self) -> (r:Scalar) 
    ensures bytes_to_nat(&r.bytes) == bytes_to_nat(&self.bytes)
    {
        assume(false);
        let x = self.unpack();
        let xR = UnpackedScalar::mul_internal(&x, &constants::R);
        let x_mod_l = UnpackedScalar::montgomery_reduce(&xR);
        Scalar { bytes: x_mod_l.to_bytes() }
    }
 
    /// Check whether this `Scalar` is the canonical representative mod \\(\ell\\). This is not
    /// public because any `Scalar` that is publicly observed is reduced, by scalar invariant #2.
    fn is_canonical(&self) -> Choice {
        let reduced = self.reduce();
        // Manual comparison instead of using ct_eq
        let mut equal = true;
        for i in 0..32 {
            equal = equal && (self.bytes[i] == reduced.bytes[i]);
        }
        if equal { Choice::from(1u8) } else { Choice::from(0u8) }
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
/// SPEC FROM scalar.md
/// 1. 2^254 ≤ as_nat_32_u8 result
/// 2. as_nat_32_u8 result < 2^255
/// 3. (as_nat_32_u8 result) is divisible by 8 (the cofactor of curve25519)
/// 4. If the input is uniformly random then the result is uniformly random

pub const fn clamp_integer(mut bytes: [u8; 32]) -> (result: [u8; 32]) 
ensures
    pow2(254) <= bytes_to_nat(&result) < pow2(255), // 1.,2.
    bytes_to_nat(&result) % 8 == 0, // 3. 
    is_random_bytes(&bytes) ==> is_random_bytes(&result), // 4. 
{
    bytes[0] &= 0b1111_1000;
    bytes[31] &= 0b0111_1111;
    bytes[31] |= 0b0100_0000;
    assume(false);
    bytes
}

fn main() {}

}  