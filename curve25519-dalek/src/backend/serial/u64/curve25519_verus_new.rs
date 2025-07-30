//
// Copyright 2020-2021 Signal Messenger, LLC.
// SPDX-License-Identifier: AGPL-3.0-only
//
// Verus adaptation for XEdDSA signature verification
// This file provides the structure for Verus integration but compiles in regular Rust

#![allow(unused)]

use crate::constants::ED25519_BASEPOINT_TABLE;
use crate::edwards::EdwardsPoint;
use crate::montgomery::MontgomeryPoint;
use crate::scalar;
use crate::scalar::Scalar;

use subtle::ConstantTimeEq;

use sha2::{Digest, Sha512};
use subtle::{Choice, ConditionallySelectable};
use vstd::prelude::*;
use vstd::arithmetic::power2::*;
use vstd::calc;

#[cfg(feature = "rand_core")]
use rand_core::{CryptoRng, RngCore};

verus! {

    // External function specifications for random functions
    #[cfg(feature = "rand_core")]
    #[verifier::external_body]
    fn random_u8<R>(rng: &mut R) -> u8
    where
        R: CryptoRng + RngCore,
    {
        let mut bytes = [0u8; 1];
        rng.fill_bytes(&mut bytes);
        bytes[0]
    }

    // External function specifications for SHA-512
    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExSha512(Sha512);

    #[verifier::external_body]
    fn sha512_new() -> Sha512 {
        Sha512::new()
    }

    #[verifier::external_body]
    fn sha512_update(hash: &mut Sha512, data: &[u8]) {
        hash.update(data);
    }

    #[verifier::external_body]
    fn sha512_finalize(hash: Sha512) -> [u8; 64] {
        hash.finalize().into()
    }

    // Utility function for clamping X25519 private keys
    fn clamp_integer(mut bytes: [u8; 32]) -> [u8; 32] {
        bytes[0] &= 248;
        bytes[31] &= 127;
        bytes[31] |= 64;
        bytes
    }

const AGREEMENT_LENGTH: usize = 32;
pub const PRIVATE_KEY_LENGTH: usize = 32;
pub const PUBLIC_KEY_LENGTH: usize = 32;
pub const SIGNATURE_LENGTH: usize = 64;

// Placeholder types for X25519 operations
#[derive(Clone)]
pub struct StaticSecret {
    bytes: [u8; 32],
}

impl StaticSecret {
    pub fn to_bytes(&self) -> [u8; 32] {
        self.bytes
    }
}

impl From<[u8; 32]> for StaticSecret {
    fn from(bytes: [u8; 32]) -> Self {
        StaticSecret { bytes }
    }
}

pub struct PublicKey {
    bytes: [u8; 32],
}

impl PublicKey {
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.bytes
    }
}

impl From<&StaticSecret> for PublicKey {
    fn from(_secret: &StaticSecret) -> Self {
        // Placeholder implementation for X25519 public key derivation
        PublicKey { bytes: [0u8; 32] }
    }
}

impl From<[u8; 32]> for PublicKey {
    fn from(bytes: [u8; 32]) -> Self {
        PublicKey { bytes }
    }
}

#[derive(Clone)]
pub struct PrivateKey {
    secret: StaticSecret,
}

impl PrivateKey {
    #[cfg(feature = "rand_core")]
    pub fn new<R>(csprng: &mut R) -> Self
    where
        R: CryptoRng + RngCore,
    {
        // This is essentially StaticSecret::random_from_rng only with clamping
        let mut bytes = [0u8; 32];
        csprng.fill_bytes(&mut bytes);
        bytes = clamp_integer(bytes);

        let secret = StaticSecret::from(bytes);
        PrivateKey { secret }
    }

    pub fn calculate_agreement(
        &self,
        their_public_key: &[u8; PUBLIC_KEY_LENGTH],
    ) -> [u8; AGREEMENT_LENGTH] {
        // Placeholder implementation for X25519 Diffie-Hellman
        // In real implementation this would be:
        // *self.secret.diffie_hellman(&PublicKey::from(*their_public_key)).as_bytes()
        [0u8; AGREEMENT_LENGTH]
    }

    /// Calculates an XEdDSA signature using the X25519 private key directly.
    ///
    /// Refer to <https://signal.org/docs/specifications/xeddsa/#curve25519> for more details.
    ///
    /// Note that this implementation varies slightly from that paper in that the sign bit is not
    /// fixed to 0, but rather passed back in the most significant bit of the signature which would
    /// otherwise always be 0. This is for compatibility with the implementation found in
    /// libsignal-protocol-java.
    #[cfg(feature = "rand_core")]
    pub fn calculate_signature<R>(
        &self,
        csprng: &mut R,
        message: &[&[u8]],
    ) -> [u8; SIGNATURE_LENGTH]
    where
        R: CryptoRng + RngCore,
    {
        let mut random_bytes = [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
                               0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
                               0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
                               0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
        let mut i = 0;
        while i < 64 {
            random_bytes[i] = random_u8(csprng);
            i += 1;
        }

        let key_data = self.secret.to_bytes();
        let a = Scalar::from_bytes_mod_order(key_data);
        let ed_public_key_point = &a * &ED25519_BASEPOINT_TABLE;
        let ed_public_key = ed_public_key_point.compress();
        let sign_bit = ed_public_key.as_bytes()[31] & 0b1000_0000_u8;

        let mut hash1 = sha512_new();
        let hash_prefix = [
            0xFEu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8,
            0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8,
            0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8,
        ];
        // Explicitly pass a slice to avoid generating multiple versions of update().
        sha512_update(&mut hash1, &hash_prefix);
        sha512_update(&mut hash1, &key_data);
        // Manual iteration to avoid Verus limitation with slice iterators
        let mut i = 0;
        while i < message.len() {
            sha512_update(&mut hash1, message[i]);
            i += 1;
        }
        sha512_update(&mut hash1, &random_bytes);

        let r = Scalar::from_hash(hash1);
        let cap_r = (&r * &ED25519_BASEPOINT_TABLE).compress();

        let mut hash = sha512_new();
        sha512_update(&mut hash, cap_r.as_bytes());
        sha512_update(&mut hash, ed_public_key.as_bytes());
        // Manual iteration to avoid Verus limitation with slice iterators
        let mut i = 0;
        while i < message.len() {
            sha512_update(&mut hash, message[i]);
            i += 1;
        }

        let h = Scalar::from_hash(hash);
        let s = (h * a) + r;

        let mut result = [0u8; SIGNATURE_LENGTH];
        // Copy cap_r bytes
        let cap_r_bytes = cap_r.as_bytes();
        let mut i = 0;
        while i < 32 {
            result[i] = cap_r_bytes[i];
            i += 1;
        }
        // Copy s bytes
        let s_bytes = s.as_bytes();
        let mut i = 0;
        while i < 32 {
            result[32 + i] = s_bytes[i];
            i += 1;
        }
        // Set sign bit
        let mut last = result[SIGNATURE_LENGTH - 1];
        last &= 0b0111_1111_u8;
        last |= sign_bit;
        result[SIGNATURE_LENGTH - 1] = last;
        result
    }

    pub fn verify_signature(
        their_public_key: &[u8; PUBLIC_KEY_LENGTH],
        message: &[&[u8]],
        signature: &[u8; SIGNATURE_LENGTH],
    ) -> bool {
        let mont_point = MontgomeryPoint(*their_public_key);
        let ed_pub_key_point =
            match mont_point.to_edwards((signature[SIGNATURE_LENGTH - 1] & 0b1000_0000_u8) >> 7) {
                Some(x) => x,
                None => return false,
            };
        let cap_a = ed_pub_key_point.compress();
        let mut cap_r = [0u8; 32];
        let mut i = 0;
        while i < 32 {
            cap_r[i] = signature[i];
            i += 1;
        }
        let mut s = [0u8; 32];
        let mut i = 0;
        while i < 32 {
            s[i] = signature[32 + i];
            i += 1;
        }
        s[31] &= 0b0111_1111_u8;
        if (s[31] & 0b1110_0000_u8) != 0 {
            return false;
        }
        let minus_cap_a = -ed_pub_key_point;

        let mut hash = sha512_new();
        // Explicitly pass a slice to avoid generating multiple versions of update().
        sha512_update(&mut hash, &cap_r);
        sha512_update(&mut hash, cap_a.as_bytes());
        let mut i = 0;
        while i < message.len() {
            sha512_update(&mut hash, message[i]);
            i += 1;
        }
        let h = Scalar::from_hash(hash);

        let cap_r_check_point = EdwardsPoint::vartime_double_scalar_mul_basepoint(
            &h,
            &minus_cap_a,
            &Scalar::from_bytes_mod_order(s),
        );
        let cap_r_check = cap_r_check_point.compress();

        bool::from(cap_r_check.as_bytes().ct_eq(&cap_r))
    }

    pub fn derive_public_key_bytes(&self) -> [u8; PUBLIC_KEY_LENGTH] {
        *PublicKey::from(&self.secret).as_bytes()
    }

    pub fn private_key_bytes(&self) -> [u8; PRIVATE_KEY_LENGTH] {
        self.secret.to_bytes()
    }
}

impl From<[u8; PRIVATE_KEY_LENGTH]> for PrivateKey {
    fn from(private_key: [u8; 32]) -> Self {
        let secret = StaticSecret::from(clamp_integer(private_key));
        PrivateKey { secret }
    }
}

}
