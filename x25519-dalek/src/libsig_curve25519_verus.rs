//
// Copyright 2020-2021 Signal Messenger, LLC.
// SPDX-License-Identifier: AGPL-3.0-only

/**** 
 * 
 * NOTE: Verus models for libsignal/rust/core/src/curve/curve25519.rs
 *
 */

//! XEdDSA signature functionality for X25519 keys
//! 
//! This module implements the XEdDSA signature scheme which allows X25519 keys
//! to be used for both key exchange and signatures.


#![allow(unused)]

use curve25519_dalek::constants::ED25519_BASEPOINT_TABLE;
use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::montgomery::MontgomeryPoint;
use curve25519_dalek::scalar;
use curve25519_dalek::scalar::Scalar;
use crate::x25519::{PublicKey, StaticSecret};

use subtle::ConstantTimeEq;

use sha2::{Digest, Sha512};
use subtle::{Choice, ConditionallySelectable};
use vstd::prelude::*;
use vstd::arithmetic::power2::*;
use vstd::calc;

use rand::{CryptoRng, Rng};
use rand_core::RngCore;

use curve25519_dalek::backend::serial::u64::scalar::*;

verus! {


    pub uninterp spec fn is_random(x: u8) -> bool;
    pub uninterp spec fn is_random_bytes(bytes: &[u8]) -> bool;
    pub uninterp spec fn is_random_hash(hash: &Sha512) -> bool;
    pub uninterp spec fn is_random_scalar(scalar: &Scalar) -> bool;

    /// External specification for RngCore::fill_bytes ensuring randomness
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

    // External function specifications for SHA-512
    /// External specification for SHA-512 hasher
   // #[verifier::external_type_specification]
   // #[verifier::external_body]
   // pub struct ExSha512(Sha512);

    // External specifications for curve types
    /// External specification for Montgomery point
    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExMontgomeryPoint(MontgomeryPoint);

    /// External specification for Edwards point
    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExEdwardsPoint(EdwardsPoint);

    /// External specification for compressed Edwards Y coordinate
    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExCompressedEdwardsY(curve25519_dalek::edwards::CompressedEdwardsY);

    /// External specification for scalar
    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExScalar(Scalar);

    // External specifications for X25519 types
    /// External specification for static secret
    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExStaticSecret(StaticSecret);

    /// External specification for public key
    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExPublicKey(PublicKey);

    /// External specification for shared secret
    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExSharedSecret(crate::x25519::SharedSecret);

    #[verifier::external_body]
    fn montgomery_point_new(bytes: [u8; 32]) -> MontgomeryPoint {
        MontgomeryPoint(bytes)
    }

    #[verifier::external_body]
    fn montgomery_to_edwards(point: &MontgomeryPoint, sign: u8) -> Option<EdwardsPoint> {
        point.to_edwards(sign)
    }

    #[verifier::external_body]
    fn edwards_compress(point: &EdwardsPoint) -> curve25519_dalek::edwards::CompressedEdwardsY {
        point.compress()
    }

    #[verifier::external_body]
    fn compressed_edwards_as_bytes(compressed: &curve25519_dalek::edwards::CompressedEdwardsY) -> &[u8; 32] {
        compressed.as_bytes()
    }

    #[verifier::external_body]
    fn edwards_negate(point: &EdwardsPoint) -> EdwardsPoint {
        -point
    }

    #[verifier::external_body]
    fn edwards_vartime_double_scalar_mul_basepoint(
        a: &Scalar, 
        point_a: &EdwardsPoint, 
        b: &Scalar
    ) -> EdwardsPoint {
        EdwardsPoint::vartime_double_scalar_mul_basepoint(a, point_a, b)
        }

    #[verifier::external_body]
    fn scalar_from_bytes_mod_order(bytes: [u8; 32]) -> (result: Scalar)
    // TODO
   //  ensures bytes_to_nat(&bytes) % group_order() == bytes_to_nat(&scalar_to_bytes(&result)) % group_order(),
    {
         Scalar::from_bytes_mod_order(bytes)
    }



    #[verifier::external_body]
    fn scalar_from_hash(hash: Sha512) -> (result: Scalar)
    ensures
        is_random_hash(&hash) ==> is_random_scalar(&result),
    {
        Scalar::from_hash(hash)
    }

    #[verifier::external_body]
    fn scalar_as_bytes(scalar: &Scalar) -> &[u8; 32] {
        scalar.as_bytes()
    }

    #[verifier::external_body]
   // #[verifier::allow_in_spec]
    fn scalar_to_bytes(scalar: &Scalar) -> (result: [u8; 32])
    {
        scalar.to_bytes()
    }
    
    #[verifier::external_body]
    fn scalar_mul(a: &Scalar, b: &Scalar) -> Scalar {
        a * b
    }

    #[verifier::external_body]
    fn scalar_add(a: &Scalar, b: &Scalar) -> Scalar {
        a + b
    }

    #[verifier::external_body]
    fn scalar_basepoint_mul(scalar: &Scalar) -> EdwardsPoint {
        scalar * ED25519_BASEPOINT_TABLE
    }

    #[verifier::external_body]
    fn constant_time_eq(a: &[u8; 32], b: &[u8; 32]) -> bool {
        use subtle::ConstantTimeEq;
        bool::from(a.ct_eq(b))
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
    fn sha512_update_64(hash: &mut Sha512, data: &[u8;64]) 
    ensures
        is_random_bytes(data) ==> is_random_hash(hash),
    {
        hash.update(data);
    }

 /*    #[verifier::external_body]
    fn sha512_finalize(hash: Sha512) -> (result: [u8; 64])
    requires
        is_random_bytes(hash.finalize().as_slice()),
    ensures  
        is_random_bytes(&result),
    {
        hash.finalize().into()
    }
*/
    #[verifier::external_body]
    fn static_secret_from_bytes(bytes: [u8; 32]) -> StaticSecret {
        StaticSecret::from(bytes)
    }

    #[verifier::external_body]
    fn static_secret_to_bytes(secret: &StaticSecret) -> [u8; 32] {
        secret.to_bytes()
    }

    #[verifier::external_body]
    fn public_key_from_static_secret(secret: &StaticSecret) -> PublicKey {
        PublicKey::from(secret)
    }

    #[verifier::external_body]
    fn public_key_as_bytes(pubkey: &PublicKey) -> &[u8; 32] {
        pubkey.as_bytes()
    }

    #[verifier::external_body]
    fn public_key_from_bytes(bytes: [u8; 32]) -> PublicKey {
        PublicKey::from(bytes)
    }

    #[verifier::external_body]
    fn static_secret_diffie_hellman(secret: &StaticSecret, pubkey: &PublicKey) -> crate::x25519::SharedSecret {
        secret.diffie_hellman(pubkey)
    }

    #[verifier::external_body]
    fn shared_secret_as_bytes(shared: &crate::x25519::SharedSecret) -> &[u8; 32] {
        shared.as_bytes()
    }

    // Utility function for clamping X25519 private keys
    fn clamp_integer(mut bytes: [u8; 32]) -> [u8; 32] {
        bytes[0] &= 248;
        bytes[31] &= 127;
        bytes[31] |= 64;
        bytes
    }

const AGREEMENT_LENGTH: usize = 32;
/// The length of a private key in bytes
pub const PRIVATE_KEY_LENGTH: usize = 32;
/// The length of a public key in bytes  
pub const PUBLIC_KEY_LENGTH: usize = 32;
/// The length of a signature in bytes
pub const SIGNATURE_LENGTH: usize = 64;

/// A private key for XEdDSA signatures and X25519 key exchange
pub struct PrivateKey {
    secret: StaticSecret,
}

impl Clone for PrivateKey {
    fn clone(&self) -> Self {
        PrivateKey { secret: static_secret_from_bytes(static_secret_to_bytes(&self.secret)) }
    }
}

impl PrivateKey {
    /// Generate a new private key using the provided CSPRNG
    pub fn new<R>(csprng: &mut R) -> (result: PrivateKey)
    where
        R: CryptoRng + Rng,
    requires
        true, // We could add requirements about the RNG here
    ensures
        // The result should be a valid PrivateKey
        true, // We could add more specific properties here
    {
        // This is essentially StaticSecret::random_from_rng only with clamping
        let mut bytes = [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
                         0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
        let mut i = 0;
        while i < 32
            decreases 32 - i
        {
            bytes[i] = random_u8(csprng);
            i += 1;
        }
        bytes = clamp_integer(bytes);

        let secret = static_secret_from_bytes(bytes);
        let result = PrivateKey { secret };
        result
    }

    /// Calculate the shared secret with another party's public key
    pub fn calculate_agreement(
        &self,
        their_public_key: &[u8; PUBLIC_KEY_LENGTH],
    ) -> [u8; AGREEMENT_LENGTH] {
        let pubkey = public_key_from_bytes(*their_public_key);
        let shared = static_secret_diffie_hellman(&self.secret, &pubkey);
        *shared_secret_as_bytes(&shared)
    }

    /// Calculates an XEdDSA signature using the X25519 private key directly.
    ///
    /// Refer to <https://signal.org/docs/specifications/xeddsa/#curve25519> for more details.
    ///
    /// Note that this implementation varies slightly from that paper in that the sign bit is not
    /// fixed to 0, but rather passed back in the most significant bit of the signature which would
    /// otherwise always be 0. This is for compatibility with the implementation found in
    /// libsignal-protocol-java.
    /// 
    
    // Vars	Definition
    // k	Montgomery private key (integer mod q)
    // M	Message to sign (byte sequence)
    // Z	64 bytes secure random data (byte sequence)

    // xeddsa_sign(k, M, Z):
    // A, a = calculate_key_pair(k)
    // r = hash1(a || M || Z) (mod q)
    // R = rB
    // h = hash(R || A || M) (mod q)
    // s = r + ha (mod q)
    // return R || s

    // WHERE:
    // calculate_key_pair(k):
    // E = kB
    // A.y = E.y
    // A.s = 0
    // THIS IS SKIPPED IN IMPLEMENTATION
    // SO a IS ALWAYS k
    // if E.s == 1:
    //     a = -k (mod q)
    // else:
    //     a = k (mod q)
    // return A, 


    pub fn calculate_signature<R>(
        &self,
        csprng: &mut R,
        message: &[&[u8]],
        // message plays the role of M, the message to sign (byte sequence)
    ) -> (result: ([u8; SIGNATURE_LENGTH], Scalar))
    where
        R: CryptoRng + Rng,
    requires
        true,
    ensures
        result.0.len() == SIGNATURE_LENGTH,
        // is_random_scalar(&result.1), 
       {

        // ORIGINAL CODE C1:
        //let mut random_bytes = [0u8; 64];
        // START OF VERUS-COMPLIANT CODE FOR C1:
        let mut random_bytes = [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
                               0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
                               0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
                               0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
        // END OF VERUS-COMPLIANT CODE FOR C1

        fill_bytes(csprng, &mut random_bytes);
        assert(is_random_bytes(&random_bytes));
        // random_bytes plays the role of Z, a 64 bytes secure random data (byte sequence)
        /* OLDER WORKAROUND 
        let mut i = 0;
        while i < 64
            decreases 64 - i
        {
            random_bytes[i] = random_u8(csprng);
            i += 1;
        }
        */

        // &self.secret plays the role of k, the Montgomery private key (integer mod q)
        let key_data = static_secret_to_bytes(&self.secret);
            
        // A, a = calculate_key_pair(k)
        // a is k converted to a scalar
        let a = scalar_from_bytes_mod_order(key_data);
        // ed_public_key_point plays the role of E
        let ed_public_key_point = scalar_basepoint_mul(&a);
        // ed_public_key plays the role of A
        let ed_public_key = edwards_compress(&ed_public_key_point);
        // sign_bit plays the role of A.s
        let sign_bit = compressed_edwards_as_bytes(&ed_public_key)[31] & 0b1000_0000_u8;

        // NOW DOING r = hash1(a || M || Z) (mod q)
        let mut hash1 = sha512_new();
        let hash_prefix = [
            0xFEu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8,
            0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8,
            0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8, 0xFFu8,
        ];
        // Explicitly pass a slice to avoid generating multiple versions of update().
        
        sha512_update(&mut hash1, &hash_prefix);
        //  NOTE: spec here 
        // https://signal.org/docs/specifications/xeddsa/#xeddsa
        // says they should put a in hash1, but they put k - should be same thing
        sha512_update(&mut hash1, &key_data);

        // ORIGINAL CODE C3:
        // for message_piece in message {
        //     hash1.update(message_piece);
        // }
        // START OF VERUS-COMPLIANT CODE FOR C3:
        // Manual iteration to avoid Verus limitation with slice iterators
        let mut i = 0;
        while i < message.len()
            decreases message.len() - i
        {
            sha512_update(&mut hash1, message[i]);
            i += 1;
        }
        // END OF VERUS-COMPLIANT CODE FOR C3:

        // NOTE: needed to create sha512_update_64 version to help verus verifier, 
        // should be removed when we can get the verifier to work without it
        sha512_update_64(&mut hash1, &random_bytes);
        assert(is_random_hash(&hash1));

        let r = scalar_from_hash(hash1);
        assert(is_random_scalar(&r));

        //r = H(prefix || private_key_bytes || message || random_bytes)
        // r = H(prefix || k || M || Z)

        let cap_r = edwards_compress(&scalar_basepoint_mul(&r));
        //  cap_r = R = [r]B
  
        // NOW DOING h = hash(R || A || M) (mod q)
        let mut hash = sha512_new();
        sha512_update(&mut hash, compressed_edwards_as_bytes(&cap_r));
        sha512_update(&mut hash, compressed_edwards_as_bytes(&ed_public_key));
        
        // ORIGINAL CODE C4:
        // for message_piece in message {
        //     hash.update(message_piece);
        // }
        // START OF VERUS-COMPLIANT CODE FOR C4:
        let mut i = 0;
        while i < message.len()
            decreases message.len() - i
        {
            sha512_update(&mut hash, message[i]);
            i += 1;
        }
        // END OF VERUS-COMPLIANT CODE FOR C4
        
        let h = scalar_from_hash(hash);
        // h = H(R || A || M) (mod q)

        // NOW DOING s = h * a + r
        // s = h * a + r
        let s = scalar_add(&scalar_mul(&h, &a), &r);

        // s = H(R || A || M) * a + r (mod q)

        let mut result = [0u8; SIGNATURE_LENGTH];
        // Copy cap_r bytes
        let cap_r_bytes = compressed_edwards_as_bytes(&cap_r);
        let mut i = 0;
        while i < 32
            decreases 32 - i
        {
            result[i] = cap_r_bytes[i];
            i += 1;
        }
        // Copy s bytes
        let s_bytes = scalar_as_bytes(&s);
        let mut i = 0;
        while i < 32
            decreases 32 - i
        {
            result[32 + i] = s_bytes[i];
            i += 1;
        }
        // Set sign bit
        let mut last = result[SIGNATURE_LENGTH - 1];
        last &= 0b0111_1111_u8;
        last |= sign_bit;
        result[SIGNATURE_LENGTH - 1] = last;
        (result, s)
    }

    /// Verify an XEdDSA signature against a public key and message
    pub fn verify_signature(
        their_public_key: &[u8; PUBLIC_KEY_LENGTH],
        message: &[&[u8]],
        signature: &[u8; SIGNATURE_LENGTH],
    ) -> bool {
        let mont_point = montgomery_point_new(*their_public_key);
        let ed_pub_key_point =
            match montgomery_to_edwards(&mont_point, (signature[SIGNATURE_LENGTH - 1] & 0b1000_0000_u8) >> 7) {
                Some(x) => x,
                None => return false,
            };
        let cap_a = edwards_compress(&ed_pub_key_point);
        let mut cap_r = [0u8; 32];
        let mut i = 0;
        while i < 32
            decreases 32 - i
        {
            cap_r[i] = signature[i];
            i += 1;
        }
        let mut s = [0u8; 32];
        let mut i = 0;
        while i < 32
            decreases 32 - i
        {
            s[i] = signature[32 + i];
            i += 1;
        }
        s[31] &= 0b0111_1111_u8;
        if (s[31] & 0b1110_0000_u8) != 0 {
            return false;
        }
        let minus_cap_a = edwards_negate(&ed_pub_key_point);

        let mut hash = sha512_new();
        // Explicitly pass a slice to avoid generating multiple versions of update().
        sha512_update(&mut hash, &cap_r);
        sha512_update(&mut hash, compressed_edwards_as_bytes(&cap_a));
        let mut i = 0;
        while i < message.len()
            decreases message.len() - i
        {
            sha512_update(&mut hash, message[i]);
            i += 1;
        }
        let h = scalar_from_hash(hash);

        let cap_r_check_point = edwards_vartime_double_scalar_mul_basepoint(
            &h,
            &minus_cap_a,
            &scalar_from_bytes_mod_order(s),
        );
        let cap_r_check = edwards_compress(&cap_r_check_point);

        constant_time_eq(compressed_edwards_as_bytes(&cap_r_check), &cap_r)
    }

    /// Derive the public key bytes from this private key
    pub fn derive_public_key_bytes(&self) -> [u8; PUBLIC_KEY_LENGTH] {
        let pubkey = public_key_from_static_secret(&self.secret);
        *public_key_as_bytes(&pubkey)
    }

    /// Get the private key bytes
    pub fn private_key_bytes(&self) -> [u8; PRIVATE_KEY_LENGTH] {
        static_secret_to_bytes(&self.secret)
    }
}

impl From<[u8; PRIVATE_KEY_LENGTH]> for PrivateKey {
    fn from(private_key: [u8; 32]) -> Self {
        let secret = static_secret_from_bytes(clamp_integer(private_key));
        PrivateKey { secret }
    }
}

} 