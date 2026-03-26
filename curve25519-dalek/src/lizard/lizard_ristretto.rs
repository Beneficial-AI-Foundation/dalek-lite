//! Defines additional methods on `RistrettoPoint` for Lizard.
//!
//! For the reference mathematical intent of the encoding/decoding scheme, see
//! `crate::specs::lizard_specs`.
#![allow(non_snake_case)]

use digest::generic_array::typenum::U32;
use digest::Digest;

use crate::constants;
use crate::field::FieldElement;

use subtle::Choice;
use subtle::ConditionallySelectable;
use subtle::ConstantTimeEq;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::backend::serial::u64::subtle_assumes::choice_is_true;
#[allow(unused_imports)]
use crate::backend::serial::u64::subtle_assumes::{
    choice_and, choice_or, conditional_assign_generic, ct_eq_bytes32, negate_field_element,
    select_u8,
};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::core_assumes::axiom_sha256_output_length;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::core_assumes::spec_sha256;
use crate::core_assumes::{bytes32_8_to_24, sha256_hash_bytes, write_bytes32_8_to_24};

use crate::edwards::EdwardsPoint;

use super::jacobi_quartic::JacobiPoint;
use super::lizard_constants;

use crate::ristretto::RistrettoPoint;
#[allow(unused_imports)]
use core::prelude::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::core_specs::u8_32_as_nat;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::{lemma_mod_bound, lemma_small_mod};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::lizard_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::ristretto_specs::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::add_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::as_bytes_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::constants_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::from_bytes_lemmas::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::batch_invert_lemmas::lemma_is_zero_iff_canonical_nat_zero;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::lemma_square_matches_field_square;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::sqrt_m1_lemmas::lemma_sqrt_m1_limbs_bounded;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::sqrt_ratio_lemmas::{
    lemma_canonical_nat_lt_p, lemma_invsqrt_unique,
};

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::to_nat_lemmas::lemma_canonical_bytes_equal;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::lizard_lemmas::*;

verus! {

// lemma_h_equals_spec_lizard_fe_bytes, lemma_decode_candidate_preimage,
// lemma_coset_bridge, lemma_invsqrt_bridge moved to lizard_lemmas.rs
// for co-location with their axiom dependencies.
impl RistrettoPoint {
    /// Directly encode 253 bits as a RistrettoPoint, using Elligator
    pub fn from_uniform_bytes_single_elligator(bytes: &[u8; 32]) -> (result: RistrettoPoint)
        ensures
            is_well_formed_edwards_point(result.0),
            is_in_even_subgroup(result.0),
            // result = elligator(r_0)  where r_0 = from_bytes(bytes)
            edwards_point_as_affine(result.0) == spec_elligator_ristretto_flavor(
                fe51_as_canonical_nat(&spec_fe51_from_bytes(bytes)),
            ),
    {
        /* ORIGINAL CODE: RistrettoPoint::elligator_ristretto_flavor(&FieldElement::from_bytes(bytes)) */
        let fe = FieldElement::from_bytes(bytes);
        proof {
            lemma_fe51_limbs_bounded_weaken(&fe, 51, 54);
        }
        let result = RistrettoPoint::elligator_ristretto_flavor(&fe);
        proof {
            let fe_spec = spec_fe51_from_bytes(bytes);
            assert(fe51_as_canonical_nat(&fe) == fe51_as_canonical_nat(&fe_spec)) by {
                lemma_from_u8_32_as_nat(bytes);
                lemma_as_nat_32_mod_255(bytes);
            }
            assert(spec_elligator_ristretto_flavor(fe51_as_canonical_nat(&fe))
                == spec_elligator_ristretto_flavor(fe51_as_canonical_nat(&fe_spec)));
        }
        result
    }

    /// Encode 16 bytes of data to a RistrettoPoint, using the Lizard method.
    ///
    /// VERIFICATION NOTE: This generic Digest variant is not verified (`external`).
    /// The verified implementation is `lizard_encode_verus` below, which is
    /// semantically equivalent but uses SHA-256 via an `external_body` spec
    /// instead of the generic `Digest` trait. Both compute the same result
    /// when `D = Sha256`. Runtime test `test_lizard_encode_roundtrip_exhaustive`
    /// confirms behavioral equivalence.
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    pub fn lizard_encode<D: Digest>(data: &[u8; 16]) -> RistrettoPoint where
        D: Digest<OutputSize = U32>,
     {
        let mut fe_bytes: [u8; 32] = Default::default();

        let digest = D::digest(data);
        fe_bytes[0..32].copy_from_slice(digest.as_slice());
        fe_bytes[8..24].copy_from_slice(data);
        fe_bytes[0] &= 254;  // make positive since Elligator on r and -r is the same
        fe_bytes[31] &= 63;
        let fe = FieldElement::from_bytes(&fe_bytes);
        RistrettoPoint::elligator_ristretto_flavor(&fe)
    }

    /// Verus-friendly variant of `lizard_encode::<Sha256>`.
    ///
    pub fn lizard_encode_verus(data: &[u8; 16]) -> (result: RistrettoPoint)
        ensures
            is_well_formed_edwards_point(result.0),
            is_in_even_subgroup(result.0),
            edwards_point_as_affine(result.0) == spec_lizard_encode(data@),
    {
        /* ORIGINAL CODE: let mut fe_bytes: [u8; 32] = Default::default(); */
        let mut fe_bytes: [u8; 32] = [0u8;32];
        /* ORIGINAL CODE: let digest = D::digest(data); */
        let digest: [u8; 32] = sha256_hash_bytes(data);
        /* ORIGINAL CODE: fe_bytes[0..32].copy_from_slice(digest.as_slice()); */
        fe_bytes = digest;
        /* ORIGINAL CODE: fe_bytes[8..24].copy_from_slice(data); */
        write_bytes32_8_to_24(&mut fe_bytes, data);

        fe_bytes[0] &= 254;  // make positive since Elligator on r and -r is the same
        fe_bytes[31] &= 63;

        let fe = FieldElement::from_bytes(&fe_bytes);
        proof {
            lemma_fe51_limbs_bounded_weaken(&fe, 51, 54);
        }
        let result = RistrettoPoint::elligator_ristretto_flavor(&fe);
        proof {
            // fe = from_bytes(fe_bytes) = from_bytes(spec_lizard_fe_bytes(data))
            assert(fe51_as_canonical_nat(&fe) == fe51_as_canonical_nat(
                &spec_fe51_from_bytes(&fe_bytes),
            )) by {
                lemma_from_u8_32_as_nat(&fe_bytes);
                lemma_as_nat_32_mod_255(&fe_bytes);
            };
            axiom_sha256_output_length(data@);
            let spec_bytes = spec_lizard_fe_bytes(data@);
            assert(fe_bytes@ =~= spec_bytes@);
        }
        result
    }

    /// Decode 16 bytes of data from a RistrettoPoint, using the Lizard method.
    ///
    /// VERIFICATION NOTE: This generic Digest variant is not verified (`external`).
    /// The verified implementation is `lizard_decode_verus` below, which is
    /// semantically equivalent but uses SHA-256 via an `external_body` spec
    /// instead of the generic `Digest` trait. Both compute the same result
    /// when `D = Sha256`. Runtime test `test_lizard_decode_roundtrip_exhaustive`
    /// confirms behavioral equivalence.
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    pub fn lizard_decode<D: Digest>(&self) -> Option<[u8; 16]> where D: Digest<OutputSize = U32> {
        let mut result: [u8; 16] = Default::default();
        let mut h: [u8; 32] = Default::default();
        let (mask, fes) = self.elligator_ristretto_flavor_inverse();
        let mut n_found = 0;
        /* ORIGINAL CODE: for (j, fe_j) in fes.iter().enumerate() {
           Verus cannot compile .enumerate() even with verifier::external. */
        for j in 0..8 {
            let fe_j = &fes[j];
            let mut ok = Choice::from((mask >> j) & 1);
            let buf2 = fe_j.as_bytes();  // array
            h.copy_from_slice(&D::digest(&buf2[8..24]));  // array
            h[8..24].copy_from_slice(&buf2[8..24]);
            h[0] &= 254;
            h[31] &= 63;
            ok &= h.ct_eq(&buf2);
            for i in 0..16 {
                result[i] = u8::conditional_select(&result[i], &buf2[8 + i], ok);
            }
            n_found += ok.unwrap_u8();
        }
        if n_found == 1 {
            Some(result)
        } else {
            None
        }
    }

    /// Verus-friendly variant of `lizard_decode::<Sha256>`.
    ///
    #[verifier::rlimit(20)]
    pub fn lizard_decode_verus(&self) -> (result: Option<[u8; 16]>)
        requires
            is_well_formed_edwards_point(self.0),
        ensures
            match result {
                Some(bytes) => ({
                    let (x, y) = edwards_point_as_affine(self.0);
                    spec_lizard_decode_ristretto(x, y) == Some(bytes@) && is_lizard_preimage_coset(
                        bytes@,
                        ristretto_coset_affine(x, y),
                    )
                }),
                None => ({
                    let (x, y) = edwards_point_as_affine(self.0);
                    spec_lizard_decode_ristretto(x, y).is_None()
                }),
            },
    {
        /* ORIGINAL CODE: let mut result: [u8; 16] = Default::default(); */
        let mut result: [u8; 16] = [0u8;16];
        /* ORIGINAL CODE: let mut h: [u8; 32] = Default::default(); */
        let mut h: [u8; 32] = [0u8;32];
        let (mask, fes) = self.elligator_ristretto_flavor_inverse();

        let ghost epa = edwards_point_as_affine(self.0);
        let ghost coset_spec = ristretto_coset_affine(epa.0, epa.1);
        let ghost mut passed_data: Option<Seq<u8>> = None;

        let ghost candidates = spec_lizard_decode_candidates(self.0);

        let mut n_found: u32 = 0;
        proof {
            assert(forall|x: u8, n: u8|
                n < 8 && (x >> n) & 1u8 == 1u8 ==> #[trigger] (x & (1u8 << n)) != 0u8)
                by (bit_vector);
            assert(forall|x: u8, n: u8|
                n < 8 && #[trigger] (x & (1u8 << n)) != 0u8 ==> (x >> n) & 1u8 == 1u8)
                by (bit_vector);
        }
        /* ORIGINAL CODE: for (j, fe_j) in fes.iter().enumerate() { */
        for j in 0..8
            invariant
                n_found <= j as u32,
                n_found >= 1 <==> passed_data.is_Some(),
                passed_data.is_Some() ==> passed_data.unwrap().len() == 16,
                passed_data.is_Some() ==> is_lizard_preimage_coset(
                    passed_data.unwrap(),
                    coset_spec,
                ),
                passed_data.is_Some() ==> forall|i: int|
                    #![trigger result[i]]
                    0 <= i < 16 ==> result[i] == passed_data.unwrap()[i] as u8,
                // Exec count matches spec partial count
                n_found as nat == partial_sha_consistent_count(candidates, j as int),
                // Bit-shift equivalence (frame, both directions)
                forall|x: u8, n: u8|
                    n < 8 && (x >> n) & 1u8 == 1u8 ==> #[trigger] (x & (1u8 << n)) != 0u8,
                forall|x: u8, n: u8|
                    n < 8 && #[trigger] (x & (1u8 << n)) != 0u8 ==> (x >> n) & 1u8 == 1u8,
                // Elligator inverse postcondition (frame)
                forall|k: int|
                    #![trigger fes[k]]
                    0 <= k < 8 && (mask & (1u8 << k as u8)) != 0 ==> ({
                        let ej = spec_elligator_ristretto_flavor(fe51_as_canonical_nat(&fes[k]));
                        ej == coset_spec[0] || ej == coset_spec[1] || ej == coset_spec[2] || ej
                            == coset_spec[3]
                    }),
                // Candidates bridge (frame)
                candidates == spec_lizard_decode_candidates(self.0),
                ({
                    let cands = spec_lizard_decode_candidates(self.0);
                    forall|k: int|
                        #![trigger cands[k]]
                        0 <= k < 8 ==> (((mask & (1u8 << k as u8)) != 0) == cands[k].0 && (
                        cands[k].0 ==> fe51_as_canonical_nat(&fes[k]) == cands[k].1))
                }),
        {
            /* ORIGINAL CODE: let fe_j = &fes[j]; -- inlined below */
            let mut ok = Choice::from((mask >> j) & 1);
            let ghost mask_bit_set = choice_is_true(ok);
            let buf2 = fes[j].as_bytes();
            /* ORIGINAL CODE: h.copy_from_slice(&D::digest(&buf2[8..24]));
               h[8..24].copy_from_slice(&buf2[8..24]);
               -- Verus cannot handle D::digest (generic Digest trait) or slice ops;
               refactored into sha256_hash_bytes + write_bytes32_8_to_24 with
               an intermediate msg array. */
            let msg: [u8; 16] = bytes32_8_to_24(&buf2);
            h = sha256_hash_bytes(&msg);
            write_bytes32_8_to_24(&mut h, &msg);
            h[0] &= 254;
            h[31] &= 63;
            let ghost h_snap = h;
            /* ORIGINAL CODE: ok &= h.ct_eq(&buf2); */
            ok = choice_and(ok, ct_eq_bytes32(&h, &buf2));

            proof {
                // Scope each lemma to prevent intermediate facts from leaking
                assert(h_snap == spec_lizard_fe_bytes(msg@)) by {
                    lemma_h_equals_spec_lizard_fe_bytes(h_snap, msg@);
                };

                let cj = candidates[j as int];
                assert(choice_is_true(ok) == (cj.0 && spec_candidate_sha_consistent(cj.1))) by {
                    let sha_match = h_snap == buf2;
                    lemma_exec_ok_matches_spec_slot(
                        mask_bit_set,
                        sha_match,
                        &buf2,
                        msg@,
                        h_snap,
                        &fes[j as int],
                        cj,
                    );
                };

                if choice_is_true(ok) {
                    assert(is_lizard_preimage_coset(msg@, coset_spec)) by {
                        lemma_decode_candidate_preimage(&fes[j as int], &buf2, msg@, coset_spec);
                    };
                    passed_data = Some(msg@);
                }
            }

            let ghost result_snap = result;
            for i in 0..16
                invariant
                    forall|k: int|
                        #![trigger result[k]]
                        0 <= k < i ==> (choice_is_true(ok) ==> result[k] == buf2[(8 + k) as int])
                            && (!choice_is_true(ok) ==> result[k] == result_snap[k]),
                    forall|k: int|
                        #![trigger result[k]]
                        i <= k < 16 ==> result[k] == result_snap[k],
            {
                /* ORIGINAL CODE: result[i] = u8::conditional_select(&result[i], &buf2[8 + i], ok); */
                result[i] = select_u8(&result[i], &buf2[8 + i], ok);
            }

            proof {
                if choice_is_true(ok) {
                    assert(forall|i: int|
                        #![trigger result[i]]
                        0 <= i < 16 ==> result[i] == passed_data.unwrap()[i] as u8) by {
                        assert(forall|i: int|
                            #![trigger msg[i]]
                            0 <= i < 16 ==> msg[i] == buf2[(8 + i) as int]);
                    };
                }
            }

            /* ORIGINAL CODE: n_found += ok.unwrap_u8(); */
            let add: u32 = ok.unwrap_u8() as u32;
            n_found = n_found + add;

            proof {
                // Maintain partial_sha_consistent_count invariant
                assert(n_found as nat == partial_sha_consistent_count(candidates, (j + 1) as int));
            }
        }

        let result = if n_found == 1 {
            Some(result)
        } else {
            None
        };
        proof {
            let x = epa.0;
            let y = epa.1;
            assert(n_found as nat == spec_sha_consistent_count(self.0)) by {
                lemma_partial_count_full(self.0);
            };
            axiom_decode_from_point(self.0, passed_data);
            assert(match result {
                Some(bytes) => ({
                    spec_lizard_decode_ristretto(x, y) == Some(bytes@) && is_lizard_preimage_coset(
                        bytes@,
                        coset_spec,
                    )
                }),
                None => ({ spec_lizard_decode_ristretto(x, y).is_None() }),
            }) by {
                if n_found == 1 {
                    lemma_lizard_decode_ristretto_witness(x, y, passed_data.unwrap());
                } else {
                    lemma_lizard_decode_ristretto_none(x, y);
                }
            };
        }
        result
    }

    /// Directly encode 253 bits as a RistrettoPoint, using Elligator
    // NOTE: This function's body duplicates `from_uniform_bytes_single_elligator`,
    // wrapped in `Some(...)`.  The `data.len() != 32` guard can never trigger
    // because `data` is `&[u8; 32]`, so `None` is unreachable — but we preserve
    // the original upstream code (including the dead branch) per the "never
    // modify original Rust code" rule.
    pub fn encode_253_bits(data: &[u8; 32]) -> (result: Option<RistrettoPoint>)
        ensures
            match result {
                Some(p) => is_well_formed_edwards_point(p.0) && is_in_even_subgroup(p.0)
                    && edwards_point_as_affine(p.0) == spec_elligator_ristretto_flavor(
                    fe51_as_canonical_nat(&spec_fe51_from_bytes(data)),
                ),
                None => false,
            },
    {
        if data.len() != 32 {
            return None;
        }
        let fe = FieldElement::from_bytes(data);
        proof {
            lemma_fe51_limbs_bounded_weaken(&fe, 51, 54);
        }
        let p = RistrettoPoint::elligator_ristretto_flavor(&fe);
        let result = Some(p);
        proof {
            let fe_spec = spec_fe51_from_bytes(data);
            assert(fe51_as_canonical_nat(&fe) == fe51_as_canonical_nat(&fe_spec)) by {
                lemma_from_u8_32_as_nat(data);
                lemma_as_nat_32_mod_255(data);
            }
            assert(spec_elligator_ristretto_flavor(fe51_as_canonical_nat(&fe))
                == spec_elligator_ristretto_flavor(fe51_as_canonical_nat(&fe_spec)));
        }
        result
    }

    /// Directly decode a RistrettoPoint as 253 bits, using Elligator
    ///
    /// Elligator inversion: compute up to 8 field-element preimages of a Ristretto point.
    /// Returns `(mask, candidates)` where bit `j` of `mask` is set iff
    /// `Elligator(candidates[j])` equals `self`.  Used by `lizard_decode_verus`
    /// to find which candidate (if any) has the Lizard `b(m)` structure.
    pub fn decode_253_bits(&self) -> (result: (u8, [[u8; 32]; 8]))
        requires
            is_well_formed_edwards_point(self.0),
        ensures
    // Elligator inversion: each valid candidate maps forward to a coset member of self

            ({
                let (x, y) = edwards_point_as_affine(self.0);
                let coset = ristretto_coset_affine(x, y);
                forall|j: int|
                    #![trigger result.1[j]]
                    0 <= j < 8 && (result.0 & (1u8 << j as u8)) != 0 ==> ({
                        let ej = spec_elligator_ristretto_flavor(
                            fe51_as_canonical_nat(&spec_fe51_from_bytes(&result.1[j])),
                        );
                        ej == coset[0] || ej == coset[1] || ej == coset[2] || ej == coset[3]
                    })
            }),
    {
        let mut ret = [[0u8;32];8];
        let (mask, fes) = self.elligator_ristretto_flavor_inverse();

        for j in 0..8
            invariant
        // `fes == fes` forces Verus to keep `fes` in the loop's proof context;
        // without it the solver cannot reference `fes[k]` in the next invariant.

                fes == fes,
                forall|k: int| #![trigger ret[k]] 0 <= k < j ==> as_bytes_post(&fes[k], &ret[k]),
        {
            ret[j] = fes[j].as_bytes();
        }
        proof {
            assert forall|j: int| #![trigger ret[j]] 0 <= j < 8 implies fe51_as_canonical_nat(
                &spec_fe51_from_bytes(&ret[j]),
            ) == fe51_as_canonical_nat(&fes[j]) by {
                lemma_from_u8_32_as_nat(&ret[j]);
                lemma_as_nat_32_mod_255(&ret[j]);
                lemma_from_bytes_as_bytes_roundtrip(
                    &fes[j],
                    &ret[j],
                    &spec_fe51_from_bytes(&ret[j]),
                );
            };
        }
        (mask, ret)
    }

    /// Return the coset self + E[4], for debugging.
    pub fn xcoset4(&self) -> (result: [EdwardsPoint; 4])
        requires
            is_well_formed_edwards_point(self.0),
        ensures
            is_well_formed_edwards_point(result[0]),
            is_well_formed_edwards_point(result[1]),
            is_well_formed_edwards_point(result[2]),
            is_well_formed_edwards_point(result[3]),
            result[0] == self.0,
            // result = {P, P+T₂, P+T₄, P+T₆}  (self + E[4] coset)
            ({
                let (x, y) = edwards_point_as_affine(self.0);
                let coset = ristretto_coset_affine(x, y);
                edwards_point_as_affine(result[1]) == coset[1] && edwards_point_as_affine(result[2])
                    == coset[2] && edwards_point_as_affine(result[3]) == coset[3]
            }),
    {
        /* ORIGINAL CODE: [self.0, self.0 + constants::EIGHT_TORSION[2], self.0 + constants::EIGHT_TORSION[4], self.0 + constants::EIGHT_TORSION[6]] */
        let t2 = constants::EIGHT_TORSION[2];
        let t4 = constants::EIGHT_TORSION[4];
        let t6 = constants::EIGHT_TORSION[6];
        proof {
            use_type_invariant(t2);
            use_type_invariant(t4);
            use_type_invariant(t6);
            assert(is_well_formed_edwards_point(t2)) by {
                lemma_unfold_edwards(t2);
            }
            assert(is_well_formed_edwards_point(t4)) by {
                lemma_unfold_edwards(t4);
            }
            assert(is_well_formed_edwards_point(t6)) by {
                lemma_unfold_edwards(t6);
            }
        }
        let result = [self.0, &self.0 + &t2, &self.0 + &t4, &self.0 + &t6];
        result
    }

    /// Computes the at most 8 positive FieldElements f such that
    /// self == elligator_ristretto_flavor(f).
    /// Assumes self is even.
    ///
    /// Returns a bitmask of which elements in fes are set.
    pub fn elligator_ristretto_flavor_inverse(&self) -> (result: (u8, [FieldElement; 8]))
        requires
            is_well_formed_edwards_point(self.0),
        ensures
            forall|j: int| 0 <= j < 8 ==> #[trigger] fe51_limbs_bounded(&result.1[j], 52),
            // ∀j with bit j set: elligator(result.1[j]) ∈ coset(self)
            ({
                let (x, y) = edwards_point_as_affine(self.0);
                let coset = ristretto_coset_affine(x, y);
                forall|j: int|
                    #![trigger result.1[j]]
                    0 <= j < 8 && (result.0 & (1u8 << j as u8)) != 0 ==> ({
                        let ej = spec_elligator_ristretto_flavor(
                            fe51_as_canonical_nat(&result.1[j]),
                        );
                        ej == coset[0] || ej == coset[1] || ej == coset[2] || ej == coset[3]
                    })
            }),
            // Spec candidate correspondence: mask bit ↔ spec ok, values match when ok
            ({
                let candidates = spec_lizard_decode_candidates(self.0);
                forall|j: int|
                    #![trigger candidates[j]]
                    0 <= j < 8 ==> (((result.0 & (1u8 << j as u8)) != 0) == candidates[j].0 && (
                    candidates[j].0 ==> fe51_as_canonical_nat(&result.1[j]) == candidates[j].1))
            }),
    {
        // Elligator2 computes a Point from a FieldElement in two steps: first
        // it computes a (s,t) on the Jacobi quartic and then computes the
        // corresponding even point on the Edwards curve.
        //
        // We invert in three steps.  Any Ristretto point has four representatives
        // as even Edwards points.  For each of those even Edwards points,
        // there are two points on the Jacobi quartic that map to it.
        // Each of those eight points on the Jacobi quartic might have an
        // Elligator2 preimage.
        //
        // Essentially we first loop over the four representatives of our point,
        // then for each of them consider both points on the Jacobi quartic and
        // check whether they have an inverse under Elligator2.  We take the
        // following shortcut though.
        //
        // We can compute two Jacobi quartic points for (x,y) and (-x,-y)
        // at the same time.  The four Jacobi quartic points are two of
        // such pairs.
        let mut mask: u8 = 0;
        let jcs = self.to_jacobi_quartic_ristretto();
        let mut ret = [FieldElement::ONE;8];
        let ghost mut bound_shift: u8 = 0;
        let ghost mut slot_ok: Seq<bool> = seq![
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
        ];
        let ghost epa = edwards_point_as_affine(self.0);
        let ghost coset_spec = ristretto_coset_affine(epa.0, epa.1);
        let ghost candidates = spec_lizard_decode_candidates(self.0);

        proof {
            assert((mask as u16) < (1u16 << (bound_shift as u16))) by (bit_vector)
                requires
                    mask == 0u8,
                    bound_shift == 0u8,
            ;
            // Coset membership for all 4 Jacobi points
            assert forall|k: int| #![trigger jcs[k]] 0 <= k < 4 implies ({
                let ji = jacobi_to_edwards_affine(
                    fe51_as_canonical_nat(&jcs[k].S),
                    fe51_as_canonical_nat(&jcs[k].T),
                );
                ji == coset_spec[0] || ji == coset_spec[1] || ji == coset_spec[2] || ji
                    == coset_spec[3]
            }) by {
                let _ = coset_spec[k];
            };
        }

        for i in 0..4
            invariant
                forall|k: int|
                    #![trigger ret[k]]
                    0 <= k < 2 * i ==> fe51_limbs_bounded(&ret[k], 52),
                forall|k: int|
                    0 <= k < 4 ==> #[trigger] fe51_limbs_bounded(&jcs[k].S, 52)
                        && fe51_limbs_bounded(&jcs[k].T, 52),
                // Coset membership for all 4 Jacobi points (immutable, trivially maintained)
                forall|k: int|
                    #![trigger jcs[k]]
                    0 <= k < 4 ==> ({
                        let ji = jacobi_to_edwards_affine(
                            fe51_as_canonical_nat(&jcs[k].S),
                            fe51_as_canonical_nat(&jcs[k].T),
                        );
                        ji == coset_spec[0] || ji == coset_spec[1] || ji == coset_spec[2] || ji
                            == coset_spec[3]
                    }),
                bound_shift == (2 * i) as u8,
                bound_shift <= 8,
                (mask as u16) < (1u16 << (bound_shift as u16)),
                slot_ok.len() == 8,
                forall|k: int|
                    #![trigger slot_ok[k]]
                    0 <= k < 2 * i ==> slot_ok[k] == mask_bit(mask, k),
                // Correctness: processed slots that are flagged map to coset members
                forall|j: int|
                    #![trigger ret[j]]
                    0 <= j < 2 * i ==> (slot_ok[j] ==> is_slot_in_coset(
                        fe51_as_canonical_nat(&ret[j]),
                        coset_spec,
                    )),
                // JQ spec equality (frame from to_jacobi_quartic_ristretto ensures)
                forall|k: int|
                    #![trigger jcs[k]]
                    0 <= k < 4 ==> spec_to_jacobi_quartic_ristretto(self.0)[k] == (
                        fe51_as_canonical_nat(&jcs[k].S),
                        fe51_as_canonical_nat(&jcs[k].T),
                    ),
                // Candidates binding (frame)
                candidates == spec_lizard_decode_candidates(self.0),
                // Spec candidate correspondence for processed slots
                forall|k: int|
                    #![trigger candidates[k]]
                    0 <= k < 2 * i ==> (slot_ok[k] == candidates[k].0 && (candidates[k].0
                        ==> fe51_as_canonical_nat(&ret[k]) == candidates[k].1)),
        {
            proof {
                assert(fe51_limbs_bounded(&jcs[i as int].S, 52));
                assert(fe51_limbs_bounded(&jcs[i as int].T, 52));
                lemma_fe51_limbs_bounded_weaken(&jcs[i as int].S, 52, 54);
                lemma_fe51_limbs_bounded_weaken(&jcs[i as int].T, 52, 54);
            }
            let (ok, fe) = jcs[i].elligator_inv();
            let mut tmp: u8 = 0;
            ret[2 * i] = fe;
            /* ORIGINAL CODE: tmp.conditional_assign(&1, ok); */
            conditional_assign_generic(&mut tmp, &1u8, ok);
            let ghost old_mask_even = mask;
            let pos_even: u8 = (2 * i) as u8;
            /* ORIGINAL CODE: mask |= tmp << (2 * i); */
            mask |= tmp << pos_even;

            proof {
                lemma_mask_or_bound(old_mask_even, tmp, pos_even);
                bound_shift = (bound_shift + 1) as u8;
                let ghost old_slot_even = slot_ok;
                slot_ok = slot_ok.update(2 * i as int, choice_is_true(ok));

                lemma_mask_bound_implies_bit_clean(old_mask_even, pos_even, pos_even);
                lemma_or_bit_all(old_mask_even, tmp, pos_even);

                if choice_is_true(ok) {
                    let s_i = fe51_as_canonical_nat(&jcs[i as int].S);
                    let t_i = fe51_as_canonical_nat(&jcs[i as int].T);
                    assert(jcs[i as int] == jcs[i as int]);  // trigger
                    lemma_even_is_slot_in_coset(
                        fe51_as_canonical_nat(&ret[2 * i as int]),
                        s_i,
                        t_i,
                        coset_spec,
                    );
                }
                // Even slot spec correspondence

                {
                    lemma_candidate_from_jq_spec(self.0);
                    let s_i = fe51_as_canonical_nat(&jcs[i as int].S);
                    let t_i = fe51_as_canonical_nat(&jcs[i as int].T);
                    assert(spec_to_jacobi_quartic_ristretto(self.0)[i as int] == (s_i, t_i));
                    assert(candidates[2 * i as int] == spec_elligator_inv(s_i, t_i));
                    assert(choice_is_true(ok) == spec_elligator_inv(s_i, t_i).0);
                    assert(slot_ok[2 * i as int] == candidates[2 * i as int].0);
                    if candidates[2 * i as int].0 {
                        assert(fe51_as_canonical_nat(&ret[2 * i as int]) == candidates[2
                            * i as int].1);
                    }
                }
            }

            let jc = jcs[i].dual();
            let (ok, fe) = jc.elligator_inv();
            let mut tmp: u8 = 0;
            ret[2 * i + 1] = fe;
            /* ORIGINAL CODE: tmp.conditional_assign(&1, ok); */
            conditional_assign_generic(&mut tmp, &1u8, ok);
            let ghost old_mask_odd = mask;
            let pos_odd: u8 = (2 * i + 1) as u8;
            /* ORIGINAL CODE: mask |= tmp << (2 * i + 1); */
            mask |= tmp << pos_odd;

            proof {
                lemma_mask_or_bound(old_mask_odd, tmp, pos_odd);
                bound_shift = (bound_shift + 1) as u8;
                let ghost old_slot_odd = slot_ok;
                slot_ok = slot_ok.update((2 * i + 1) as int, choice_is_true(ok));

                lemma_mask_bound_implies_bit_clean(old_mask_odd, pos_odd, pos_odd);
                lemma_or_bit_all(old_mask_odd, tmp, pos_odd);

                if choice_is_true(ok) {
                    let s_i = fe51_as_canonical_nat(&jcs[i as int].S);
                    let t_i = fe51_as_canonical_nat(&jcs[i as int].T);
                    assert(jcs[i as int] == jcs[i as int]);  // trigger
                    lemma_odd_is_slot_in_coset(
                        fe51_as_canonical_nat(&ret[(2 * i + 1) as int]),
                        fe51_as_canonical_nat(&jc.S),
                        fe51_as_canonical_nat(&jc.T),
                        s_i,
                        t_i,
                        coset_spec,
                    );
                }
                // Odd slot spec correspondence

                {
                    lemma_candidate_from_jq_spec(self.0);
                    let s_i = fe51_as_canonical_nat(&jcs[i as int].S);
                    let t_i = fe51_as_canonical_nat(&jcs[i as int].T);
                    let ns_i = fe51_as_canonical_nat(&jc.S);
                    let nt_i = fe51_as_canonical_nat(&jc.T);
                    assert(ns_i == field_neg(s_i));
                    assert(nt_i == field_neg(t_i));
                    assert(candidates[(2 * i + 1) as int] == spec_elligator_inv(
                        field_neg(s_i),
                        field_neg(t_i),
                    ));
                    assert(choice_is_true(ok) == spec_elligator_inv(ns_i, nt_i).0);
                    assert(slot_ok[(2 * i + 1) as int] == candidates[(2 * i + 1) as int].0);
                    if candidates[(2 * i + 1) as int].0 {
                        assert(fe51_as_canonical_nat(&ret[(2 * i + 1) as int]) == candidates[(2 * i
                            + 1) as int].1);
                    }
                }
            }
        }

        let result = (mask, ret);
        proof {
            // Reveal per-slot correctness to obtain the coset postcondition
            assert(forall|j: int|
                #![trigger result.1[j]]
                0 <= j < 8 && (result.0 & (1u8 << j as u8)) != 0 ==> ({
                    let ej = spec_elligator_ristretto_flavor(fe51_as_canonical_nat(&result.1[j]));
                    ej == coset_spec[0] || ej == coset_spec[1] || ej == coset_spec[2] || ej
                        == coset_spec[3]
                })) by {
                reveal(is_slot_in_coset);
            };

            // Spec candidate correspondence from loop invariant (2*4 == 8 slots)
            assert(forall|j: int|
                #![trigger candidates[j]]
                0 <= j < 8 ==> (((result.0 & (1u8 << j as u8)) != 0) == candidates[j].0 && (
                candidates[j].0 ==> fe51_as_canonical_nat(&result.1[j]) == candidates[j].1)));
        }
        result
    }

    /// Find a point on the Jacobi quartic associated to each of the four
    /// points Ristretto equivalent to self.
    ///
    /// There is one exception: for (0,-1) there is no point on the quartic and
    /// so we repeat one on the quartic equivalent to (0,1).
    /// **Contract note:** The ensures now exposes both the coset-membership
    /// disjunctions (for callers that only need geometric correctness) and the
    /// per-element equality with `spec_to_jacobi_quartic_ristretto` (for
    /// `elligator_ristretto_flavor_inverse` to prove spec candidate correspondence).
    /// Since `spec_to_jacobi_quartic_ristretto` is opaque, the equality term is
    /// inert for callers that do not reveal or index into it.
    fn to_jacobi_quartic_ristretto(self) -> (result: [JacobiPoint; 4])
        requires
            is_well_formed_edwards_point(self.0),
        ensures
            forall|i: int|
                0 <= i < 4 ==> #[trigger] fe51_limbs_bounded(&result[i].S, 52)
                    && fe51_limbs_bounded(&result[i].T, 52),
            // Each JQ point maps to some coset member (disjunction)
            ({
                let (x, y) = edwards_point_as_affine(self.0);
                let coset = ristretto_coset_affine(x, y);
                forall|i: int|
                    #![trigger coset[i]]
                    0 <= i < 4 ==> ({
                        let ji = jacobi_to_edwards_affine(
                            fe51_as_canonical_nat(&result[i].S),
                            fe51_as_canonical_nat(&result[i].T),
                        );
                        ji == coset[0] || ji == coset[1] || ji == coset[2] || ji == coset[3]
                    })
            }),
            // Per-element equality with spec_to_jacobi_quartic_ristretto
            ({
                let spec_jcs = spec_to_jacobi_quartic_ristretto(self.0);
                &&& spec_jcs[0] == (
                    fe51_as_canonical_nat(&result[0].S),
                    fe51_as_canonical_nat(&result[0].T),
                )
                &&& spec_jcs[1] == (
                    fe51_as_canonical_nat(&result[1].S),
                    fe51_as_canonical_nat(&result[1].T),
                )
                &&& spec_jcs[2] == (
                    fe51_as_canonical_nat(&result[2].S),
                    fe51_as_canonical_nat(&result[2].T),
                )
                &&& spec_jcs[3] == (
                    fe51_as_canonical_nat(&result[3].S),
                    fe51_as_canonical_nat(&result[3].T),
                )
            }),
    {
        proof {
            assert(edwards_x(self.0) == self.0.X && edwards_y(self.0) == self.0.Y && edwards_z(
                self.0,
            ) == self.0.Z && edwards_t(self.0) == self.0.T) by {
                lemma_unfold_edwards(self.0);
            };
            assert(fe51_limbs_bounded(&self.0.X, 54) && fe51_limbs_bounded(&self.0.Y, 54)
                && fe51_limbs_bounded(&self.0.Z, 54) && fe51_limbs_bounded(&self.0.T, 54)) by {
                lemma_edwards_point_weaken_to_54(&self.0);
            };
        }
        let x2 = self.0.X.square();  // X²
        let y2 = self.0.Y.square();  // Y²
        let y4 = y2.square();  // Y⁴
        let z2 = self.0.Z.square();  // Z²
        let z_min_y = &self.0.Z - &self.0.Y;  // Z - Y
        proof {
            assert(sum_of_limbs_bounded(&self.0.Z, &self.0.Y, u64::MAX)) by {
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&self.0.Z, &self.0.Y, 52);
            };
        }
        let z_pl_y = &self.0.Z + &self.0.Y;  // Z + Y
        let z2_min_y2 = &z2 - &y2;  // Z² - Y²

        // gamma = 1/sqrt(Y⁴ · X² · (Z² - Y²))
        let gamma_arg = &(&y4 * &x2) * &z2_min_y2;
        let (gamma_sq, gamma) = gamma_arg.invsqrt();

        proof {
            assert(fe51_limbs_bounded(&gamma, 54)) by {
                lemma_fe51_limbs_bounded_weaken(&gamma, 52, 54);
            };
        }
        let den1 = &gamma * &y2;

        let s_over_x = &den1 * &z_min_y;
        proof {
            assert(fe51_limbs_bounded(&z_pl_y, 54)) by {
                lemma_fe51_limbs_bounded_weaken(&z_pl_y, 53, 54);
            };
        }
        let sp_over_xp = &den1 * &z_pl_y;

        let s0 = &s_over_x * &self.0.X;
        /* ORIGINAL CODE: let s1 = &(-(&sp_over_xp)) * &self.0.X; */
        let neg_sp_over_xp = negate_field_element(&sp_over_xp);
        let s1 = &neg_sp_over_xp * &self.0.X;

        proof {
            assert(fe51_limbs_bounded(&lizard_constants::MDOUBLE_INVSQRT_A_MINUS_D, 54)) by {
                lemma_mdouble_invsqrt_a_minus_d_bounded_51();
                lemma_fe51_limbs_bounded_weaken(
                    &lizard_constants::MDOUBLE_INVSQRT_A_MINUS_D,
                    51,
                    54,
                );
            };
        }
        // t_0 = -2/sqrt(-d-1) · Z · sOverX
        // t_1 = -2/sqrt(-d-1) · Z · spOverXp
        let tmp1 = &lizard_constants::MDOUBLE_INVSQRT_A_MINUS_D * &self.0.Z;
        let mut t0 = &tmp1 * &s_over_x;
        let mut t1 = &tmp1 * &sp_over_xp;

        // den2 = -1/sqrt(1+d) · (Y² - Z²) · gamma
        /* ORIGINAL CODE: let den = &(&(-(&z2_min_y2)) * &lizard_constants::MINVSQRT_ONE_PLUS_D) * &gamma; */
        proof {
            assert(fe51_limbs_bounded(&lizard_constants::MINVSQRT_ONE_PLUS_D, 54)) by {
                lemma_minvsqrt_one_plus_d_bounded_51();
                lemma_fe51_limbs_bounded_weaken(&lizard_constants::MINVSQRT_ONE_PLUS_D, 51, 54);
            };
        }
        let neg_z2_min_y2 = negate_field_element(&z2_min_y2);
        let den2 = &(&neg_z2_min_y2 * &lizard_constants::MINVSQRT_ONE_PLUS_D) * &gamma;

        // Dual computation under (X, Y, Z) → (Y, X, iZ)
        proof {
            assert(fe51_limbs_bounded(&constants::SQRT_M1, 54)) by {
                lemma_sqrt_m1_limbs_bounded();
            };
        }
        let iz = &constants::SQRT_M1 * &self.0.Z;  // iZ
        let iz_min_x = &iz - &self.0.X;  // iZ - X
        proof {
            assert(sum_of_limbs_bounded(&iz, &self.0.X, u64::MAX)) by {
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&iz, &self.0.X, 52);
            };
        }
        let iz_pl_x = &iz + &self.0.X;  // iZ + X

        let s_over_y = &den2 * &iz_min_x;
        proof {
            assert(fe51_limbs_bounded(&iz_pl_x, 54)) by {
                lemma_fe51_limbs_bounded_weaken(&iz_pl_x, 53, 54);
            };
        }
        let sp_over_yp = &den2 * &iz_pl_x;

        let mut s2 = &s_over_y * &self.0.Y;
        /* ORIGINAL CODE: let mut s3 = &(-(&sp_over_yp)) * &self.0.Y; */
        let neg_sp_over_yp = negate_field_element(&sp_over_yp);
        let mut s3 = &neg_sp_over_yp * &self.0.Y;

        // t_2 = -2/sqrt(-d-1) · iZ · sOverY
        // t_3 = -2/sqrt(-d-1) · iZ · spOverYp
        let tmp2 = &lizard_constants::MDOUBLE_INVSQRT_A_MINUS_D * &iz;
        let mut t2 = &tmp2 * &s_over_y;
        let mut t3 = &tmp2 * &sp_over_yp;

        // Special case: X=0 or Y=0.  Then return
        //
        //  (0,1)   (1,-2i/sqrt(-d-1)   (-1,-2i/sqrt(-d-1))
        //
        // Note that if X=0 or Y=0, then s_i = t_i = 0.
        proof {
            assert(fe51_limbs_bounded(&FieldElement::ONE, 52) && fe51_limbs_bounded(
                &lizard_constants::MIDOUBLE_INVSQRT_A_MINUS_D,
                52,
            )) by {
                lemma_one_limbs_bounded_51();
                lemma_fe51_limbs_bounded_weaken(&FieldElement::ONE, 51, 52);
                lemma_midouble_invsqrt_a_minus_d_bounded_51();
                lemma_fe51_limbs_bounded_weaken(
                    &lizard_constants::MIDOUBLE_INVSQRT_A_MINUS_D,
                    51,
                    52,
                );
            };
        }
        /* ORIGINAL CODE: let x_or_y_is_zero = self.0.X.is_zero() | self.0.Y.is_zero(); */
        let x_or_y_is_zero = choice_or(self.0.X.is_zero(), self.0.Y.is_zero());
        let ghost t0_pre = t0;
        let ghost t1_pre = t1;
        let ghost t2_pre = t2;
        let ghost t3_pre = t3;
        let ghost s2_pre = s2;
        let ghost s3_pre = s3;
        /* ORIGINAL CODE: t0.conditional_assign(&FieldElement::ONE, x_or_y_is_zero); */
        conditional_assign_generic(&mut t0, &FieldElement::ONE, x_or_y_is_zero);
        /* ORIGINAL CODE: t1.conditional_assign(&FieldElement::ONE, x_or_y_is_zero); */
        conditional_assign_generic(&mut t1, &FieldElement::ONE, x_or_y_is_zero);
        /* ORIGINAL CODE: t2.conditional_assign(&MIDOUBLE_INVSQRT_A_MINUS_D, x_or_y_is_zero); */
        conditional_assign_generic(
            &mut t2,
            &lizard_constants::MIDOUBLE_INVSQRT_A_MINUS_D,
            x_or_y_is_zero,
        );
        /* ORIGINAL CODE: t3.conditional_assign(&MIDOUBLE_INVSQRT_A_MINUS_D, x_or_y_is_zero); */
        conditional_assign_generic(
            &mut t3,
            &lizard_constants::MIDOUBLE_INVSQRT_A_MINUS_D,
            x_or_y_is_zero,
        );
        /* ORIGINAL CODE: s2.conditional_assign(&FieldElement::ONE, x_or_y_is_zero); */
        conditional_assign_generic(&mut s2, &FieldElement::ONE, x_or_y_is_zero);
        /* ORIGINAL CODE: s3.conditional_assign(&(-(&FieldElement::ONE)), x_or_y_is_zero); */
        let minus_one = negate_field_element(&FieldElement::ONE);
        conditional_assign_generic(&mut s3, &minus_one, x_or_y_is_zero);

        /* ORIGINAL CODE: direct return [JacobiPoint{S: s0, T: t0}, ...] -- restructured to insert proof block */
        let result = [
            JacobiPoint { S: s0, T: t0 },
            JacobiPoint { S: s1, T: t1 },
            JacobiPoint { S: s2, T: t2 },
            JacobiPoint { S: s3, T: t3 },
        ];
        proof {
            let s0n = fe51_as_canonical_nat(&s0);
            let t0n = fe51_as_canonical_nat(&t0);
            let s1n = fe51_as_canonical_nat(&s1);
            let t1n = fe51_as_canonical_nat(&t1);
            let s2n = fe51_as_canonical_nat(&s2);
            let t2n = fe51_as_canonical_nat(&t2);
            let s3n = fe51_as_canonical_nat(&s3);
            let t3n = fe51_as_canonical_nat(&t3);

            // Exec-to-spec bridge (all intermediates scoped here)
            assert(spec_to_jacobi_quartic_ristretto(self.0) == [
                (s0n, t0n),
                (s1n, t1n),
                (s2n, t2n),
                (s3n, t3n),
            ]) by {
                let xn = fe51_as_canonical_nat(&self.0.X);
                let yn = fe51_as_canonical_nat(&self.0.Y);
                let zn = fe51_as_canonical_nat(&self.0.Z);
                let gamma_nat = fe51_as_canonical_nat(&gamma);
                let gamma_arg_nat = fe51_as_canonical_nat(&gamma_arg);

                assert(fe51_as_canonical_nat(&x2) == field_square(xn)) by {
                    lemma_square_matches_field_square(fe51_as_nat(&self.0.X), fe51_as_nat(&x2));
                };
                assert(fe51_as_canonical_nat(&y2) == field_square(yn)) by {
                    lemma_square_matches_field_square(fe51_as_nat(&self.0.Y), fe51_as_nat(&y2));
                };
                assert(fe51_as_canonical_nat(&y4) == field_square(fe51_as_canonical_nat(&y2))) by {
                    lemma_square_matches_field_square(fe51_as_nat(&y2), fe51_as_nat(&y4));
                };
                assert(fe51_as_canonical_nat(&z2) == field_square(zn)) by {
                    lemma_square_matches_field_square(fe51_as_nat(&self.0.Z), fe51_as_nat(&z2));
                };
                let one_nat = fe51_as_canonical_nat(&FieldElement::ONE);
                assert(one_nat == 1) by {
                    lemma_one_field_element_value();
                };
                assert(gamma_nat < p()) by {
                    lemma_canonical_nat_lt_p(&gamma);
                };
                assert(gamma_arg_nat < p()) by {
                    lemma_canonical_nat_lt_p(&gamma_arg);
                };
                assert(gamma_nat == nat_invsqrt(gamma_arg_nat)) by {
                    lemma_invsqrt_bridge(
                        gamma_arg_nat,
                        gamma_nat,
                        choice_is_true(gamma_sq),
                        one_nat,
                    );
                };
                assert(choice_is_true(x_or_y_is_zero) == (xn == 0 || yn == 0)) by {
                    lemma_is_zero_iff_canonical_nat_zero(self.0.X);
                    lemma_is_zero_iff_canonical_nat_zero(self.0.Y);
                };
                reveal(spec_to_jacobi_quartic_ristretto);
            };

            // result[i] ↔ nat values
            assert(fe51_as_canonical_nat(&result[0].S) == s0n && fe51_as_canonical_nat(&result[0].T)
                == t0n);
            assert(fe51_as_canonical_nat(&result[1].S) == s1n && fe51_as_canonical_nat(&result[1].T)
                == t1n);
            assert(fe51_as_canonical_nat(&result[2].S) == s2n && fe51_as_canonical_nat(&result[2].T)
                == t2n);
            assert(fe51_as_canonical_nat(&result[3].S) == s3n && fe51_as_canonical_nat(&result[3].T)
                == t3n);

            // Per-element spec equality (bridges array equality to result form)
            let spec_jcs = spec_to_jacobi_quartic_ristretto(self.0);
            assert(spec_jcs[0] == (
                fe51_as_canonical_nat(&result[0].S),
                fe51_as_canonical_nat(&result[0].T),
            ));
            assert(spec_jcs[1] == (
                fe51_as_canonical_nat(&result[1].S),
                fe51_as_canonical_nat(&result[1].T),
            ));
            assert(spec_jcs[2] == (
                fe51_as_canonical_nat(&result[2].S),
                fe51_as_canonical_nat(&result[2].T),
            ));
            assert(spec_jcs[3] == (
                fe51_as_canonical_nat(&result[3].S),
                fe51_as_canonical_nat(&result[3].T),
            ));

            // Coset correctness from spinoff
            lemma_coset_bridge(self.0, s0n, t0n, s1n, t1n, s2n, t2n, s3n, t3n);
        }
        result
    }
}

} // verus!
// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------
#[cfg(test)]
mod test {

    use sha2;

    use self::sha2::Sha256;
    use super::*;
    use crate::ristretto::CompressedRistretto;
    use rand_core::RngCore;
    #[cfg(feature = "rand")]
    use rand_os::OsRng;
    use subtle::ConditionallySelectable;
    use subtle::ConstantTimeEq;

    fn test_lizard_encode_helper(data: &[u8; 16], result: &[u8; 32]) {
        let p = RistrettoPoint::lizard_encode::<Sha256>(data);
        let p_bytes = p.compress().to_bytes();
        assert!(&p_bytes == result);
        let p = CompressedRistretto::from_slice(&p_bytes)
            .unwrap()
            .decompress()
            .unwrap();
        let data_out = p.lizard_decode::<Sha256>().unwrap();
        assert!(&data_out == data);
    }

    #[test]
    fn test_lizard_encode() {
        test_lizard_encode_helper(
            &[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            &[
                0xf0, 0xb7, 0xe3, 0x44, 0x84, 0xf7, 0x4c, 0xf0, 0xf, 0x15, 0x2, 0x4b, 0x73, 0x85,
                0x39, 0x73, 0x86, 0x46, 0xbb, 0xbe, 0x1e, 0x9b, 0xc7, 0x50, 0x9a, 0x67, 0x68, 0x15,
                0x22, 0x7e, 0x77, 0x4f,
            ],
        );

        test_lizard_encode_helper(
            &[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
            &[
                0xcc, 0x92, 0xe8, 0x1f, 0x58, 0x5a, 0xfc, 0x5c, 0xaa, 0xc8, 0x86, 0x60, 0xd8, 0xd1,
                0x7e, 0x90, 0x25, 0xa4, 0x44, 0x89, 0xa3, 0x63, 0x4, 0x21, 0x23, 0xf6, 0xaf, 0x7,
                0x2, 0x15, 0x6e, 0x65,
            ],
        );

        test_lizard_encode_helper(
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
            &[
                0xc8, 0x30, 0x57, 0x3f, 0x8a, 0x8e, 0x77, 0x78, 0x67, 0x1f, 0x76, 0xcd, 0xc7, 0x96,
                0xdc, 0xa, 0x23, 0x5c, 0xf1, 0x77, 0xf1, 0x97, 0xd9, 0xfc, 0xba, 0x6, 0xe8, 0x4e,
                0x96, 0x24, 0x74, 0x44,
            ],
        );
    }

    #[test]
    fn test_elligator_inv() {
        let mut rng = rand::thread_rng();

        for i in 0..100 {
            let mut fe_bytes = [0u8; 32];

            if i == 0 {
                // Test for first corner-case: fe = 0
                fe_bytes = [0u8; 32];
            } else if i == 1 {
                // Test for second corner-case: fe = +sqrt(i*d)
                fe_bytes = [
                    168, 27, 92, 74, 203, 42, 48, 117, 170, 109, 234, 14, 45, 169, 188, 205, 21,
                    110, 235, 115, 153, 84, 52, 117, 151, 235, 123, 244, 88, 85, 179, 5,
                ];
            } else {
                // For the rest, just generate a random field element to test.
                rng.fill_bytes(&mut fe_bytes);
            }
            fe_bytes[0] &= 254; // positive
            fe_bytes[31] &= 127; // < 2^255-19
            let fe = FieldElement::from_bytes(&fe_bytes);

            let pt = RistrettoPoint::elligator_ristretto_flavor(&fe);
            for pt2 in &pt.xcoset4() {
                let (mask, fes) = RistrettoPoint(*pt2).elligator_ristretto_flavor_inverse();

                let mut found = false;
                for (j, fe_j) in fes.iter().enumerate() {
                    if mask & (1 << j) != 0 {
                        assert_eq!(RistrettoPoint::elligator_ristretto_flavor(fe_j), pt);
                        if *fe_j == fe {
                            found = true;
                        }
                    }
                }
                assert!(found);
            }
        }
    }

    /// Runtime validation for `lemma_elligator_inv_algebraic`.
    ///
    /// Explicitly exercises all three branches of `spec_elligator_inv`:
    ///   - Branch 1a: s=0, t=1 (identity) → returns sqrt(i·d)
    ///   - Branch 1b: s=0, t=−1 (identity coset partner) → returns 0
    ///   - Branch 2: s≠0, square case → main inversion succeeds
    ///   - Branch 3: s≠0, non-square case → inversion fails
    /// Tracks per-branch hit counts and asserts minimum coverage.
    #[test]
    fn test_axiom_elligator_inv_roundtrip() {
        use core::ops::Neg;
        let mut rng = rand::thread_rng();
        let mut branch_1a_hits = 0u32; // s=0, t=1
        let mut branch_1b_hits = 0u32; // s=0, t=-1
        let mut branch_2_hits = 0u32; // s!=0, success (square case)
        let mut branch_3_hits = 0u32; // s!=0, failure (non-square)
        let mut dual_success_count = 0u32;

        let zero = FieldElement::ZERO;
        let one = FieldElement::ONE;
        let minus_one = Neg::neg(&one);

        // ---- Explicit Branch 1a: s=0, t=1 (identity point) ----
        {
            let jc = JacobiPoint { S: zero, T: one };
            let (ok, inv_fe) = jc.elligator_inv();
            assert!(bool::from(ok), "Branch 1a (s=0,t=1): must succeed");
            let round_trip = RistrettoPoint::elligator_ristretto_flavor(&inv_fe);
            let (ex, ey) = jacobi_to_edwards_exec(&zero, &one);
            assert!(
                affine_eq(&round_trip.0, &ex, &ey),
                "Branch 1a: round-trip must recover the same Edwards point"
            );
            branch_1a_hits += 1;
        }

        // ---- Explicit Branch 1b: s=0, t=-1 (identity coset partner) ----
        {
            let jc = JacobiPoint {
                S: zero,
                T: minus_one,
            };
            let (ok, inv_fe) = jc.elligator_inv();
            assert!(bool::from(ok), "Branch 1b (s=0,t=-1): must succeed");
            assert!(fe_eq(&inv_fe, &zero), "Branch 1b: returned r must be 0");
            let round_trip = RistrettoPoint::elligator_ristretto_flavor(&inv_fe);
            let (ex, ey) = jacobi_to_edwards_exec(&zero, &minus_one);
            assert!(
                affine_eq(&round_trip.0, &ex, &ey),
                "Branch 1b: round-trip must recover the same Edwards point"
            );
            branch_1b_hits += 1;
        }

        // ---- Random points: exercise branches 2 and 3, plus duals ----
        for i in 0..300 {
            let mut fe_bytes = [0u8; 32];
            if i == 0 {
                fe_bytes = [0u8; 32];
            } else if i == 1 {
                fe_bytes[0] = 1;
            } else if i == 2 {
                // sqrt(i*d) bytes — known to exercise branch 1a via forward map
                fe_bytes = [
                    168, 27, 92, 74, 203, 42, 48, 117, 170, 109, 234, 14, 45, 169, 188, 205, 21,
                    110, 235, 115, 153, 84, 52, 117, 151, 235, 123, 244, 88, 85, 179, 5,
                ];
            } else {
                rng.fill_bytes(&mut fe_bytes);
            }
            fe_bytes[0] &= 254;
            fe_bytes[31] &= 127;
            let fe = FieldElement::from_bytes(&fe_bytes);
            let pt = RistrettoPoint::elligator_ristretto_flavor(&fe);

            let jcs = RistrettoPoint(pt.0).to_jacobi_quartic_ristretto();

            for jc in &jcs {
                let s_is_zero = jc.S.as_bytes() == [0u8; 32];
                let t_is_one = fe_eq(&jc.T, &one);
                let t_is_minus_one = fe_eq(&jc.T, &minus_one);

                // Test the Jacobi point itself
                let (ok, inv_fe) = jc.elligator_inv();
                if ok.into() {
                    let round_trip = RistrettoPoint::elligator_ristretto_flavor(&inv_fe);
                    assert_eq!(
                        round_trip, pt,
                        "Round-trip failed for Jacobi point (i={})",
                        i
                    );

                    if s_is_zero && t_is_one {
                        branch_1a_hits += 1;
                    } else if s_is_zero && t_is_minus_one {
                        branch_1b_hits += 1;
                    } else {
                        branch_2_hits += 1;
                    }
                } else {
                    assert!(
                        !s_is_zero,
                        "s=0 should always succeed, but failed (i={})",
                        i
                    );
                    branch_3_hits += 1;
                }

                // Test the dual (-S, -T)
                let dual = jc.dual();
                let (ok_d, inv_fe_d) = dual.elligator_inv();
                if ok_d.into() {
                    let round_trip_d = RistrettoPoint::elligator_ristretto_flavor(&inv_fe_d);
                    assert_eq!(
                        round_trip_d, pt,
                        "Round-trip failed for dual Jacobi point (i={})",
                        i
                    );
                    dual_success_count += 1;
                }
            }
        }

        // Minimum coverage assertions
        assert!(
            branch_1a_hits >= 1,
            "Branch 1a (s=0,t=1) never hit: {branch_1a_hits}"
        );
        assert!(
            branch_1b_hits >= 1,
            "Branch 1b (s=0,t=-1) never hit: {branch_1b_hits}"
        );
        assert!(
            branch_2_hits >= 100,
            "Branch 2 (s!=0, success) too few hits: {branch_2_hits}"
        );
        assert!(
            branch_3_hits >= 10,
            "Branch 3 (s!=0, failure) too few hits: {branch_3_hits}"
        );
        assert!(
            dual_success_count >= 50,
            "Too few dual successes: {dual_success_count}"
        );

        eprintln!(
            "Branch coverage: 1a={}, 1b={}, 2(success)={}, 3(failure)={}, duals={}",
            branch_1a_hits, branch_1b_hits, branch_2_hits, branch_3_hits, dual_success_count
        );
    }

    fn jacobi_to_edwards_exec(s: &FieldElement, t: &FieldElement) -> (FieldElement, FieldElement) {
        let s_sq = s.square();
        let one = FieldElement::ONE;
        let y_num = &one - &s_sq;
        let y_den = &one + &s_sq;
        let y = &y_num * &y_den.invert();
        let two = &FieldElement::ONE + &FieldElement::ONE;
        let two_s = &two * s;
        let t_sqrt_ad_m1 = t * &constants::SQRT_AD_MINUS_ONE;
        let x = &two_s * &t_sqrt_ad_m1.invert();
        (x, y)
    }

    fn fe_eq(a: &FieldElement, b: &FieldElement) -> bool {
        a.as_bytes() == b.as_bytes()
    }

    fn affine_eq(p: &EdwardsPoint, x: &FieldElement, y: &FieldElement) -> bool {
        fe_eq(&(&p.X * &p.Z.invert()), x) && fe_eq(&(&p.Y * &p.Z.invert()), y)
    }

    /// Runtime validation for `axiom_jacobi_quartic_birational_pair01`.
    ///
    /// For random Ristretto points, converts to Jacobi quartic and
    /// checks that JQ[0] maps to coset[0] and JQ[1] maps to coset[2].
    #[test]
    fn test_axiom_birational_pair01() {
        let mut rng = rand::thread_rng();
        let mut checked = 0u32;

        for i in 0..500 {
            let mut bytes = [0u8; 32];
            if i == 0 {
                bytes = [0u8; 32];
            } else {
                rng.fill_bytes(&mut bytes);
            }
            bytes[0] &= 254;
            bytes[31] &= 127;
            let fe = FieldElement::from_bytes(&bytes);
            let pt = RistrettoPoint::elligator_ristretto_flavor(&fe);
            let coset = pt.xcoset4();
            let jcs = RistrettoPoint(pt.0).to_jacobi_quartic_ristretto();

            let x_aff = &pt.0.X * &pt.0.Z.invert();
            let y_aff = &pt.0.Y * &pt.0.Z.invert();
            if x_aff == FieldElement::ZERO || y_aff == FieldElement::ZERO {
                continue;
            }

            let (x0, y0) = jacobi_to_edwards_exec(&jcs[0].S, &jcs[0].T);
            let (x1, y1) = jacobi_to_edwards_exec(&jcs[1].S, &jcs[1].T);

            assert!(
                affine_eq(&coset[0], &x0, &y0),
                "Birational: JQ[0] doesn't map to coset[0] (i={i})"
            );
            assert!(
                affine_eq(&coset[2], &x1, &y1),
                "Birational: JQ[1] doesn't map to coset[2] (i={i})"
            );
            checked += 1;
        }
        assert!(
            checked > 400,
            "Too few non-degenerate points tested: {checked}"
        );
    }

    /// Runtime validation for `axiom_jacobi_quartic_torsion_pair23`.
    ///
    /// For random Ristretto points, converts to Jacobi quartic and
    /// checks that JQ[2] maps to coset[1] and JQ[3] maps to coset[3].
    #[test]
    fn test_axiom_torsion_pair23() {
        let mut rng = rand::thread_rng();
        let mut checked = 0u32;

        for i in 0..500 {
            let mut bytes = [0u8; 32];
            if i == 0 {
                bytes = [0u8; 32];
            } else {
                rng.fill_bytes(&mut bytes);
            }
            bytes[0] &= 254;
            bytes[31] &= 127;
            let fe = FieldElement::from_bytes(&bytes);
            let pt = RistrettoPoint::elligator_ristretto_flavor(&fe);
            let coset = pt.xcoset4();
            let jcs = RistrettoPoint(pt.0).to_jacobi_quartic_ristretto();

            let x_aff = &pt.0.X * &pt.0.Z.invert();
            let y_aff = &pt.0.Y * &pt.0.Z.invert();
            if x_aff == FieldElement::ZERO || y_aff == FieldElement::ZERO {
                continue;
            }

            let (x2, y2) = jacobi_to_edwards_exec(&jcs[2].S, &jcs[2].T);
            let (x3, y3) = jacobi_to_edwards_exec(&jcs[3].S, &jcs[3].T);

            assert!(
                affine_eq(&coset[1], &x2, &y2),
                "Torsion: JQ[2] doesn't map to coset[1] (i={i})"
            );
            assert!(
                affine_eq(&coset[3], &x3, &y3),
                "Torsion: JQ[3] doesn't map to coset[3] (i={i})"
            );
            checked += 1;
        }
        assert!(
            checked > 400,
            "Too few non-degenerate points tested: {checked}"
        );
    }

    /// Runtime validation for `lemma_jacobi_quartic_edge_values`.
    ///
    /// Tests the edge case (x=0 or y=0) by directly constructing
    /// the identity (0,1,1,0) and the 2-torsion point (0,-1,1,0),
    /// then checking that each JQ→Edwards result is a coset member.
    #[test]
    fn test_axiom_edge_values() {
        let zero = FieldElement::ZERO;
        let one = FieldElement::ONE;
        let neg_one = -&one;

        let identity = EdwardsPoint {
            X: zero,
            Y: one,
            Z: one,
            T: zero,
        };
        let two_torsion = EdwardsPoint {
            X: zero,
            Y: neg_one,
            Z: one,
            T: zero,
        };

        for pt in &[identity, two_torsion] {
            let coset = RistrettoPoint(*pt).xcoset4();
            let jcs = RistrettoPoint(*pt).to_jacobi_quartic_ristretto();

            for k in 0..4 {
                let (xj, yj) = jacobi_to_edwards_exec(&jcs[k].S, &jcs[k].T);
                let is_member = (0..4).any(|c| affine_eq(&coset[c], &xj, &yj));
                assert!(
                    is_member,
                    "Edge axiom: JQ[{k}] doesn't map to any coset member"
                );
            }
        }
    }

    /// Runtime validation for `axiom_four_torsion_affine`.
    ///
    /// Computes the affine coordinates X/Z and Y/Z of the even-indexed
    /// 8-torsion elements T[2], T[4], T[6] and checks:
    ///   T[2] = (sqrt(-1), 0), T[4] = (0, -1), T[6] = (-sqrt(-1), 0).
    #[test]
    fn test_axiom_four_torsion_affine() {
        let torsion = constants::EIGHT_TORSION;
        let sqrt_m1 = constants::SQRT_M1;
        let neg_sqrt_m1 = -&sqrt_m1;
        let neg_one = -&FieldElement::ONE;

        // T[2] is a 4-torsion element with y = 0, x = ±sqrt(-1)
        let t2 = &torsion[2];
        let z_inv = t2.Z.invert();
        let x2 = &t2.X * &z_inv;
        let y2 = &t2.Y * &z_inv;
        assert!(fe_eq(&y2, &FieldElement::ZERO), "T[2].y should be 0");
        let x2_sq = &x2 * &x2;
        assert!(
            fe_eq(&x2_sq, &FieldElement::MINUS_ONE),
            "T[2].x² should be -1"
        );

        // T[4] is the 2-torsion element (0, -1)
        let t4 = &torsion[4];
        let z_inv = t4.Z.invert();
        let x4 = &t4.X * &z_inv;
        let y4 = &t4.Y * &z_inv;
        assert!(fe_eq(&x4, &FieldElement::ZERO), "T[4].x should be 0");
        assert!(fe_eq(&y4, &neg_one), "T[4].y should be -1");

        // T[6] is a 4-torsion element with y = 0, x = -T[2].x
        let t6 = &torsion[6];
        let z_inv = t6.Z.invert();
        let x6 = &t6.X * &z_inv;
        let y6 = &t6.Y * &z_inv;
        assert!(fe_eq(&y6, &FieldElement::ZERO), "T[6].y should be 0");
        let x6_sq = &x6 * &x6;
        assert!(
            fe_eq(&x6_sq, &FieldElement::MINUS_ONE),
            "T[6].x² should be -1"
        );

        // T[2] and T[6] are the two distinct 4-torsion points: x₂ = -x₆
        let neg_x6 = -&x6;
        assert!(fe_eq(&x2, &neg_x6), "T[2].x should be -T[6].x");

        // One of them is sqrt(-1) and the other is -sqrt(-1)
        assert!(
            (fe_eq(&x2, &sqrt_m1) && fe_eq(&x6, &neg_sqrt_m1))
                || (fe_eq(&x2, &neg_sqrt_m1) && fe_eq(&x6, &sqrt_m1)),
            "T[2] and T[6] should be ±sqrt(-1) in some order"
        );
    }

    /// Runtime validation for `axiom_mc_times_sqrt_ad_m1`.
    ///
    /// Checks that mc · √(ad−1) = 2·√(−1) where
    /// mc = MIDOUBLE_INVSQRT_A_MINUS_D.
    ///
    /// Equivalently: mc · √(ad−1) − 2·i = 0.
    #[test]
    fn test_axiom_mc_times_sqrt_ad_m1() {
        let mc = lizard_constants::MIDOUBLE_INVSQRT_A_MINUS_D;
        let sqrt_ad_m1 = constants::SQRT_AD_MINUS_ONE;
        let product = &mc * &sqrt_ad_m1;

        // Verify product² = (-2i)² = -4
        let product_sq = &product * &product;
        let four = {
            let two = &FieldElement::ONE + &FieldElement::ONE;
            &two * &two
        };
        let neg_four = -&four;
        assert!(fe_eq(&product_sq, &neg_four), "product² should be -4");

        // Verify product = -2i, i.e. product - (-2i) = product + 2i = 0
        // OR product = 2i, i.e. product - 2i = 0
        let two = &FieldElement::ONE + &FieldElement::ONE;
        let two_i = &two * &constants::SQRT_M1;
        let sum_minus = &product - &two_i;
        assert!(
            fe_eq(&sum_minus, &FieldElement::ZERO),
            "mc * sqrt(ad-1) should be 2*sqrt(-1).\nproduct-2i bytes: {:?}",
            sum_minus.as_bytes()
        );
    }

    /// Runtime validation for `axiom_decode_from_point`.
    ///
    /// Encodes 200+ random 16-byte messages via Lizard, then decodes them
    /// and verifies the round-trip succeeds.
    #[test]
    fn test_lizard_decode_roundtrip_exhaustive() {
        let mut rng = rand::thread_rng();
        let mut success = 0u32;
        let total = 200;

        for i in 0..total {
            let mut msg = [0u8; 16];
            if i == 0 {
                // all zeros
            } else if i == 1 {
                msg = [0xFF; 16];
            } else {
                rng.fill_bytes(&mut msg);
            }

            let pt = RistrettoPoint::lizard_encode::<Sha256>(&msg);
            match pt.lizard_decode::<Sha256>() {
                Some(decoded) => {
                    assert_eq!(decoded, msg, "Round-trip mismatch at iteration {i}");
                    success += 1;
                }
                None => {
                    // Extremely rare collision — acceptable but count it
                }
            }
        }
        assert!(
            success >= 195,
            "Too few successful round-trips: {success}/{total}"
        );
    }

    /// Runtime sanity check for `elligator_ristretto_flavor_inverse`.
    ///
    /// For 200+ random Ristretto points, verifies that the exec-level
    /// `(mask, fes)` yields field elements whose forward Elligator image
    /// is a coset member (the coset property is now formally proved via
    /// the strengthened ensures of `elligator_ristretto_flavor_inverse`).
    #[test]
    fn test_elligator_inverse_coset_membership() {
        let mut rng = rand::thread_rng();
        let mut checked = 0u32;

        for i in 0..200 {
            let mut fe_bytes = [0u8; 32];
            if i == 0 {
                fe_bytes = [0u8; 32];
            } else {
                rng.fill_bytes(&mut fe_bytes);
            }
            fe_bytes[0] &= 254;
            fe_bytes[31] &= 127;
            let fe = FieldElement::from_bytes(&fe_bytes);
            let pt = RistrettoPoint::elligator_ristretto_flavor(&fe);

            let (mask, fes) = RistrettoPoint(pt.0).elligator_ristretto_flavor_inverse();
            let coset = RistrettoPoint(pt.0).xcoset4();

            for j in 0..8u8 {
                if mask & (1 << j) != 0 {
                    let round_trip = RistrettoPoint::elligator_ristretto_flavor(&fes[j as usize]);
                    let is_member = (0..4).any(|c| round_trip == RistrettoPoint(coset[c]));
                    assert!(is_member, "Candidate {j} does not map to coset (i={i})");
                    checked += 1;
                }
            }
        }
        assert!(checked > 100, "Too few candidates checked: {checked}");
    }
}
