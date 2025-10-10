// field.rs
#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::common_verus::bit_lemmas::*;
use super::common_verus::div_mod_lemmas::*;
use super::common_verus::mask_lemmas::*;
use super::common_verus::mul_lemmas::*;
use super::common_verus::pow_lemmas::*;
use super::common_verus::shift_lemmas::*;

use super::field_lemmas::as_nat_lemmas::*;
use super::field_lemmas::field_core::*;
use super::field_lemmas::load8_lemmas::*;
use super::field_lemmas::negate_lemmas::*;
use super::field_lemmas::pow2_51_lemmas::*;
use super::field_lemmas::pow2k_lemmas::*;
use super::field_lemmas::reduce_lemmas::*;
use super::field_lemmas::to_bytes_lemmas::*;
                                                                                                                                                                                
// ADAPTED CODE LINES: X.0 globally replaced with X.limbs

verus! {

/* MANUALLY moved outside and made explicit */
// LOW_51_BIT_MASK: u64 = (1u64 << 51) -1; originally
pub const LOW_51_BIT_MASK: u64 = 2251799813685247u64; // 2^51  -1

// Establishes LOW_51_BIT_MASK == mask51 and lifts properties of the RHS to the LHS
pub proof fn masks_are_equal()
    ensures
        LOW_51_BIT_MASK == mask51,
        LOW_51_BIT_MASK == low_bits_mask(51),
        LOW_51_BIT_MASK < (1u64 << 51) as nat,
{
    l51_bit_mask_lt();
}

/* MANUALLY moved outside, named return value */
const fn load8_at(input: &[u8], i: usize) -> (r: u64)
    requires
        i + 7 < input.len(),
    ensures
        r as nat == load8_at_spec(input, i)
{
    proof {
        rec_version_is_exec(input, i);
        load8_at_versions_equivalent(input, i, 7);
        plus_version_is_spec(input, i);
    }
        (input[i] as u64)
    | ((input[i + 1] as u64) << 8)
    | ((input[i + 2] as u64) << 16)
    | ((input[i + 3] as u64) << 24)
    | ((input[i + 4] as u64) << 32)
    | ((input[i + 5] as u64) << 40)
    | ((input[i + 6] as u64) << 48)
    | ((input[i + 7] as u64) << 56)
}

/* MANUALLY moved outside */
#[inline(always)]
fn m(x: u64, y: u64) -> (r: u128)
    ensures
        (r as nat) == (x as nat) * (y as nat),
        r <= u128::MAX

{
    proof {
        // if a <= a' and b <= b' then ab <= a'b'
        mul_le(x as nat, u64::MAX as nat, y as nat, u64::MAX as nat);
    }
    (x as u128) * (y as u128)
}

pub struct FieldElement51 {
    // ADAPTED CODE LINE: we give a name to the field: "limbs"
    pub limbs: [u64; 5],
}

impl FieldElement51 {
    pub(crate) const fn from_limbs(limbs: [u64; 5]) -> FieldElement51 {
        // ADAPTED CODE LINE: limbs is now a named field
        FieldElement51{limbs}
    }

    // Modified to use direct struct
    pub const ZERO: FieldElement51 = FieldElement51{limbs: [0, 0, 0, 0, 0]};
    pub const ONE: FieldElement51 = FieldElement51{limbs: [1, 0, 0, 0, 0]};
    pub const MINUS_ONE: FieldElement51 = FieldElement51{limbs: [
        2251799813685228,
        2251799813685247,
        2251799813685247,
        2251799813685247,
        2251799813685247,
    ]};

    /// Invert the sign of this field element
    pub fn negate(&mut self)
        requires
            forall|i: int| 0 <= i < 5 ==> old(self).limbs[i] < (1u64 << 51),
        ensures
            forall|i: int| 0 <= i < 5 ==> self.limbs[i] < (1u64 << 52),
            // Assume we start with l = (l0, l1, l2, l3, l4).
            // Using c0 = 2^51 - 19 and c = 2^51 - 1, we can see that
            // ( 36028797018963664u64 - l0,
            //   36028797018963952u64 - l1,
            //   36028797018963952u64 - l2,
            //   36028797018963952u64 - l3,
            //   36028797018963952u64 - l4 )
            // is just 16 * (c0, c, c, c, c) - l (in vector notation)
            // Further, as_nat((c0, c, c, c, c)) = p, so
            // as_nat(16 * (c0, c, c, c, c) - l) is 16p - as_nat(l)
            // We know as_nat(reduce(v)) = as_nat(v) - p * (v4 >> 51) for any v.
            // This gives us the identity
            // as_nat(negate(l)) = as_nat(reduce(16 * (c0, c, c, c, c) - l))
            //                   = 16p - as_nat(l) - p * ((16c - l4) >> 51)
            // Note that (16c - l4) >> 51 is either 14 or 15, in either case < 16.
            as_nat(self.limbs) == 16 * p() - as_nat(old(self).limbs) - p() * ((36028797018963952u64 - old(self).limbs[4]) as u64 >> 51),
            (as_nat(self.limbs) + as_nat(old(self).limbs)) % p() == 0
    {
        proof {
            lemma_neg_no_underflow(self.limbs);
            negate_proof(self.limbs);
        }
        // See commentary in the Sub impl: (copied below)
            // To avoid underflow, first add a multiple of p.
            // Choose 16*p = p << 4 to be larger than 54-bit _rhs.
            //
            // If we could statically track the bitlengths of the limbs
            // of every FieldElement51, we could choose a multiple of p
            // just bigger than _rhs and avoid having to do a reduction.
            //
            // Since we don't yet have type-level integers to do this, we
            // have to add an explicit reduction call here.
        // Note on "magic numbers":
        // 36028797018963664u64 = 2^55 - 304 = 16 * (2^51 - 19)
        // 36028797018963952u64 = 2^55 - 16 =  16 * (2^51 - 1)
        let neg = FieldElement51::reduce([
            36028797018963664u64 - self.limbs[0],
            36028797018963952u64 - self.limbs[1],
            36028797018963952u64 - self.limbs[2],
            36028797018963952u64 - self.limbs[3],
            36028797018963952u64 - self.limbs[4],
        ]);
        self.limbs = neg.limbs;
    }

    /// Given 64-bit input limbs, reduce to enforce the bound 2^(51 + epsilon).
    #[inline(always)]
    fn reduce(mut limbs: [u64; 5]) -> (r: FieldElement51)
        ensures
            r.limbs == spec_reduce(limbs),
            forall|i: int| 0 <= i < 5 ==> r.limbs[i] < (1u64 << 52),
            (forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51)) ==> (r.limbs =~= limbs),
            as_nat(r.limbs) == as_nat(limbs) - p() * (limbs[4] >> 51),
            as_nat(r.limbs) % p() == as_nat(limbs) % p(),
            as_nat(r.limbs) < 2 * p(),
    {
        proof {
            lemma_boundaries(limbs);
            lemma_reduce(limbs);
            lemma_reduce_bound_2p(limbs);
            pow255_gt_19();
            lemma_mod_multiples_vanish((limbs[4] >> 51) as int, as_nat(spec_reduce(limbs)) as int, p() as int);
        }

        // Since the input limbs are bounded by 2^64, the biggest
        // carry-out is bounded by 2^13.
        //
        // The biggest carry-in is c4 * 19, resulting in
        //
        // 2^51 + 19*2^13 < 2^51.0000000001
        //
        // Because we don't need to canonicalize, only to reduce the
        // limb sizes, it's OK to do a "weak reduction", where we
        // compute the carry-outs in parallel.

        let c0 = limbs[0] >> 51;
        let c1 = limbs[1] >> 51;
        let c2 = limbs[2] >> 51;
        let c3 = limbs[3] >> 51;
        let c4 = limbs[4] >> 51;

        limbs[0] &= LOW_51_BIT_MASK;
        limbs[1] &= LOW_51_BIT_MASK;
        limbs[2] &= LOW_51_BIT_MASK;
        limbs[3] &= LOW_51_BIT_MASK;
        limbs[4] &= LOW_51_BIT_MASK;

        limbs[0] += c4 * 19;
        limbs[1] += c0;
        limbs[2] += c1;
        limbs[3] += c2;
        limbs[4] += c3;

        // ADAPTED CODE LINE: limbs is now a named field
        FieldElement51{limbs}
    }

    /// Load a `FieldElement51` from the low 255 bits of a 256-bit
    /// input.
    ///
    /// # Warning
    ///
    /// This function does not check that the input used the canonical
    /// representative.  It masks the high bit, but it will happily
    /// decode 2^255 - 18 to 1.  Applications that require a canonical
    /// encoding of every field element should decode, re-encode to
    /// the canonical encoding, and check that the input was
    /// canonical.
    ///
    #[rustfmt::skip] // keep alignment of bit shifts
    pub const fn from_bytes(bytes: &[u8; 32]) -> (r: FieldElement51)
        ensures
            // last bit is ignored
            as_nat(r.limbs) == as_nat_32_u8(*bytes) % pow2(255)
    {
        proof {
            l51_bit_mask_lt(); // No over/underflow in the below let-def
            assume(false);
        }
        let low_51_bit_mask = (1u64 << 51) - 1;
        // ADAPTED CODE LINE: limbs is now a named field
        FieldElement51{ limbs:
        // load bits [  0, 64), no shift
        [  load8_at(bytes,  0)        & low_51_bit_mask
        // load bits [ 48,112), shift to [ 51,112)
        , (load8_at(bytes,  6) >>  3) & low_51_bit_mask
        // load bits [ 96,160), shift to [102,160)
        , (load8_at(bytes, 12) >>  6) & low_51_bit_mask
        // load bits [152,216), shift to [153,216)
        , (load8_at(bytes, 19) >>  1) & low_51_bit_mask
        // load bits [192,256), shift to [204,112)
        , (load8_at(bytes, 24) >> 12) & low_51_bit_mask
        ]}
    }

    /// Serialize this `FieldElement51` to a 32-byte array.  The
    /// encoding is canonical.
    #[rustfmt::skip] // keep alignment of s[*] calculations
    #[allow(clippy::wrong_self_convention)]
    pub fn to_bytes(self) -> (r: [u8; 32])
        ensures
            // canonical encoding, i.e. mod p value
            as_nat_32_u8(r) == as_nat(self.limbs) % p()
    {
        proof {
            // Step 1: Reduce limbs to ensure h < 2*p
            // The reduce function ensures the limbs are bounded by 2^52
            lemma_reduce(self.limbs);
        }
        // Let h = limbs[0] + limbs[1]*2^51 + ... + limbs[4]*2^204.
        //
        // Write h = pq + r with 0 <= r < p.
        //
        // We want to compute r = h mod p.
        //
        // If h < 2*p = 2^256 - 38,
        // then q = 0 or 1,
        //
        // with q = 0 when h < p
        //  and q = 1 when h >= p.
        //
        // Notice that h >= p <==> h + 19 >= p + 19 <==> h + 19 >= 2^255.
        // Therefore q can be computed as the carry bit of h + 19.

        // First, reduce the limbs to ensure h < 2*p.
        let mut limbs = FieldElement51::reduce(self.limbs).limbs;
        
        // Track reduced limbs for proof
        proof {
            // After reduce, we have as_nat(limbs) < 2*p() from reduce's postcondition
            assert(as_nat(limbs) < 2 * p());
        }

        // Compute q with overflow proofs
        // After reduce, limbs[i] < 2^52, so limbs[0] + 19 < 2^52 + 19 < 2^64
        proof {
            assert((1u64 << 52) + 19 <= u64::MAX) by (compute);
        }
        let mut q = (limbs[0] + 19) >> 51;
        
        proof {
            // Prove q <= 2 after first iteration
            //lemma_add_preserves_bound(limbs[0], 1u64 << 52, 19);
            lemma_shr_le_u64((limbs[0] + 19) as u64, ((1u64 << 52) + 19) as u64, 51);
            assert((((1u64 << 52) + 19) as u64) >> 51 == 2) by (compute);
            assert(q <= 2);
        }
        
        // Second iteration
        //proof {
        //    assert((1u64 << 52) + 2 <= u64::MAX) by (compute);
            //lemma_add_preserves_bound(limbs[1], 1u64 << 52, q);
        //}
        let ghost old_q = q;
        q = (limbs[1] + q) >> 51;
        
        proof {
            lemma_shr_le_u64((limbs[1] + old_q) as u64, ((1u64 << 52) + 2) as u64, 51);
            assert(((limbs[1] + old_q) as u64) >> 51 == q);
            assert((((1u64 << 52) + 2) as u64) >> 51 == 2) by (compute);
            assert(q <= 2);
        }
        
        // Third iteration
        //proof {
        //    lemma_add_preserves_bound(limbs[2], 1u64 << 52, q);
        //}
        let ghost old_q2 = q;
        q = (limbs[2] + q) >> 51;
        
        proof {
            lemma_shr_le_u64((limbs[2] + old_q2) as u64, ((1u64 << 52) + 2) as u64, 51);
            assert(((limbs[2] + old_q2) as u64) >> 51 == q);
            assert((((1u64 << 52) + 2) as u64) >> 51 == 2) by (compute);
            assert(q <= 2);
        }
        
        // Fourth iteration
        //proof {
        //    lemma_add_preserves_bound(limbs[3], 1u64 << 52, q);
        //}
        let ghost old_q3 = q;
        q = (limbs[3] + q) >> 51;
        
        proof {
            lemma_shr_le_u64((limbs[3] + old_q3) as u64, ((1u64 << 52) + 2) as u64, 51);
            assert(((limbs[3] + old_q3) as u64) >> 51 == q);
            assert((((1u64 << 52) + 2) as u64) >> 51 == 2) by (compute);
            assert(q <= 2);
        }
        
        // Fifth iteration
        //proof {
        //    lemma_add_preserves_bound(limbs[4], 1u64 << 52, q);
        //}
        q = (limbs[4] + q) >> 51;
        let ghost reduced_limbs = limbs;
        proof {
            // Step 2: Prove that q is the correct quotient
            lemma_compute_q(reduced_limbs, q);
            // Note: as_nat(reduced_limbs) < 2*p() from reduce's postcondition (line 278)
            assert(as_nat(reduced_limbs) < 2 * p());
        }

        // Now we can compute r as r = h - pq = r - (2^255-19)q = r + 19q - 2^255q
        
        proof {
            // q is at most 1, so 19*q is at most 19
            assert(q <= 1);
            assert((1u64 << 52) + 19 <= u64::MAX) by (compute);
        }
        limbs[0] += 19 * q;

        // Now carry the result to compute r + 19q ...
        // Use LOW_51_BIT_MASK constant directly for proof purposes
        
        // Track intermediate values for proof
        let ghost l0 = limbs[0];
        
        proof {
            // Establish that LOW_51_BIT_MASK == mask51
            masks_are_equal();
            
            // limbs[0] < 2^52 + 19, so limbs[0] >> 51 <= 2
            lemma_shr_le_u64(limbs[0], ((1u64 << 52) + 19) as u64, 51);
            assert((((1u64 << 52) + 19) as u64) >> 51 == 2) by (compute);
            assert(limbs[0] >> 51 <= 2);
            assert((1u64 << 52) + 2 <= u64::MAX) by (compute);
        }
        limbs[1] += limbs[0] >> 51;
        let ghost l1 = limbs[1];
        limbs[0] &= LOW_51_BIT_MASK;
        
        proof {
            lemma_shr_le_u64(limbs[1], ((1u64 << 52) + 2) as u64, 51);
            assert((((1u64 << 52) + 2) as u64) >> 51 == 2) by (compute);
            assert(limbs[1] >> 51 <= 2);
            assert((1u64 << 52) + 2 <= u64::MAX) by (compute);
        }
        limbs[2] += limbs[1] >> 51;
        let ghost l2 = limbs[2];
        limbs[1] &= LOW_51_BIT_MASK;
        
        proof {
            lemma_shr_le_u64(limbs[2], ((1u64 << 52) + 2) as u64, 51);
            assert(limbs[2] >> 51 <= 2);
        }
        limbs[3] += limbs[2] >> 51;
        let ghost l3 = limbs[3];
        limbs[2] &= LOW_51_BIT_MASK;
        
        proof {
            lemma_shr_le_u64(limbs[3], ((1u64 << 52) + 2) as u64, 51);
            assert(limbs[3] >> 51 <= 2);
        }
        limbs[4] += limbs[3] >> 51;
        let ghost l4 = limbs[4];
        limbs[3] &= LOW_51_BIT_MASK;
        // ... but instead of carrying (limbs[4] >> 51) = 2^255q
        // into another limb, discard it, subtracting the value
        limbs[4] &= LOW_51_BIT_MASK;

        // Track final limbs for proof
        let ghost final_limbs = limbs;

        proof {
            // Step 3: Prove that the reduction preserves the value mod p
            // Establish preconditions:
            assert(q == 0 || q == 1); // from lemma_compute_q postcondition
            // The relationship as_nat(reduced_limbs) >= p() <==> q == 1 comes from lemma_compute_q
            
            // Prove that final_limbs == reduce_with_q_spec(reduced_limbs, q)
            // This requires showing the executable code matches the spec
            
            // LOW_51_BIT_MASK == mask51 was already established earlier
            // Now show that each intermediate value matches the spec
            // l0 = reduced_limbs[0] + 19 * q
            assert(l0 == (reduced_limbs[0] + 19 * q) as u64);
            
            // l1 = reduced_limbs[1] + (l0 >> 51)
            assert(l1 == (reduced_limbs[1] + (l0 >> 51)) as u64);
            
            // limbs[0] after masking = l0 & mask51
            assert(final_limbs[0] == (l0 & LOW_51_BIT_MASK) as u64);
            assert(final_limbs[0] == (l0 & mask51) as u64);
            
            // l2 = reduced_limbs[2] + (l1 >> 51)
            assert(l2 == (reduced_limbs[2] + (l1 >> 51)) as u64);
            
            // limbs[1] after masking = l1 & mask51
            assert(final_limbs[1] == (l1 & LOW_51_BIT_MASK) as u64);
            assert(final_limbs[1] == (l1 & mask51) as u64);
            
            // l3 = reduced_limbs[3] + (l2 >> 51)
            assert(l3 == (reduced_limbs[3] + (l2 >> 51)) as u64);
            
            // limbs[2] after masking = l2 & mask51
            assert(final_limbs[2] == (l2 & LOW_51_BIT_MASK) as u64);
            assert(final_limbs[2] == (l2 & mask51) as u64);
            
            // l4 = reduced_limbs[4] + (l3 >> 51)
            assert(l4 == (reduced_limbs[4] + (l3 >> 51)) as u64);
            
            // limbs[3] after masking = l3 & mask51
            assert(final_limbs[3] == (l3 & LOW_51_BIT_MASK) as u64);
            assert(final_limbs[3] == (l3 & mask51) as u64);
            
            // limbs[4] after masking = l4 & mask51
            assert(final_limbs[4] == (l4 & LOW_51_BIT_MASK) as u64);
            assert(final_limbs[4] == (l4 & mask51) as u64);
            
            // Now construct the spec result and show it equals final_limbs
            let spec_result = reduce_with_q_spec(reduced_limbs, q);
            assert(spec_result[0] == (l0 & mask51) as u64);
            assert(spec_result[1] == (l1 & mask51) as u64);
            assert(spec_result[2] == (l2 & mask51) as u64);
            assert(spec_result[3] == (l3 & mask51) as u64);
            assert(spec_result[4] == (l4 & mask51) as u64);
            
            // Therefore final_limbs == spec_result
            assert(final_limbs[0] == spec_result[0]);
            assert(final_limbs[1] == spec_result[1]);
            assert(final_limbs[2] == spec_result[2]);
            assert(final_limbs[3] == spec_result[3]);
            assert(final_limbs[4] == spec_result[4]);
            assert(final_limbs == spec_result);
            assert(final_limbs == reduce_with_q_spec(reduced_limbs, q));
            
            lemma_to_bytes_reduction(reduced_limbs, final_limbs, q);
            // Now we know: as_nat(final_limbs) == as_nat(self.limbs) % p()
        }

        // Now arrange the bits of the limbs.
        let mut s = [0u8;32];
        s[ 0] =   limbs[0]                           as u8;
        s[ 1] =  (limbs[0] >>  8)                    as u8;
        s[ 2] =  (limbs[0] >> 16)                    as u8;
        s[ 3] =  (limbs[0] >> 24)                    as u8;
        s[ 4] =  (limbs[0] >> 32)                    as u8;
        s[ 5] =  (limbs[0] >> 40)                    as u8;
        s[ 6] = ((limbs[0] >> 48) | (limbs[1] << 3)) as u8;
        s[ 7] =  (limbs[1] >>  5)                    as u8;
        s[ 8] =  (limbs[1] >> 13)                    as u8;
        s[ 9] =  (limbs[1] >> 21)                    as u8;
        s[10] =  (limbs[1] >> 29)                    as u8;
        s[11] =  (limbs[1] >> 37)                    as u8;
        s[12] = ((limbs[1] >> 45) | (limbs[2] << 6)) as u8;
        s[13] =  (limbs[2] >>  2)                    as u8;
        s[14] =  (limbs[2] >> 10)                    as u8;
        s[15] =  (limbs[2] >> 18)                    as u8;
        s[16] =  (limbs[2] >> 26)                    as u8;
        s[17] =  (limbs[2] >> 34)                    as u8;
        s[18] =  (limbs[2] >> 42)                    as u8;
        s[19] = ((limbs[2] >> 50) | (limbs[3] << 1)) as u8;
        s[20] =  (limbs[3] >>  7)                    as u8;
        s[21] =  (limbs[3] >> 15)                    as u8;
        s[22] =  (limbs[3] >> 23)                    as u8;
        s[23] =  (limbs[3] >> 31)                    as u8;
        s[24] =  (limbs[3] >> 39)                    as u8;
        s[25] = ((limbs[3] >> 47) | (limbs[4] << 4)) as u8;
        s[26] =  (limbs[4] >>  4)                    as u8;
        s[27] =  (limbs[4] >> 12)                    as u8;
        s[28] =  (limbs[4] >> 20)                    as u8;
        s[29] =  (limbs[4] >> 28)                    as u8;
        s[30] =  (limbs[4] >> 36)                    as u8;
        s[31] =  (limbs[4] >> 44)                    as u8;

        proof {
            // Step 4: Prove that packing limbs into bytes preserves the value
            lemma_limbs_to_bytes(final_limbs, s);
            // Now we know: as_nat_32_u8(s) == as_nat(final_limbs)
            // Combined with step 3: as_nat(final_limbs) == as_nat(self.limbs) % p()
            // We get: as_nat_32_u8(s) == as_nat(self.limbs) % p()
        }

        // High bit should be zero.
        // DISABLED DUE TO NO VERUS SUPPORT FOR PANICS
        // debug_assert!((s[31] & 0b1000_0000u8) == 0u8);

        s
    }

    /// Given `k > 0`, return `self^(2^k)`.
    #[rustfmt::skip] // keep alignment of c* calculations
    pub fn pow2k(&self, mut k: u32) -> (r: FieldElement51)
        requires
            k > 0, // debug_assert!( k > 0 );
            forall |i: int| 0 <= i < 5 ==> self.limbs[i] < 1u64 << 54 // 51 + b for b = 3
        ensures
            forall |i: int| 0 <= i < 5 ==> r.limbs[i] < 1u64 << 54,
            as_nat(r.limbs) % p() == pow(as_nat(self.limbs) as int, pow2(k as nat)) as nat % p()
    {
        let mut a: [u64; 5] = self.limbs;

        // pre-loop invariant, i = 0
        proof {
            assert(as_nat(a) == pow(as_nat(self.limbs) as int, pow2(0))) by {
                lemma2_to64(); // pow2(0) = 1
                lemma_pow1(as_nat(self.limbs) as int);
            }
        }

        for i in 0..k
            invariant
                forall |j: int| 0 <= j < 5 ==> a[j] < 1u64 << 54,
                as_nat(a) % p() == pow(as_nat(self.limbs) as int, pow2(i as nat)) as nat % p(),
        {
            proof {
                pow255_gt_19(); // p > 0
                lemma2_to64_rest(); // pow2(51 | 54)
                shift_is_pow2(54);

                let bound = 1u64 << 54;
                let bound19 = (19 * bound) as u64;
                let bound_sq = 1u128 << 108;

                // u64 to u128 conversion forces extra assert
                assert( (1u64 << 54) * ((19 * (1u64 << 54)) as u64) == 19 * (1u128 << 108)) by (bit_vector);
                assert(((1u64 << 54) as u128) * ((1u64 << 54) as u128) == (1u128 << 108)) by (bit_vector);

                // precond for term_product_bounds
                assert( 19 * bound <= u64::MAX) by {
                    assert( 19 * (1u64 << 54) <= u64::MAX) by (compute);
                }
                // If a[i] < 2^54 then a[i] * a[j] < 2^108 and a[i] * (19 * a[j]) < 19 * 2^108
                term_product_bounds(a, bound);

                // ci_0 < 77 * (1u128 << 108)
                c_i_0_bounded(a, bound);

                // precond for c_i_shift_bounded
                assert(77 * (bound * bound) + u64::MAX <= ((u64::MAX as u128) << 51)) by {
                    assert( 77 * (1u128 << 108)+ u64::MAX <= ((u64::MAX as u128) << 51)) by (compute);
                }
                // ci >> 51 <= u64::MAX
                c_i_shift_bounded(a, bound);

                // bv arithmetic
                assert(19 < (1u64 << 5)) by (bit_vector);
                assert((1u64 << 51) < (1u64 << 52)) by (bit_vector);
                assert((1u64 << 52) < (1u64 << 54)) by (bit_vector);
                assert((1u64 << 54) < (1u64 << 59)) by (bit_vector);
                assert((1u64 << 54) * (1u64 << 5) == (1u64 << 59)) by (bit_vector);
                assert(((1u64 << 54) as u128) * ((1u64 << 59) as u128) == (1u128 << 113)) by (bit_vector);

                let a3_19 = (19 * a[3]) as u64;
                let a4_19 = (19 * a[4]) as u64;

                // NOTE: we assert the properties derived from c_i_0_bounded
                // and c_i_shift_bounded after every variable declaration,
                // to trigger the solver instantiation

                // ci_0 defs

                let c0_0: u128 = c0_0_val(a); // a[0] *  a[0] + 2*( a[1] * a4_19 + a[2] * a3_19
                assert(c0_0 < 77 * bound_sq);

                let c1_0: u128 = c1_0_val(a); // a[3] * a3_19 + 2*( a[0] *  a[1] + a[2] * a4_19
                assert(c1_0 < 59 * bound_sq);

                let c2_0: u128 = c2_0_val(a); // a[1] *  a[1] + 2*( a[0] *  a[2] + a[4] * a3_19
                assert(c2_0 < 41 * bound_sq);

                let c3_0: u128 =  c3_0_val(a); // a[4] * a4_19 + 2*( a[0] *  a[3] + a[1] *  a[2]
                assert(c3_0 < 23 * bound_sq);

                let c4_0: u128 =  c4_0_val(a); // a[2] *  a[2] + 2*( a[0] *  a[4] + a[1] *  a[3]
                assert(c4_0 < 5 * bound_sq);

                // ci defs

                let c1 = c1_val(a); // (c1_0 + ((c0_0 >> 51) as u64) as u128) as u128;
                assert((c1 >> 51) <= (u64::MAX as u128));

                let c2 = c2_val(a); // (c2_0 + ((c1 >> 51) as u64) as u128) as u128;
                assert((c2 >> 51) <= (u64::MAX as u128));

                let c3 = c3_val(a); // (c3_0 + ((c2 >> 51) as u64) as u128) as u128;
                assert((c3 >> 51) <= (u64::MAX as u128));

                let c4 = c4_val(a); // (c4_0 + ((c3 >> 51) as u64) as u128) as u128;
                assert((c4 >> 51) <= (u64::MAX as u128));

                let a0_0 = (c0_0 as u64) & LOW_51_BIT_MASK;
                // a0_0 < (1u64 << 51)
                masked_lt_51(c0_0 as u64);

                let a1_0 = (c1 as u64) & LOW_51_BIT_MASK;
                // a1_0 < (1u64 << 51)
                masked_lt_51(c1 as u64);

                let a2 = (c2 as u64) & LOW_51_BIT_MASK;
                // a2 < (1u64 << 51)
                masked_lt_51(c2 as u64);

                let a3 = (c3 as u64) & LOW_51_BIT_MASK;
                // a3 < (1u64 << 51)
                masked_lt_51(c3 as u64);

                let carry: u64 = (c4 >> 51) as u64;
                let a4 = (c4 as u64) & LOW_51_BIT_MASK;
                // a4 < (1u64 << 51)
                masked_lt_51(c4 as u64);

                assert(c4 <= c4_0 + (u64::MAX as u128));
                lemma_shr_51_le(c4, (5 * bound_sq + (u64::MAX as u128)) as u128 );

                // From the comments below:
                // c4 < 2^110.33  so that carry < 2^59.33
                // and
                // a[0] + carry * 19 < 2^51 + 19 * 2^59.33 < 2^63.58

                // ceil(2^59.33)
                let pow2_5933 = 724618875532318195u64;

                assert((5 * (1u128 << 108) + (u64::MAX as u128)) as u128 >> 51 < (pow2_5933 as u128)) by (compute);
                assert(carry < pow2_5933);

                // a[0] += carry * 19 fits in u64
                assert(a0_0 + carry * 19 <= u64::MAX) by {
                    assert((1u64 << 51) + 19 * pow2_5933 <= u64::MAX) by (compute);
                }

                let a0_1 = (a0_0 + carry * 19) as u64;

                lemma_shr_51_le(a0_1 as u128, u64::MAX as u128);
                assert( ((u64::MAX as u128) >> 51) < (1u64 << 13) ) by (compute);

                // a1_0 < (1u64 << 51)
                assert((1u64 << 51) + (1u64 << 13) < (1u64 << 52)) by (compute);

                // Now a[1] < 2^51 + 2^(64 -51) = 2^51 + 2^13 < 2^(51 + epsilon).
                assert(a1_0 + (a0_1 >> 51) < (1u64 << 52));
                let a1_1 = (a1_0 + (a0_1 >> 51)) as u64;

                let a0_2 = a0_1 & LOW_51_BIT_MASK;
                // a0_2 < (1u64 << 51)
                masked_lt_51(a0_1 as u64);

                //---- end of no-overflow proof ----
                // Loop invariant: after i loops we have as_nat(a) % p = as_nat(self.limbs) ^ (2 ^ i) % p
                let a_hat = [a0_2, a1_1, a2, a3, a4];
                assert(as_nat(a_hat) % p() == (as_nat(a) * as_nat(a)) % p() ) by {
                    // it suffices to prove as_nat(a_hat) == (as_nat(a))^2 (mod p)
                    // let s = pow2(51) for brevity

                    // By definition, as_nat(a_hat) = a0_2 + s * a1_1 + s^2 * a2 + s^3 * a3 + s^4 * a4
                    // a0_2 + s * a1_1 cancel out terms via the div/mod identity:
                    assert(as_nat(a_hat) ==
                        a0_1 +
                        pow2(51) * a1_0 +
                        pow2(102) * a2 +
                        pow2(153) * a3 +
                        pow2(204) * a4
                    ) by {
                        // a0_2 + s * a1_1 =
                        // a0_1 % s  + s * (a1_0 + s * (a0_1 / s)) =
                        // s * a1_0 + [s * (a0_1 / s) + a0_1 % s] = (by the div-mod identity)
                        // s * a1_0 + a0_1
                        assert(a0_2 + pow2(51) * a1_1 == a0_1 + pow2(51) * a1_0) by {
                            lemma_div_and_mod_51((a0_1 >> 51), a0_2, a0_1);
                        }
                    }

                    // Next, we replace all _ & LOW_BITS_MASK with (mod s)
                    assert(as_nat(a_hat) ==
                        ((c0_0 as u64) % (pow2(51) as u64)) + 19 * carry +
                        pow2( 51) * ((c1 as u64) % (pow2(51) as u64)) +
                        pow2(102) * ((c2 as u64) % (pow2(51) as u64)) +
                        pow2(153) * ((c3 as u64) % (pow2(51) as u64)) +
                        pow2(204) * ((c4 as u64) % (pow2(51) as u64))
                    ) by {
                        l51_bit_mask_lt();

                        assert((pow2(51) as u64) == (pow2(51) as u128));

                        assert(a0_1 == ((c0_0 as u64) % (pow2(51) as u64)) + 19 * carry) by {
                            lemma_u64_low_bits_mask_is_mod(c0_0 as u64, 51);
                        }

                        assert(a1_0 == (c1 as u64) % (pow2(51) as u64)) by {
                            lemma_u64_low_bits_mask_is_mod(c1 as u64, 51);
                        }

                        assert(a2 == (c2 as u64) % (pow2(51) as u64)) by {
                            lemma_u64_low_bits_mask_is_mod(c2 as u64, 51);
                        }

                        assert(a3 == (c3 as u64) % (pow2(51) as u64)) by {
                            lemma_u64_low_bits_mask_is_mod(c3 as u64, 51);
                        }

                        assert(a4 == (c4 as u64) % (pow2(51) as u64)) by {
                            lemma_u64_low_bits_mask_is_mod(c4 as u64, 51);
                        }
                    }

                    // We can see all mod operations in u128
                    assert(as_nat(a_hat) ==
                        (c0_0 % (pow2(51) as u128)) + 19 * carry +
                        pow2( 51) * (c1 % (pow2(51) as u128)) +
                        pow2(102) * (c2 % (pow2(51) as u128)) +
                        pow2(153) * (c3 % (pow2(51) as u128)) +
                        pow2(204) * (c4 % (pow2(51) as u128))
                    ) by {
                        // pow2(51) is the same in u64 and 128
                        lemma_cast_then_mod_51(c0_0);
                        lemma_cast_then_mod_51(c1);
                        lemma_cast_then_mod_51(c2);
                        lemma_cast_then_mod_51(c3);
                        lemma_cast_then_mod_51(c4);
                    }

                    // Next, we categorically replace a % s with a - s * ( a / s )
                    assert(as_nat(a_hat) ==
                        (c0_0 - pow2(51) * (c0_0 / (pow2(51) as u128))) + 19 * carry +
                        pow2( 51) * (c1 - pow2(51) * (c1/ (pow2(51) as u128))) +
                        pow2(102) * (c2 - pow2(51) * (c2/ (pow2(51) as u128))) +
                        pow2(153) * (c3 - pow2(51) * (c3/ (pow2(51) as u128))) +
                        pow2(204) * (c4 - pow2(51) * (c4/ (pow2(51) as u128)))
                    ) by {
                        lemma_fundamental_div_mod(c0_0 as int, pow2(51) as int);
                        lemma_fundamental_div_mod(c1 as int, pow2(51) as int);
                        lemma_fundamental_div_mod(c2 as int, pow2(51) as int);
                        lemma_fundamental_div_mod(c3 as int, pow2(51) as int);
                        lemma_fundamental_div_mod(c4 as int, pow2(51) as int);
                    }

                    // Then, we know that
                    // carry = c4/s
                    // c4 = c4_0 + c3/s <=> c3/s = c4 - c4_0
                    // c3 = c3_0 + c2/s <=> c2/s = c3 - c3_0
                    // c2 = c2_0 + c1/s <=> c1/s = c2 - c2_0
                    // c1 = c1_0 + c0_0/s <=> c0_0/s = c1 - c1_0
                    assert(as_nat(a_hat) ==
                        (c0_0 - pow2(51) * (c1 - c1_0)) + 19 * carry +
                        pow2( 51) * (c1 - pow2(51) * (c2 - c2_0)) +
                        pow2(102) * (c2 - pow2(51) * (c3 - c3_0)) +
                        pow2(153) * (c3 - pow2(51) * (c4 - c4_0)) +
                        pow2(204) * (c4 - pow2(51) * carry)
                    ) by {
                        lemma_u128_shr_is_div(c0_0, 51);
                        lemma_u128_shr_is_div(c1, 51);
                        lemma_u128_shr_is_div(c2, 51);
                        lemma_u128_shr_is_div(c3, 51);
                        lemma_u128_shr_is_div(c4, 51);
                    }

                    // Now we use distributivity and pow exponent sums, which cancels out any ci terms and leaves only ci_0 terms
                    // Conveniently, we're left with a difference of c * p
                    assert(as_nat(a_hat) ==
                        c0_0 +
                        pow2(51) * c1_0 +
                        pow2(102) * c2_0 +
                        pow2(153) * c3_0 +
                        pow2(204) * c4_0 -
                        p() * carry
                    ) by {
                        assert(c0_0 - pow2(51) * (c1 - c1_0) == c0_0 - pow2(51) * c1 + pow2(51) * c1_0) by {
                            lemma_mul_is_distributive_sub(pow2(51) as int, c1 as int, c1_0 as int);
                        }

                        assert(pow2( 51) * (c1 - pow2(51) * (c2 - c2_0)) == pow2( 51) * c1 - pow2(102) * c2 + pow2(102) * c2_0) by {
                            lemma_mul_sub(c1 as int, c2 as int, c2_0 as int, 51);
                        }

                        assert(pow2(102) * (c2 - pow2(51) * (c3 - c3_0)) == pow2(102) * c2 - pow2(153) * c3 + pow2(153) * c3_0) by {
                            lemma_mul_sub(c2 as int, c3 as int, c3_0 as int, 102);
                        }

                        assert(pow2(153) * (c3 - pow2(51) * (c4 - c4_0)) == pow2(153) * c3 - pow2(204) * c4 + pow2(204) * c4_0) by {
                            lemma_mul_sub(c3 as int, c4 as int, c4_0 as int, 153);
                        }

                        assert(pow2(204) * (c4 - pow2(51) * carry) == pow2(204) * c4 - pow2(255) * carry) by {
                            lemma_mul_is_distributive_sub(pow2(204) as int, c4 as int, pow2(51) * carry);
                            lemma_mul_is_associative(pow2(204) as int, pow2(51) as int, carry as int);
                            lemma_pow2_adds(204, 51);
                        }

                        // carry on the right, get p
                        assert(
                            c0_0 +
                            pow2(51) * c1_0 +
                            pow2(102) * c2_0 +
                            pow2(153) * c3_0 +
                            pow2(204) * c4_0 +
                            19 * carry - pow2(255) * carry
                            ==
                            c0_0 +
                            pow2(51) * c1_0 +
                            pow2(102) * c2_0 +
                            pow2(153) * c3_0 +
                            pow2(204) * c4_0 -
                            p() * carry
                        ) by {
                            pow255_gt_19();
                            lemma_mul_is_distributive_sub_other_way(carry as int, pow2(255) as int, 19);
                        }
                    }

                    let c_arr_as_nat = (c0_0 +
                        pow2(51) * c1_0 +
                        pow2(102) * c2_0 +
                        pow2(153) * c3_0 +
                        pow2(204) * c4_0
                        );


                    assert(as_nat(a_hat) % p() == c_arr_as_nat as nat % p()) by {
                        lemma_mod_diff_factor(carry as int, c_arr_as_nat as int, p() as int);
                    }

                    // We use the as_nat_squared lemma to see what (as_nat(a)^2) evaluates to (mod p)

                    // The nat_squared lemma gives us the following:
                    // as_nat(a) * as_nat(a) ==
                    // pow2(8 * 51) * (a[4] * a[4]) +
                    // pow2(7 * 51) * (2 * (a[3] * a[4])) +
                    // pow2(6 * 51) * (a[3] * a[3] + 2 * (a[2] * a[4])) +
                    // pow2(5 * 51) * (2 * (a[2] * a[3]) + 2 * (a[1] * a[4])) +
                    // pow2(4 * 51) * (a[2] * a[2] + 2 * (a[1] * a[3]) + 2 * (a[0] * a[4])) +
                    // pow2(3 * 51) * (2 * (a[1] * a[2]) + 2 * (a[0] * a[3])) +
                    // pow2(2 * 51) * (a[1] * a[1] + 2 * (a[0] * a[2])) +
                    // pow2(1 * 51) * (2 * (a[0] * a[1])) +
                    //                (a[0] * a[0])
                    //
                    // AND
                    //
                    // (as_nat(a) * as_nat(a)) % p() ==
                    // (
                    //     pow2(4 * 51) * (a[2] * a[2] + 2 * (a[1] * a[3]) + 2 * (a[0] * a[4])) +
                    //     pow2(3 * 51) * (2 * (a[1] *  a[2]) + 2 * (a[0] *  a[3]) + 19 * (a[4] * a[4])) +
                    //     pow2(2 * 51) * (a[1] * a[1] + 2 * (a[0] *  a[2]) + 19 * (2 * (a[3] * a[4]))) +
                    //     pow2(1 * 51) * (2 * (a[0] *  a[1]) + 19 * (a[3] * a[3] + 2 * (a[2] * a[4]))) +
                    //                    (a[0] *  a[0] + 19 * (2 * (a[2] * a[3]) + 2 * (a[1] * a[4])))
                    // ) as nat % p()
                    as_nat_squared(a);

                    // We're basically done, what remains is to prove that the coefficients next to pow2(i * 51)
                    // are exactly ci_0s (via distributivity and associativity)

                    // let c0_0: u128 = a[0] *  a[0] + 2*( a[1] * a4_19 + a[2] * a3_19);
                    assert(c0_0 == (a[0] *  a[0] + 19 * (2 * (a[2] * a[3]) + 2 * (a[1] * a[4])))) by {
                        // The solver does distributivity on its own.

                        // LHS = a[0] *  a[0] + 2*( a[1] * a4_19 + a[2] * a3_19);
                        //     = a[0] *  a[0] + 2*( a[1] * a4_19 ) + 2 * (a[2] * a3_19);
                        // RHS = a[0] *  a[0] + 19 * (2 * (a[2] * a[3]) + 2 * (a[1] * a[4]))
                        //     = a[0] *  a[0] + 19 * (2 * (a[2] * a[3])) + 19 * (2 * (a[1] * a[4]))

                        // goals
                        // 1) 2 * (a[1] * a4_19) = 19 * (2 * (a[1] * a[4]))
                        // 2) 2 * (a[2] * a3_19) = 19 * (2 * (a[2] * a[3]))

                        assert(2*(a[1] * a4_19) == 19 * (2 * (a[1] * a[4]))) by {
                            lemma_reorder_mul(a[1] as int, a[4] as int);
                        }

                        assert(2*(a[2] * a3_19) == 19 * (2 * (a[2] * a[3]))) by {
                            lemma_reorder_mul(a[2] as int, a[3] as int);
                        }
                    }

                    // let c1_0: u128 = a[3] * a3_19 + 2*( a[0] *  a[1] + a[2] * a4_19);
                    assert(c1_0 == (2 * (a[0] *  a[1]) + 19 * (a[3] * a[3] + 2 * (a[2] * a[4]))))  by {
                        // The solver does distributivity on its own.

                        // LHS = a[3] * a3_19 + 2*( a[0] *  a[1] + a[2] * a4_19)
                        //     = a[3] * a3_19 + 2*( a[0] *  a[1]) + 2 * (a[2] * a4_19)
                        // RHS = 2 * (a[0] *  a[1]) + 19 * (a[3] * a[3] + 2 * (a[2] * a[4]))
                        //     = 2 * (a[0] *  a[1]) + 19 * (a[3] * a[3]) + 19 * (2 * (a[2] * a[4]))

                        // goals: 1) a[3] * a3_19 = 19 * (a[3] * a[3])
                        //        2) 2 * (a[2] * a4_19) = 19 * (2 * (a[2] * a[4]))

                        assert(a[3] * a3_19 == 19 * (a[3] * a[3])) by {
                            lemma_mul_is_associative(a[3] as int, a[3] as int, 19);
                        }

                        assert(2*(a[2] * a4_19) == 19 * (2 * (a[2] * a[4]))) by {
                            lemma_reorder_mul(a[2] as int, a[4] as int);
                        }
                    }

                    // let c2_0: u128 = a[1] *  a[1] + 2*( a[0] *  a[2] + a[4] * a3_19);
                    assert(c2_0 == (a[1] * a[1] + 2 * (a[0] *  a[2]) + 19 * (2 * (a[3] * a[4]))))  by {
                        // The solver does distributivity on its own.

                        // LHS = a[1] * a[1] + 2 * (a[0] *  a[2] + a[4] * a3_19)
                        //     = a[1] * a[1] + 2 * (a[0] *  a[2]) +  2 * (a[4] * a3_19)
                        // RHS = a[1] * a[1] + 2 * (a[0] *  a[2]) + 19 * (2 * (a[3] * a[4]))

                        // goals: 2 * (a[4] * a3_19) = 19 * (2 * (a[3] * a[4]))

                        assert(2 * (a[4] * a3_19) == 19 * (2 * (a[3] * a[4]))) by {
                            lemma_mul_is_associative(a[4] as int, a[3] as int, 19);
                        }
                    }

                    // let c3_0: u128 = a[4] * a4_19 + 2*( a[0] *  a[3] + a[1] *  a[2]);
                    assert(c3_0 == (2 * (a[1] *  a[2]) + 2 * (a[0] *  a[3]) + 19 * (a[4] * a[4])))  by {
                        // The solver does distributivity on its own.

                        // LHS = a[4] * a4_19 + 2 * (a[0] *  a[3] + a[1] *  a[2])
                        //     = a[4] * a4_19 + 2 * (a[0] *  a[3]) + 2 * (a[1] *  a[2])
                        // RHS = 2 * (a[1] *  a[2]) + 2 * (a[0] *  a[3]) + 19 * (a[4] * a[4])

                        // goals: a[4] * a4_19 = 19 * (a[4] * a[4])

                        assert(a[4] * a4_19 == 19 * (a[4] * a[4])) by {
                            lemma_mul_is_associative(a[4] as int, a[4] as int, 19);
                        }
                    }

                    // let c4_0: u128 = a[2] *  a[2] + 2*( a[0] *  a[4] + a[1] *  a[3]);
                    assert(c4_0 == (a[2] * a[2] + 2 * (a[1] * a[3]) + 2 * (a[0] * a[4])))  by {
                        // The solver does distributivity on its own.

                        // LHS = a[2] * a[2] + 2 * (a[0] * a[4] + a[1] * a[3])
                        //     = a[2] * a[2] + 2 * (a[0] * a[4]) + 2 * (a[1] * a[3])
                        // RHS = a[2] * a[2] + 2 * (a[1] * a[3]) + 2 * (a[0] * a[4])

                        // goals: none
                    }
                }

                let a_pow_2i_int = pow(as_nat(self.limbs) as int, pow2(i as nat));
                assert(a_pow_2i_int >= 0) by {
                    lemma_pow_nat_is_nat(as_nat(self.limbs), i as nat);
                }
                let a_pow_2i: nat = a_pow_2i_int as nat;

                assert(as_nat(a_hat) % p() ==
                    ((as_nat(a) % p()) * (as_nat(a) % p())) % p()
                ) by {
                    lemma_mul_mod_noop(as_nat(a) as int, as_nat(a) as int, p() as int);
                }

                // (a_pow_2i % p)^2 % p = (a_pow_2i^2) % p
                lemma_mul_mod_noop(a_pow_2i as int, a_pow_2i as int, p() as int);

                // We know, by the loop inv, that
                // as_nat(a) % p == a_pow_2i % p
                // and, by the above
                // as_nat(a_hat) % p  = (as_nat(a) * as_nat(a)) % p = (a_pow_2i ^ 2)) % p
                // It suffices to prove that
                // (v^(2^i))^2 = v^(2^(i + 1))
                lemma_pow2_square(as_nat(self.limbs) as int, i as nat);
            }
            // Precondition: assume input limbs a[i] are bounded as
            //
            // a[i] < 2^(51 + b)
            //
            // where b is a real parameter measuring the "bit excess" of the limbs.

            // Precomputation: 64-bit multiply by 19.
            //
            // This fits into a u64 whenever 51 + b + lg(19) < 64.
            //
            // Since 51 + b + lg(19) < 51 + 4.25 + b
            //                       = 55.25 + b,
            // this fits if b < 8.75.
            let a3_19 = 19 * a[3];
            let a4_19 = 19 * a[4];

            // Multiply to get 128-bit coefficients of output.
            //
            // The 128-bit multiplications by 2 turn into 1 slr + 1 slrd each,
            // which doesn't seem any better or worse than doing them as precomputations
            // on the 64-bit inputs.
            let     c0: u128 = m(a[0],  a[0]) + 2*( m(a[1], a4_19) + m(a[2], a3_19) );
            let mut c1: u128 = m(a[3], a3_19) + 2*( m(a[0],  a[1]) + m(a[2], a4_19) );
            let mut c2: u128 = m(a[1],  a[1]) + 2*( m(a[0],  a[2]) + m(a[4], a3_19) );
            let mut c3: u128 = m(a[4], a4_19) + 2*( m(a[0],  a[3]) + m(a[1],  a[2]) );
            let mut c4: u128 = m(a[2],  a[2]) + 2*( m(a[0],  a[4]) + m(a[1],  a[3]) );

            // Same bound as in multiply:
            //    c[i] < 2^(102 + 2*b) * (1+i + (4-i)*19)
            //         < 2^(102 + lg(1 + 4*19) + 2*b)
            //         < 2^(108.27 + 2*b)
            //
            // The carry (c[i] >> 51) fits into a u64 when
            //    108.27 + 2*b - 51 < 64
            //    2*b < 6.73
            //    b < 3.365.
            //
            // So we require b < 3 to ensure this fits.
            // DISABLED DUE TO NO VERUS SUPPORT FOR PANICS
            // debug_assert!(a[0] < (1 << 54));
            // debug_assert!(a[1] < (1 << 54));
            // debug_assert!(a[2] < (1 << 54));
            // debug_assert!(a[3] < (1 << 54));
            // debug_assert!(a[4] < (1 << 54));

            // const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1; // already defined

            // Casting to u64 and back tells the compiler that the carry is bounded by 2^64, so
            // that the addition is a u128 + u64 rather than u128 + u128.
            c1 += ((c0 >> 51) as u64) as u128;
            a[0] = (c0 as u64) & LOW_51_BIT_MASK;

            c2 += ((c1 >> 51) as u64) as u128;
            a[1] = (c1 as u64) & LOW_51_BIT_MASK;

            c3 += ((c2 >> 51) as u64) as u128;
            a[2] = (c2 as u64) & LOW_51_BIT_MASK;

            c4 += ((c3 >> 51) as u64) as u128;
            a[3] = (c3 as u64) & LOW_51_BIT_MASK;

            let carry: u64 = (c4 >> 51) as u64;
            a[4] = (c4 as u64) & LOW_51_BIT_MASK;

            // To see that this does not overflow, we need a[0] + carry * 19 < 2^64.
            //
            // c4 < a2^2 + 2*a0*a4 + 2*a1*a3 + (carry from c3)
            //    < 2^(102 + 2*b + lg(5)) + 2^64.
            //
            // When b < 3 we get
            //
            // c4 < 2^110.33  so that carry < 2^59.33
            //
            // so that
            //
            // a[0] + carry * 19 < 2^51 + 19 * 2^59.33 < 2^63.58
            //
            // and there is no overflow.
            a[0] += carry * 19;

            // Now a[1] < 2^51 + 2^(64 -51) = 2^51 + 2^13 < 2^(51 + epsilon).
            a[1] += a[0] >> 51;
            a[0] &= LOW_51_BIT_MASK;

            // Now all a[i] < 2^(51 + epsilon) and a = self^(2^k).
        }

        // ADAPTED CODE LINE: limbs is now a named field
        FieldElement51{limbs: a}
    }

    /// Returns the square of this field element.
    pub fn square(&self) -> (r: FieldElement51)
        requires
            // The precondition in pow2k loop propagates to here
            forall |i: int| 0 <= i < 5 ==> self.limbs[i] < 1u64 << 54
        ensures
            as_nat(r.limbs) % p() == pow(as_nat(self.limbs) as int, 2) as nat % p()

    {
        proof {
            // pow2(1) == 2
            lemma2_to64();
        }
        self.pow2k(1)
    }

    /// Returns 2 times the square of this field element.
    pub fn square2(&self) -> (r: FieldElement51)
        requires
            // The precondition in pow2k loop propagates to here
            forall |i: int| 0 <= i < 5 ==> self.limbs[i] < 1u64 << 54
        ensures
            as_nat(r.limbs) % p() == (2 * pow(as_nat(self.limbs) as int, 2)) as nat % p()
    {
        let mut square = self.pow2k(1);

        // invisible to Rust, can be referenced in proofs
        // Since square is mut, we save the initial value
        let ghost old_limbs = square.limbs;

        proof {
            // forall |i: int| 0 <= i < 5 ==> 2 * old_limbs[i] <= u64::MAX
            assert forall |i: int| 0 <= i < 5 implies 2 * square.limbs[i] <= u64::MAX by {
                // if LHS < RHS, then 2 * LHS < 2 * RHS
                lemma_mul_left_inequality(2, square.limbs[i] as int, (1u64 << 54) as int);
                assert(2 * (1u64 << 54) <= u64::MAX) by (compute);
            }

            let ka = [
                (2 * square.limbs[0]) as u64,
                (2 * square.limbs[1]) as u64,
                (2 * square.limbs[2]) as u64,
                (2 * square.limbs[3]) as u64,
                (2 * square.limbs[4]) as u64
            ];

            // as_nat(ka) == 2 * as_nat(square.limbs)
            // and
            // as_nat(ka) % p() == (2 * as_nat(square.limbs)) % p()
            as_nat_k(square.limbs, 2);

            // By pow2k ensures:
            // as_nat(square.limbs) % p() == pow(as_nat(self.limbs) as int, pow2(1)) as nat % p()
            // We just need pow2(1) == 2
            lemma2_to64();

            // p > 0
            pow255_gt_19();

            assert(as_nat(ka) % p() ==
                ((2nat % p()) * (as_nat(square.limbs) % p())) % p()
                ==
                ((2nat % p()) * (pow(as_nat(self.limbs) as int, 2) as nat % p())) % p()
            ) by {
                lemma_mul_mod_noop(2, as_nat(square.limbs) as int, p() as int);
            }

            // as_nat(self.limbs)^2 >= 0
            assert(pow(as_nat(self.limbs) as int, 2) >= 0) by {
                lemma_pow_nat_is_nat(as_nat(self.limbs), 1);
            }

            assert(
                ((2nat % p()) * (pow(as_nat(self.limbs) as int, 2) as nat % p())) % p()
                ==
                (2 * (pow(as_nat(self.limbs) as int, 2))) as nat % p()
            ) by {
                lemma_mul_mod_noop(2, pow(as_nat(self.limbs) as int, 2) as int, p() as int);
            }

            assert(as_nat(ka) % p() == (2 * (pow(as_nat(self.limbs) as int, 2))) as nat % p());
        }

        for i in 0..5
            invariant
                forall |j: int| 0 <= j < 5 ==> old_limbs[j] < (1u64 << 54),
                forall |j: int| 0 <= j < i ==> #[trigger] square.limbs[j] == 2 * old_limbs[j],
                forall |j: int| i <= j < 5 ==> #[trigger] square.limbs[j] == old_limbs[j],
        {
            proof {
                assert(2 * (1u64 << 54) <= u64::MAX) by (compute);
                lemma_mul_strict_inequality(square.limbs[i as int] as int, (1u64 << 54) as int, 2);
            }

            square.limbs[i] *= 2;
        }

        square
    }
}

fn main()
{}

}
