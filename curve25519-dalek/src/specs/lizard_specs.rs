//! Specifications for the Lizard reversible encoding.
//!
//! Lizard is a *reversible encoding* of 16 bytes (128 bits) into a Ristretto point.
//! It is intended for applications that need to embed a short message into a group
//! element and later recover it **iff** the point was produced by the encoding
//! procedure.
//!
//! Lizard is **not** a hash-to-curve function: it does not model a random oracle
//! into the group.
//!
//! ## Example application: Signal's anonymous credentials
//!
//! Signal's zkgroup library uses Lizard to embed a 16-byte UUID into a
//! Ristretto point. The point can then be encrypted and used in zero-knowledge
//! proofs, while remaining decodable back to the UUID on decryption.
//!
//! ```text
//! // Encoding (uid_struct.rs):
//! let point = RistrettoPoint::lizard_encode::<Sha256>(&uuid_bytes);
//!
//! // Decoding (uid_encryption.rs):
//! match point.lizard_decode::<Sha256>() {
//!     Some(bytes) => { /* recovered UUID */ }
//!     None        => { /* not a Lizard-encoded point */ }
//! }
//! ```
//!
//! ## Mathematical objects and notation
//!
//! - The message is a 16-byte string `m ∈ {0,1}^{128}` (represented as `Seq<u8>` with `len == 16`).
//! - `SHA256 : {0,1}^* → {0,1}^{256}` is modeled as the uninterpreted function
//!   `crate::core_assumes::spec_sha256`.
//! - `F_p` is the prime field with `p = 2^255 - 19`. We represent field elements as `nat` in
//!   `[0, p)` using `fe51_as_canonical_nat`.
//! - `Elligator : F_p → E(F_p)` is the Ristretto Elligator map, modeled as
//!   `spec_elligator_ristretto_flavor`, returning affine Edwards coordinates `(x, y)` in `F_p × F_p`.
//!
//! ## Encoding pipeline (`lizard_encode_verus` / `spec_lizard_encode`)
//!
//! ```text
//!          b(·)              r(·)            Elligator
//!   m  ──────────►  b(m)  ────────►  r(m)  ───────────►  P(m)
//!   16 B            32 B             ∈ F_p               ∈ E(F_p)
//! ```
//!
//!   - `b(m) = mask(splice(SHA256(m), m))` — spec: `spec_lizard_fe_bytes` below
//!     - `SHA256(m)`: 32-byte pseudorandom envelope
//!     - `splice`: overwrite bytes 8..24 with `m` (recoverable payload)
//!     - `mask`: `b[0] &= 254` (positive — Elligator maps ±r identically),
//!       `b[31] &= 63` (below 2²⁵⁴ < p — `from_bytes` injective)
//!   - `r(m) = from_bytes(b(m)) mod p` — spec: `spec_lizard_r` below
//!   - `P(m) = Elligator(r(m))` — spec: `spec_lizard_encode` below
//!
//! ## Decoding pipeline (`lizard_decode_verus` / `spec_lizard_decode`)
//!
//! ```text
//!          Elligator⁻¹          as_bytes          extract         b(mⱼ)==bⱼ?
//!   P  ──────────────►  {r₁..r₈}  ──────►  {b₁..b₈}  ──────►  {m₁..m₈}  ──────────►  m or None
//!   ∈ E(F_p)            ≤ 8 candidates      32 B each         mⱼ=bⱼ[8..24]      1 pass→Some(m)
//!                                                                                 else→None
//! ```
//!
//!   - `Elligator⁻¹`: up to 8 candidate field elements (4 coset reps × 2 signs)
//!   - `as_bytes`: convert each rⱼ to 32-byte string bⱼ
//!   - `extract`: extract mⱼ = bⱼ[8..24]
//!   - `b(mⱼ)==bⱼ?`: verify `b(mⱼ) == bⱼ` (SHA-256 consistency)
//!   - exactly one match → `Some(m)`; zero or ≥2 → `None`
//!
//! Decode returns `None` when `n_found ≠ 1`:
//!
//!   - `n_found == 0` — point was not produced by Lizard (no candidate passes
//!     the SHA-256 consistency check).
//!   - `n_found ≥ 2` — two distinct messages `m₁ ≠ m₂` encode to the same
//!     point. Their `r` values are distinct (bytes 8..24 differ ⟹ `from_bytes`
//!     injective) but land in the same Elligator fiber (≤ 8 field elements per
//!     Ristretto point). Negligible probability — see go-ristretto reference.
//!     This is modeled by `lizard_has_unique_preimage`; `lemma_lizard_roundtrip`
//!     proves correctness conditionally on the absence of such collisions.
//!
//! ## References
//!
//! - Westerbaan, B. (2019). Lizard encoding for Ristretto.
//!   Reference Go implementation (v1.1.0) with algorithm description and
//!   probability analysis for non-decodable inputs:
//!   <https://github.com/bwesterb/go-ristretto/blob/master/ristretto.go>
//!   (see `Point.SetLizard`, `Point.LizardInto`).
//!   The quick Ristretto-Elligator inversion is joint work with Mike Hamburg.
//! - Signal usage: `libsignal/rust/zkgroup/src/crypto/uid_struct.rs` (encode),
//!   `libsignal/rust/zkgroup/src/crypto/uid_encryption.rs` (decode).
//! - Executable code: `crate::lizard::lizard_ristretto`
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::edwards_specs::*;
#[allow(unused_imports)]
use super::field_specs::*;
#[allow(unused_imports)]
use super::field_specs_u64::*;
#[allow(unused_imports)]
use super::ristretto_specs::*;
#[allow(unused_imports)]
use crate::core_assumes::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lizard::lizard_constants;
use vstd::prelude::*;

verus! {

// =============================================================================
// Lizard encoding (16 bytes -> field element bytes -> Ristretto Elligator)
// =============================================================================
/// Construct the 32-byte string `b(m)` used by Lizard before interpreting it as
/// a field element.
///
/// ```text
/// m ──► [b(m)] ──► r(m) ──► P(m)
///        ^^^^
/// ```
///
/// 1. `SHA256(m)` — pseudorandom padding
/// 2. Overwrite bytes 8..24 with `m` — recoverable payload
/// 3. `b[0] &= 254` — ensure positive (Elligator maps ±r identically)
/// 4. `b[31] &= 63` — canonical range (< 2²⁵⁴)
pub open spec fn spec_lizard_fe_bytes(data: Seq<u8>) -> [u8; 32]
    recommends
        data.len() == 16,
{
    let digest = spec_sha256(data);
    let s = Seq::new(
        32,
        |i: int|
            if 8 <= i < 24 {
                data[i - 8]
            } else {
                digest[i]
            },
    );
    let s = s.update(0, s[0] & 254u8);
    let s = s.update(31, s[31] & 63u8);
    seq_to_array_32(s)
}

/// Field element `r(m) ∈ F_p` — deterministic Elligator input derived from `b(m)`.
///
/// ```text
/// m ──► b(m) ──► [r(m)] ──► P(m)
///                 ^^^^
/// ```
pub open spec fn spec_lizard_r(fe_bytes: &[u8; 32]) -> nat {
    fe51_as_canonical_nat(&spec_fe51_from_bytes(fe_bytes))
}

/// Point `P(m) = Elligator(r(m))` — the Lizard encoding.
///
/// ```text
/// m ──► b(m) ──► r(m) ──► [P(m)]
///                          ^^^^^
/// ```
///
/// The message rides inside the Elligator preimage at bytes 8..24.
/// Returns `(x, y) ∈ F_p × F_p`.  Top-level spec for `lizard_encode_verus`.
pub open spec fn spec_lizard_encode(data: Seq<u8>) -> (nat, nat)
    recommends
        data.len() == 16,
{
    spec_elligator_ristretto_flavor(spec_lizard_r(&spec_lizard_fe_bytes(data)))
}

// =============================================================================
// Jacobi quartic ↔ Edwards conversion
// =============================================================================
//
// A Jacobi quartic is an elliptic curve of the form T² = S⁴ + 2αS² + 1,
// birationally equivalent to the Edwards curve but better suited to Elligator.
// The Ristretto Elligator map factors through this quartic:
//
//     r ∈ F_p  ──Elligator──►  (S,T) on quartic  ──►  (x,y) on Edwards
//
// `jacobi_to_edwards_affine` is the second arrow.  Its inverse
// (`to_jacobi_quartic_ristretto` in `lizard_ristretto.rs`) decomposes a
// Ristretto point into 4 Jacobi quartic points — one per coset member in
// self + E[4].  Each Jacobi point (and its dual) may then have an Elligator
// preimage (`elligator_inv` in `jacobi_quartic.rs`), giving up to 8
// candidate field elements for Lizard decoding.
//
// Reference: https://ristretto.group/formulas/elligator.html (forward map),
// https://ristretto.group/details/isogenies.html (Jacobi ↔ Edwards isogeny),
// go-ristretto elligator.go (https://github.com/bwesterb/go-ristretto/blob/v1.2.3/edwards25519/elligator.go)
/// Map from Jacobi quartic point `(S, T)` to affine Edwards coordinates `(x, y)`.
///
/// The Jacobi quartic associated to `−x² + y² = 1 + d·x²·y²` (with `a = −1`) is
/// `T² = S⁴ + 2(a − 2d)·S² + 1`.
///
/// ```text
///   y = (1 − S²) / (1 + S²)
///   x = 2·S / (T · √(ad − 1))
/// ```
///
/// where `√(ad − 1) = √(−d − 1)` is `spec_sqrt_ad_minus_one()`.
///
/// Reference: This is the 2-isogeny θ_{a₂,d₂} from Jacobi quartic to
/// twisted Edwards, given as the composition θ = η∘ψ at
/// https://ristretto.group/details/isogenies.html.
/// Hamburg (2015) "Decaf: Eliminating cofactors through point compression"
/// (https://eprint.iacr.org/2015/673), §3 derives the isogeny in the
/// context of the cofactor-elimination construction.
///
/// Requires `1 + S² ≠ 0` and `T · √(ad−1) ≠ 0` (division denominators).
///
/// Used in:
/// - `to_jacobi_quartic_ristretto` ensures (coset correctness)
/// - `elligator_inv` ensures (round-trip with `spec_elligator_ristretto_flavor`)
pub open spec fn jacobi_to_edwards_affine(s: nat, t: nat) -> (nat, nat)
    recommends
        field_add(1, field_square(s)) != 0,
        field_mul(t, spec_sqrt_ad_minus_one()) != 0,
{
    // y = (1 − S²) / (1 + S²)
    let s_sq = field_square(s);
    let y = field_mul(field_sub(1, s_sq), field_inv(field_add(1, s_sq)));
    // x = 2S / (T · √(ad−1))
    let sqrt_ad_m1 = spec_sqrt_ad_minus_one();
    let x = field_mul(field_mul(2, s), field_inv(field_mul(t, sqrt_ad_m1)));
    (x, y)
}

// =============================================================================
// Algorithmic spec anchors (opaque until exec-to-spec proofs are done)
// =============================================================================
//
// These opaque spec functions model the mathematical output of algorithms that
// are currently connected to their exec implementations via `assume`.  They
// serve as abstract anchors: axioms about Jacobi quartic / Elligator inversion
// correctness are stated purely in terms of these functions, preventing misuse
// with arbitrary values.  Use `reveal(fn_name)` in proof blocks that need to
// inspect the definition.
/// √(id) ∈ F_p — square root of the product i·d, where i = √(−1) and d
/// is the Edwards curve parameter. Used in the s = 0, t = 1 branch of
/// the Elligator inverse: Elligator(√(id)) maps to the identity (0, 1).
pub open spec fn sqrt_id() -> nat {
    fe51_as_canonical_nat(&lizard_constants::SQRT_ID)
}

/// (d + 1)/(d − 1) ∈ F_p — the ratio used in the Elligator inverse to
/// compute a = (t + 1) · (d+1)/(d−1) in the s ≢ 0 branch.
pub open spec fn dp1_over_dm1() -> nat {
    fe51_as_canonical_nat(&lizard_constants::DP1_OVER_DM1)
}

/// Elligator inverse on the Jacobi quartic: (s, t) → (success, r₀).
///
/// Given a Jacobi quartic point (s, t) ∈ J(F_p), attempts to find r₀ ∈ F_p
/// such that Elligator(r₀) maps to the Edwards point θ(s, t).
///
/// Three branches:
///   1. s ≡ 0, t ≡ 1: (true, √(id))  — identity preimage
///   2. s ≡ 0, t ≢ 1: (true, 0)       — coset partner preimage
///   3. s ≢ 0: compute a = (t+1)·(d+1)/(d−1), inv_sq_y = (s⁴ − a²)·i.
///      If inv_sq_y has a nonzero invsqrt y: (true, |(a ± s²)·y|),
///      where ± is the sign of s. Otherwise: (false, 0).
///
/// Reference: Westerbaan (2019) / go-ristretto, based on Hamburg (2015)
///   "Decaf" Appendix C (Elligator inverse on J), reparameterized for
///   Ristretto (ristretto.group/formulas/elligator.html).
///
/// Opaque to prevent solver explosion; use `reveal(spec_elligator_inv)`.
#[verifier::opaque]
pub open spec fn spec_elligator_inv(s: nat, t: nat) -> (bool, nat)
    recommends
        s < p(),
        t < p(),
{
    if field_canonical(s) == 0 {
        if field_canonical(t) == 1 {
            (true, sqrt_id())
        } else {
            (true, 0)
        }
    } else {
        // a = (t + 1) · (d+1)/(d−1)
        let a = field_mul(field_add(t, 1), dp1_over_dm1());
        // s2 = s²
        let s2 = field_square(s);
        // s4 = s⁴
        let s4 = field_square(s2);
        // inv_sq_y = (s⁴ − a²) · i
        let inv_sq_y = field_mul(field_sub(s4, field_square(a)), sqrt_m1());
        // y = 1/√(inv_sq_y)
        let y = nat_invsqrt(inv_sq_y);
        let sq = field_canonical(inv_sq_y) != 0 && is_sqrt_ratio(1, inv_sq_y, y);
        if !sq {
            (false, 0)
        } else {
            // pms2 = is_negative(s) ? −s² : s²
            let pms2 = if is_negative(s) {
                field_neg(s2)
            } else {
                s2
            };
            // x = (a + pms2) · y
            let x = field_mul(field_add(a, pms2), y);
            (true, field_abs(x))
        }
    }
}

/// ma = −2/√(−d−1) ∈ F_p — the x-coordinate scaling factor in the dual
/// isogeny θ̂: E → J for pair 0-1 (Z−Y, Z+Y basis).
pub open spec fn mdouble_invsqrt_a_minus_d() -> nat {
    fe51_as_canonical_nat(&lizard_constants::MDOUBLE_INVSQRT_A_MINUS_D)
}

/// mb = −1/√(1+d) ∈ F_p — the scaling factor for the torsion-rotated
/// pair 2-3 (iZ−X, iZ+X basis) in the dual isogeny θ̂.
pub open spec fn minvsqrt_one_plus_d() -> nat {
    fe51_as_canonical_nat(&lizard_constants::MINVSQRT_ONE_PLUS_D)
}

/// mc ∈ F_p — the t-coordinate value for pair 2-3 in the edge case
/// (X = 0 ∨ Y = 0). Defined by mc · √(ad−1) = 2√(−1).
pub open spec fn midouble_invsqrt_a_minus_d() -> nat {
    fe51_as_canonical_nat(&lizard_constants::MIDOUBLE_INVSQRT_A_MINUS_D)
}

/// Dual isogeny θ̂: E → J applied to the 4-element Ristretto coset.
///
/// Given P = (X:Y:Z:T) on the twisted Edwards curve E_{a,d}, compute
/// 4 Jacobi quartic points [(s₀,t₀), (s₁,t₁), (s₂,t₂), (s₃,t₃)]
/// such that the forward isogeny θ maps each back to a coset member:
///   θ(sᵢ, tᵢ) ∈ { P, P+T₂, P+T₄, P+T₆ }
///
/// Computation:
///   γ     = 1/√(Y⁴ · X² · (Z² − Y²))
///   den₁  = γ · Y²
///   den₂  = −(Z² − Y²) · mb · γ     (mb = −1/√(1+d))
///
///   Pair 0-1 (Z−Y, Z+Y basis):  s₀ = den₁·(Z−Y)·X,  s₁ = −den₁·(Z+Y)·X
///   Pair 2-3 (iZ−X, iZ+X basis): s₂ = den₂·(iZ−X)·Y, s₃ = −den₂·(iZ+X)·Y
///   t-coordinates via  tⱼ = ma · Z · (s_over_x or s_over_y)
///     where ma = −2/√(−d−1).
///
/// Edge case (X = 0 ∨ Y = 0): formulas evaluate to s₀=s₁=0, t₀=t₁=1, s₂=1, s₃=−1, t₂=t₃=mc.
///
/// Reference: Hamburg (2015) "Decaf" §3 (coset), §4.1 (θ̂);
///   ristretto.group/formulas/encoding.html.
///
/// Opaque; use `reveal(spec_to_jacobi_quartic_ristretto)` in proof blocks.
#[verifier::opaque]
pub open spec fn spec_to_jacobi_quartic_ristretto(point: crate::edwards::EdwardsPoint) -> [(
    nat,
    nat,
); 4]
    recommends
        is_well_formed_edwards_point(point),
{
    let (xn, yn, zn, _tn) = edwards_point_as_nat(point);

    // x2 = X²
    let x2 = field_square(xn);
    // y2 = Y²
    let y2 = field_square(yn);
    // y4 = Y⁴
    let y4 = field_square(y2);
    // z2 = Z²
    let z2 = field_square(zn);
    // z_min_y = Z − Y
    let z_min_y = field_sub(zn, yn);
    // z_pl_y = Z + Y
    let z_pl_y = field_add(zn, yn);
    // z2_min_y2 = Z² − Y²
    let z2_min_y2 = field_sub(z2, y2);

    // gamma = 1/√(Y⁴ · X² · (Z² − Y²))
    let gamma = nat_invsqrt(field_mul(field_mul(y4, x2), z2_min_y2));

    // den1 = gamma · Y²
    let den1 = field_mul(gamma, y2);
    // s_over_x = den1 · (Z − Y)
    let s_over_x = field_mul(den1, z_min_y);
    // sp_over_xp = den1 · (Z + Y)
    let sp_over_xp = field_mul(den1, z_pl_y);

    // s0 = (s_over_x) · X
    let s0 = field_mul(s_over_x, xn);
    // s1 = −(sp_over_xp) · X
    let s1 = field_mul(field_neg(sp_over_xp), xn);

    // ma = −2/√(−d − 1)
    let ma = mdouble_invsqrt_a_minus_d();
    // tmp1 = ma · Z
    let tmp1 = field_mul(ma, zn);
    // t0_gen = ma · Z · s_over_x
    let t0_gen = field_mul(tmp1, s_over_x);
    // t1_gen = ma · Z · sp_over_xp
    let t1_gen = field_mul(tmp1, sp_over_xp);

    // neg_z2_min_y2 = −(Z² − Y²)
    let neg_z2_min_y2 = field_neg(z2_min_y2);
    // mb = −1/√(1 + d)
    let mb = minvsqrt_one_plus_d();
    // den2 = −(Z² − Y²) · mb · gamma
    let den2 = field_mul(field_mul(neg_z2_min_y2, mb), gamma);

    // iz = i · Z
    let iz = field_mul(sqrt_m1(), zn);
    // iz_min_x = iZ − X
    let iz_min_x = field_sub(iz, xn);
    // iz_pl_x = iZ + X
    let iz_pl_x = field_add(iz, xn);

    // s_over_y = den2 · (iZ − X)
    let s_over_y = field_mul(den2, iz_min_x);
    // sp_over_yp = den2 · (iZ + X)
    let sp_over_yp = field_mul(den2, iz_pl_x);

    // s2_gen = s_over_y · Y
    let s2_gen = field_mul(s_over_y, yn);
    // s3_gen = −(sp_over_yp) · Y
    let s3_gen = field_mul(field_neg(sp_over_yp), yn);

    // tmp2 = ma · iZ
    let tmp2 = field_mul(ma, iz);
    // t2_gen = ma · iZ · s_over_y
    let t2_gen = field_mul(tmp2, s_over_y);
    // t3_gen = ma · iZ · sp_over_yp
    let t3_gen = field_mul(tmp2, sp_over_yp);

    let x_or_y_zero = xn == 0 || yn == 0;
    let mc = midouble_invsqrt_a_minus_d();

    let t0 = if x_or_y_zero {
        1nat
    } else {
        t0_gen
    };
    let t1 = if x_or_y_zero {
        1nat
    } else {
        t1_gen
    };
    let t2 = if x_or_y_zero {
        mc
    } else {
        t2_gen
    };
    let t3 = if x_or_y_zero {
        mc
    } else {
        t3_gen
    };
    let s2 = if x_or_y_zero {
        1nat
    } else {
        s2_gen
    };
    let s3 = if x_or_y_zero {
        field_neg(1)
    } else {
        s3_gen
    };

    [(s0, t0), (s1, t1), (s2, t2), (s3, t3)]
}

// =============================================================================
// Decoding candidates: P ──JQ──► 4 × (S,T) ──inv + dual──► 8 × (ok, r)
// =============================================================================
/// The 8 candidate `(ok, r)` pairs produced by Elligator inversion over the
/// 4 Jacobi quartic points and their duals.
///
/// For each Jacobi quartic pair `(s_i, t_i)` from
/// `spec_to_jacobi_quartic_ristretto(point)`:
/// - slot `2i`:   `spec_elligator_inv(s_i, t_i)`
/// - slot `2i+1`: `spec_elligator_inv(−s_i, −t_i)`  (the dual)
///
/// When `result[j].0` is true, `result[j].1` is a field element whose forward
/// Elligator image lies in the Ristretto coset of `point`.
pub open spec fn spec_lizard_decode_candidates(point: crate::edwards::EdwardsPoint) -> [(
    bool,
    nat,
); 8]
    recommends
        is_well_formed_edwards_point(point),
{
    let jcs = spec_to_jacobi_quartic_ristretto(point);
    [
        spec_elligator_inv(jcs[0].0, jcs[0].1),
        spec_elligator_inv(field_neg(jcs[0].0), field_neg(jcs[0].1)),
        spec_elligator_inv(jcs[1].0, jcs[1].1),
        spec_elligator_inv(field_neg(jcs[1].0), field_neg(jcs[1].1)),
        spec_elligator_inv(jcs[2].0, jcs[2].1),
        spec_elligator_inv(field_neg(jcs[2].0), field_neg(jcs[2].1)),
        spec_elligator_inv(jcs[3].0, jcs[3].1),
        spec_elligator_inv(field_neg(jcs[3].0), field_neg(jcs[3].1)),
    ]
}

// =============================================================================
// SHA consistency check for decode candidates
// =============================================================================
/// SHA round-trip consistency for a single decode candidate.
///
/// Given a candidate field element value `r ∈ [0, p)`, checks whether the
/// canonical 32-byte encoding of `r` equals `spec_lizard_fe_bytes(m)` where
/// `m` is the 16-byte payload at bytes 8..24. Mirrors the exec-level
/// `buf2 == h` check in `lizard_decode_verus`.
pub open spec fn spec_candidate_sha_consistent(r: nat) -> bool
    recommends
        r < p(),
{
    let b = u8_32_from_nat(r);
    let msg = Seq::new(16, |i: int| b[(8 + i) as int]);
    b == spec_lizard_fe_bytes(msg)
}

/// Count of SHA-consistent candidates for a given point.
///
/// The spec-level equivalent of the exec-level `n_found` loop counter.
/// Each slot contributes 1 if the candidate is valid (`ok == true`) AND
/// its canonical bytes pass the SHA round-trip check.
///
/// Deterministic function of the point — no free parameters.
pub open spec fn spec_sha_consistent_count(point: crate::edwards::EdwardsPoint) -> nat
    recommends
        is_well_formed_edwards_point(point),
{
    let c = spec_lizard_decode_candidates(point);
    (if c[0].0 && spec_candidate_sha_consistent(c[0].1) {
        1nat
    } else {
        0nat
    }) + (if c[1].0 && spec_candidate_sha_consistent(c[1].1) {
        1nat
    } else {
        0nat
    }) + (if c[2].0 && spec_candidate_sha_consistent(c[2].1) {
        1nat
    } else {
        0nat
    }) + (if c[3].0 && spec_candidate_sha_consistent(c[3].1) {
        1nat
    } else {
        0nat
    }) + (if c[4].0 && spec_candidate_sha_consistent(c[4].1) {
        1nat
    } else {
        0nat
    }) + (if c[5].0 && spec_candidate_sha_consistent(c[5].1) {
        1nat
    } else {
        0nat
    }) + (if c[6].0 && spec_candidate_sha_consistent(c[6].1) {
        1nat
    } else {
        0nat
    }) + (if c[7].0 && spec_candidate_sha_consistent(c[7].1) {
        1nat
    } else {
        0nat
    })
}

/// Partial SHA-consistent count for slots `0..j` of a candidate array.
///
/// Recursive accumulator used as the loop invariant in `lizard_decode_verus`
/// to tie the exec-level `n_found` counter to the spec-level count.
/// At `j == 8`, equals `spec_sha_consistent_count(point)`.
pub open spec fn partial_sha_consistent_count(candidates: [(bool, nat); 8], j: int) -> nat
    decreases j,
{
    if j <= 0 {
        0
    } else {
        partial_sha_consistent_count(candidates, j - 1) + if candidates[(j - 1) as int].0
            && spec_candidate_sha_consistent(candidates[(j - 1) as int].1) {
            1nat
        } else {
            0nat
        }
    }
}

// =============================================================================
// Decoding: P ──Elligator⁻¹──► {r₁..r₈} ──as_bytes──► {b₁..b₈} ──check──► m or None
//
//   Elligator⁻¹: up to 8 candidate field elements (4 coset reps × 2 signs)
//   as_bytes:     convert each rⱼ back to 32-byte string bⱼ
//   check:        extract mⱼ = bⱼ[8..24], verify b(mⱼ) == bⱼ  (SHA-256 consistency)
//   result:       exactly one match → Some(m); zero or ≥2 → None
// =============================================================================
/// True iff `encode(data) == point`.
pub open spec fn is_lizard_preimage(data: Seq<u8>, point: (nat, nat)) -> bool
    recommends
        data.len() == 16,
{
    spec_lizard_encode(data) == point
}

/// ∃! m ∈ {0,1}¹²⁸ such that `encode(m) == point`.
///
/// Guards `spec_lizard_decode`: `Some(m)` iff this holds, `None` otherwise.
pub open spec fn lizard_has_unique_preimage(point: (nat, nat)) -> bool {
    exists|data: Seq<u8>|
        data.len() == 16 && #[trigger] is_lizard_preimage(data, point) && forall|data2: Seq<u8>|
            data2.len() == 16 && #[trigger] is_lizard_preimage(data2, point) ==> data2 == data
}

/// Return the unique preimage, or `None` (collision / no preimage).
pub closed spec fn spec_lizard_decode(point: (nat, nat)) -> Option<Seq<u8>> {
    if lizard_has_unique_preimage(point) {
        Some(choose|data: Seq<u8>| data.len() == 16 && #[trigger] is_lizard_preimage(data, point))
    } else {
        None
    }
}

// =============================================================================
// Ristretto-level decoding (over the 4-element coset P + E[4])
// =============================================================================
//
// A Ristretto point is an equivalence class {P, P+T₂, P+T₄, P+T₆}.
// Decoding searches all 4 representatives, so predicates quantify over
// the entire coset:  encode(m) ∈ coset(P).
/// True iff `encode(data)` equals some element of `coset`.
///
/// `data`: 16-byte message.  `coset`: the 4 affine points `{P, P+T₂, P+T₄, P+T₆}`.
pub open spec fn is_lizard_preimage_coset(data: Seq<u8>, coset: [(nat, nat); 4]) -> bool
    recommends
        data.len() == 16,
{
    let enc = spec_lizard_encode(data);
    enc == coset[0] || enc == coset[1] || enc == coset[2] || enc == coset[3]
}

/// ∃! m ∈ {0,1}¹²⁸ such that `encode(m) ∈ coset(x, y)`.
///
/// `(x, y)`: affine Edwards coordinates of any coset representative.
/// Returns `true` iff exactly one such `m` exists.
pub open spec fn lizard_ristretto_has_unique_preimage(x: nat, y: nat) -> bool {
    let coset = ristretto_coset_affine(x, y);
    exists|data: Seq<u8>|
        data.len() == 16 && #[trigger] is_lizard_preimage_coset(data, coset) && forall|
            data2: Seq<u8>,
        |
            data2.len() == 16 && #[trigger] is_lizard_preimage_coset(data2, coset) ==> data2 == data
}

/// Return the unique preimage over `coset(x, y)`, or `None`.
///
/// `(x, y)`: affine Edwards coordinates.  Returns `Some(m)` with `|m| == 16`.
/// Top-level spec for `lizard_decode_verus`.
pub closed spec fn spec_lizard_decode_ristretto(x: nat, y: nat) -> Option<Seq<u8>> {
    let coset = ristretto_coset_affine(x, y);
    if lizard_ristretto_has_unique_preimage(x, y) {
        Some(
            choose|data: Seq<u8>|
                data.len() == 16 && #[trigger] is_lizard_preimage_coset(data, coset),
        )
    } else {
        None
    }
}

// =============================================================================
// Proved properties (point-level)
// =============================================================================
/// Soundness: `decode(P) == Some(m)` ⟹ `encode(m) == P`.
pub proof fn lemma_lizard_decode_sound(point: (nat, nat), data: Seq<u8>)
    ensures
        spec_lizard_decode(point) == Some(data) ==> spec_lizard_encode(data) == point,
{
    reveal(spec_lizard_decode);
}

/// Roundtrip: `decode(encode(m)) == Some(m)`, conditional on no collision.
pub proof fn lemma_lizard_roundtrip(data: Seq<u8>)
    requires
        data.len() == 16,
    ensures
        lizard_has_unique_preimage(spec_lizard_encode(data)) ==> spec_lizard_decode(
            spec_lizard_encode(data),
        ) == Some(data),
{
    reveal(spec_lizard_decode);
    assert(is_lizard_preimage(data, spec_lizard_encode(data)));
}

// =============================================================================
// Proved properties (Ristretto-level)
// =============================================================================
/// Soundness: `decode_ristretto(x, y) == Some(m)` ⟹ `encode(m) ∈ coset(x, y)`.
pub proof fn lemma_lizard_decode_ristretto_sound(x: nat, y: nat, data: Seq<u8>)
    ensures
        spec_lizard_decode_ristretto(x, y) == Some(data) ==> is_lizard_preimage_coset(
            data,
            ristretto_coset_affine(x, y),
        ),
{
    reveal(spec_lizard_decode_ristretto);
}

/// Roundtrip: `decode_ristretto(encode(m)) == Some(m)`, conditional on unique coset preimage.
pub proof fn lemma_lizard_roundtrip_ristretto(data: Seq<u8>)
    requires
        data.len() == 16,
    ensures
        lizard_ristretto_has_unique_preimage(spec_lizard_encode(data).0, spec_lizard_encode(data).1)
            ==> spec_lizard_decode_ristretto(spec_lizard_encode(data).0, spec_lizard_encode(data).1)
            == Some(data),
{
    reveal(spec_lizard_decode_ristretto);
    let enc = spec_lizard_encode(data);
    let coset = ristretto_coset_affine(enc.0, enc.1);
    assert(is_lizard_preimage_coset(data, coset));
}

/// Witness lemma: if `data` is the unique coset preimage, the spec decode returns it.
pub proof fn lemma_lizard_decode_ristretto_witness(x: nat, y: nat, data: Seq<u8>)
    requires
        data.len() == 16,
        is_lizard_preimage_coset(data, ristretto_coset_affine(x, y)),
        lizard_ristretto_has_unique_preimage(x, y),
    ensures
        spec_lizard_decode_ristretto(x, y) == Some(data),
{
    reveal(spec_lizard_decode_ristretto);
}

/// None lemma: if no unique coset preimage exists, the spec decode returns None.
pub proof fn lemma_lizard_decode_ristretto_none(x: nat, y: nat)
    requires
        !lizard_ristretto_has_unique_preimage(x, y),
    ensures
        spec_lizard_decode_ristretto(x, y).is_None(),
{
    reveal(spec_lizard_decode_ristretto);
}

} // verus!
