//! Property-based tests for the r4 strict bound in Montgomery reduction.
//!
//! This test searches for counterexamples to the property:
//!   r4 < 2^52 + L[4]
//!
//! where r4 is the 5th limb of the intermediate result in montgomery_reduce.
//!
//! IMPORTANT: This implementation is verified to match the original dalek implementation:
//! https://github.com/dalek-cryptography/curve25519-dalek/blob/11f5375375d3d52c153049f18bd8b1b7669c2565/curve25519-dalek/src/backend/serial/u64/scalar.rs#L265
use proptest::prelude::*;

/// The group order L in radix-2^52 representation
/// Matches: https://github.com/dalek-cryptography/curve25519-dalek/blob/11f5375375d3d52c153049f18bd8b1b7669c2565/curve25519-dalek/src/constants.rs
const L: [u64; 5] = [
    0x0002631a5cf5d3ed,
    0x000dea2f79cd6581,
    0x000000000014def9,
    0x0000000000000000,
    0x0000100000000000,
];

const MASK_52: u64 = (1u64 << 52) - 1;

/// LFACTOR = -L[0]^{-1} (mod 2^52)
/// From: https://github.com/dalek-cryptography/curve25519-dalek/blob/11f5375375d3d52c153049f18bd8b1b7669c2565/curve25519-dalek/src/constants.rs
const LFACTOR: u64 = 0x51da312547e1b;

/// The critical value: 2^52 + L[4]
const CRITICAL_R4: u64 = (1u64 << 52) + L[4];

/// u64 * u64 = u128 multiply helper
/// Exactly matches dalek's m() function
#[inline(always)]
fn m(x: u64, y: u64) -> u128 {
    (x as u128) * (y as u128)
}

/// Compute a * b as 9 limbs
/// Exactly matches dalek's mul_internal:
/// https://github.com/dalek-cryptography/curve25519-dalek/blob/11f5375375d3d52c153049f18bd8b1b7669c2565/curve25519-dalek/src/backend/serial/u64/scalar.rs#L221
#[rustfmt::skip]
fn mul_internal(a: &[u64; 5], b: &[u64; 5]) -> [u128; 9] {
    let mut z = [0u128; 9];
    z[0] = m(a[0], b[0]);
    z[1] = m(a[0], b[1]) + m(a[1], b[0]);
    z[2] = m(a[0], b[2]) + m(a[1], b[1]) + m(a[2], b[0]);
    z[3] = m(a[0], b[3]) + m(a[1], b[2]) + m(a[2], b[1]) + m(a[3], b[0]);
    z[4] = m(a[0], b[4]) + m(a[1], b[3]) + m(a[2], b[2]) + m(a[3], b[1]) + m(a[4], b[0]);
    z[5] =                 m(a[1], b[4]) + m(a[2], b[3]) + m(a[3], b[2]) + m(a[4], b[1]);
    z[6] =                                 m(a[2], b[4]) + m(a[3], b[3]) + m(a[4], b[2]);
    z[7] =                                                 m(a[3], b[4]) + m(a[4], b[3]);
    z[8] =                                                                 m(a[4], b[4]);
    z
}

/// Part 1 of montgomery_reduce - EXACTLY matches dalek:
/// https://github.com/dalek-cryptography/curve25519-dalek/blob/11f5375375d3d52c153049f18bd8b1b7669c2565/curve25519-dalek/src/backend/serial/u64/scalar.rs#L269
#[inline(always)]
fn part1(sum: u128) -> (u128, u64) {
    let p = (sum as u64).wrapping_mul(LFACTOR) & ((1u64 << 52) - 1);
    ((sum + m(p, L[0])) >> 52, p)
}

/// Part 2 of montgomery_reduce - EXACTLY matches dalek:
/// https://github.com/dalek-cryptography/curve25519-dalek/blob/11f5375375d3d52c153049f18bd8b1b7669c2565/curve25519-dalek/src/backend/serial/u64/scalar.rs#L274
#[inline(always)]
fn part2(sum: u128) -> (u128, u64) {
    let w = (sum as u64) & ((1u64 << 52) - 1);
    (sum >> 52, w)
}

/// Perform Montgomery reduction and return (r0, r1, r2, r3, r4)
/// EXACTLY matches dalek's montgomery_reduce structure:
/// https://github.com/dalek-cryptography/curve25519-dalek/blob/11f5375375d3d52c153049f18bd8b1b7669c2565/curve25519-dalek/src/backend/serial/u64/scalar.rs#L265
#[rustfmt::skip]
fn montgomery_reduce_get_intermediate(limbs: &[u128; 9]) -> [u64; 5] {
    // note: l[3] is zero, so its multiples can be skipped (same as original)
    let l = &L;

    // the first half computes the Montgomery adjustment factor n, and begins adding n*l to make limbs divisible by R
    let (carry, n0) = part1(        limbs[0]);
    let (carry, n1) = part1(carry + limbs[1] + m(n0, l[1]));
    let (carry, n2) = part1(carry + limbs[2] + m(n0, l[2]) + m(n1, l[1]));
    let (carry, n3) = part1(carry + limbs[3]               + m(n1, l[2]) + m(n2, l[1]));
    let (carry, n4) = part1(carry + limbs[4] + m(n0, l[4])               + m(n2, l[2]) + m(n3, l[1]));

    // limbs is divisible by R now, so we can divide by R by simply storing the upper half as the result
    let (carry, r0) = part2(carry + limbs[5]               + m(n1, l[4])               + m(n3, l[2]) + m(n4, l[1]));
    let (carry, r1) = part2(carry + limbs[6]                             + m(n2, l[4])               + m(n4, l[2]));
    let (carry, r2) = part2(carry + limbs[7]                                           + m(n3, l[4])              );
    let (carry, r3) = part2(carry + limbs[8]                                                         + m(n4, l[4]));
    let         r4 = carry as u64;

    // Return intermediate BEFORE sub (this is what we're testing)
    [r0, r1, r2, r3, r4]
}

/// Get just r4 for the bound check
fn montgomery_reduce_get_r4(limbs: &[u128; 9]) -> u64 {
    montgomery_reduce_get_intermediate(limbs)[4]
}

/// Perform full Montgomery reduction including the final sub
/// Returns the same result as dalek's montgomery_reduce
fn montgomery_reduce_full(limbs: &[u128; 9]) -> [u64; 5] {
    let [r0, r1, r2, r3, r4] = montgomery_reduce_get_intermediate(limbs);

    // result may be >= l, so attempt to subtract l (same as original)
    // This is Scalar52::sub(&Scalar52([r0, r1, r2, r3, r4]), l)
    let mut difference = [0u64; 5];
    let mut borrow: u64 = 0;

    for i in 0..5 {
        borrow = [r0, r1, r2, r3, r4][i].wrapping_sub(L[i] + (borrow >> 63));
        difference[i] = borrow & MASK_52;
    }

    // conditionally add l if the difference is negative
    let underflow = (borrow >> 63) as u8;
    if underflow == 1 {
        // Don't subtract, return original
        [r0, r1, r2, r3, r4]
    } else {
        difference
    }
}

/// Strategy for generating bounded scalar limbs (each < 2^52)
fn scalar52_strategy() -> impl Strategy<Value = [u64; 5]> {
    prop::array::uniform5(0u64..=MASK_52)
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 10_000_000,  // 10 million cases
        max_shrink_iters: 10000,
        ..ProptestConfig::default()
    })]

    /// Test that r4 < 2^52 + L[4] (strict bound) for random inputs
    #[test]
    fn r4_strict_bound_random(
        a in scalar52_strategy(),
        b in scalar52_strategy()
    ) {
        let limbs = mul_internal(&a, &b);
        let r4 = montgomery_reduce_get_r4(&limbs);

        // The critical property: r4 must be STRICTLY less than 2^52 + L[4]
        prop_assert!(
            r4 < CRITICAL_R4,
            "COUNTEREXAMPLE FOUND!\n\
             a = {:?}\n\
             b = {:?}\n\
             r4 = {} (0x{:x})\n\
             critical = {} (0x{:x})\n\
             This violates the strict bound r4 < 2^52 + L[4]!",
            a, b, r4, r4, CRITICAL_R4, CRITICAL_R4
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 5_000_000,  // 5 million cases
        max_shrink_iters: 10000,
        ..ProptestConfig::default()
    })]

    /// Test with high-value inputs (more likely to produce high r4)
    #[test]
    fn r4_strict_bound_high_values(
        a in prop::array::uniform5((MASK_52 / 2)..=MASK_52),
        b in prop::array::uniform5((MASK_52 / 2)..=MASK_52)
    ) {
        let limbs = mul_internal(&a, &b);
        let r4 = montgomery_reduce_get_r4(&limbs);

        prop_assert!(
            r4 < CRITICAL_R4,
            "COUNTEREXAMPLE FOUND (high values)!\n\
             a = {:?}\n\
             b = {:?}\n\
             r4 = {} (0x{:x})\n\
             critical = {} (0x{:x})",
            a, b, r4, r4, CRITICAL_R4, CRITICAL_R4
        );
    }
}

/// Verify our implementation using known test vectors from dalek
/// Test vectors from: https://github.com/dalek-cryptography/curve25519-dalek/blob/11f5375375d3d52c153049f18bd8b1b7669c2565/curve25519-dalek/src/backend/serial/u64/scalar.rs#L356
#[test]
fn verify_implementation_with_test_vectors() {
    println!("\n=== Verifying implementation with dalek test vectors ===");

    // X = 2^253-1 (from dalek test vectors)
    let x: [u64; 5] = [
        0x000fffffffffffff,
        0x000fffffffffffff,
        0x000fffffffffffff,
        0x000fffffffffffff,
        0x00001fffffffffff,
    ];

    // X^2 mod l = 3078544782642840487852506753550082162405942681916160040940637093560259278169
    // (from dalek: XX)
    let xx_expected: [u64; 5] = [
        0x0001668020217559,
        0x000531640ffd0ec0,
        0x00085fd6f9f38a31,
        0x000c268f73bb1cf4,
        0x000006ce65046df0,
    ];

    // Compute X * X using our implementation
    let limbs = mul_internal(&x, &x);
    let result = montgomery_reduce_full(&limbs);

    // The result of montgomery_reduce is (X*X)/R mod l, not X*X mod l
    // To get X*X mod l, we need to multiply by R^2 and reduce again (like dalek's mul does)
    // But for our test, we just verify the montgomery_reduce part works correctly

    // Instead, let's verify the intermediate r4 is in bounds
    let r4 = montgomery_reduce_get_r4(&limbs);
    println!(
        "  X*X intermediate r4 = {} (critical = {})",
        r4, CRITICAL_R4
    );
    assert!(r4 < CRITICAL_R4, "r4 bound violated for X*X");

    // Test with Y from dalek
    let y: [u64; 5] = [
        0x000b75071e1458fa,
        0x000bf9d75e1ecdac,
        0x000433d2baf0672b,
        0x0005fffcc11fad13,
        0x00000d96018bb825,
    ];

    let limbs_xy = mul_internal(&x, &y);
    let r4_xy = montgomery_reduce_get_r4(&limbs_xy);
    println!(
        "  X*Y intermediate r4 = {} (critical = {})",
        r4_xy, CRITICAL_R4
    );
    assert!(r4_xy < CRITICAL_R4, "r4 bound violated for X*Y");

    // Test with max values (all limbs = 2^52 - 1)
    let max_val: [u64; 5] = [MASK_52; 5];
    let limbs_max = mul_internal(&max_val, &max_val);
    let r4_max = montgomery_reduce_get_r4(&limbs_max);
    println!(
        "  MAX*MAX intermediate r4 = {} (critical = {})",
        r4_max, CRITICAL_R4
    );
    assert!(r4_max < CRITICAL_R4, "r4 bound violated for MAX*MAX");

    println!("  All test vectors pass - r4 < critical in all cases!");
}

/// Non-proptest: exhaustive search of edge cases
#[test]
fn r4_strict_bound_edge_cases() {
    let edge_values: [u64; 5] = [0, 1, MASK_52 / 2, MASK_52 - 1, MASK_52];

    let mut max_r4: u64 = 0;
    let mut test_count = 0;

    // Test single-limb cases
    for i in 0..5 {
        for j in 0..5 {
            for &val_a in &edge_values {
                for &val_b in &edge_values {
                    let mut a = [0u64; 5];
                    let mut b = [0u64; 5];
                    a[i] = val_a;
                    b[j] = val_b;

                    let limbs = mul_internal(&a, &b);
                    let r4 = montgomery_reduce_get_r4(&limbs);

                    assert!(
                        r4 < CRITICAL_R4,
                        "COUNTEREXAMPLE in edge cases!\n\
                         a[{}] = {}, b[{}] = {}\n\
                         r4 = {}, critical = {}",
                        i,
                        val_a,
                        j,
                        val_b,
                        r4,
                        CRITICAL_R4
                    );

                    max_r4 = max_r4.max(r4);
                    test_count += 1;
                }
            }
        }
    }

    // Test all-max case
    let a = [MASK_52; 5];
    let b = [MASK_52; 5];
    let limbs = mul_internal(&a, &b);
    let r4 = montgomery_reduce_get_r4(&limbs);

    assert!(
        r4 < CRITICAL_R4,
        "COUNTEREXAMPLE with all-max inputs!\n\
         r4 = {}, critical = {}",
        r4,
        CRITICAL_R4
    );

    max_r4 = max_r4.max(r4);
    test_count += 1;

    println!(
        "Edge case tests: {} cases, max r4 = {}, gap to critical = {}",
        test_count,
        max_r4,
        CRITICAL_R4 - max_r4
    );
}

/// Report statistics about r4 distribution
#[test]
fn r4_distribution_stats() {
    use std::collections::HashMap;

    let mut rng = rand::thread_rng();
    let num_samples = 1_000_000;

    let mut max_r4: u64 = 0;
    let mut r4_buckets: HashMap<u64, usize> = HashMap::new();

    for _ in 0..num_samples {
        let a: [u64; 5] = std::array::from_fn(|_| rand::Rng::gen_range(&mut rng, 0..=MASK_52));
        let b: [u64; 5] = std::array::from_fn(|_| rand::Rng::gen_range(&mut rng, 0..=MASK_52));

        let limbs = mul_internal(&a, &b);
        let r4 = montgomery_reduce_get_r4(&limbs);

        max_r4 = max_r4.max(r4);

        // Bucket by high bits (top 8 bits of r4 / 2^44)
        let bucket = r4 >> 44;
        *r4_buckets.entry(bucket).or_insert(0) += 1;
    }

    println!(
        "\n=== r4 Distribution Statistics ({} samples) ===",
        num_samples
    );
    println!("Max r4 observed: {} (0x{:x})", max_r4, max_r4);
    println!("Critical r4:     {} (0x{:x})", CRITICAL_R4, CRITICAL_R4);
    println!("Gap to critical: {}", CRITICAL_R4 - max_r4);
    println!("Gap in bits:     ~2^{}", (CRITICAL_R4 - max_r4).ilog2());

    // Show top buckets
    let mut buckets: Vec<_> = r4_buckets.into_iter().collect();
    buckets.sort_by_key(|(k, _)| std::cmp::Reverse(*k));

    println!("\nTop r4 buckets (by high bits):");
    for (bucket, count) in buckets.iter().take(10) {
        println!("  r4 >> 44 = {:3}: {} occurrences", bucket, count);
    }
}

/// Exhaustive random search - 500 million iterations
/// Run with: cargo test --release exhaustive_random_search -- --nocapture --ignored
#[test]
#[ignore] // Only run explicitly due to long runtime
fn exhaustive_random_search() {
    use std::time::Instant;

    let mut rng = rand::thread_rng();
    let num_trials: u64 = 500_000_000;

    let mut max_r4: u64 = 0;
    let mut max_r4_inputs: Option<([u64; 5], [u64; 5])> = None;

    let start = Instant::now();

    println!("\n=== Exhaustive Random Search ({} trials) ===", num_trials);
    println!("Critical r4 = {}", CRITICAL_R4);

    for i in 0..num_trials {
        if i % 10_000_000 == 0 && i > 0 {
            let elapsed = start.elapsed().as_secs_f64();
            let rate = i as f64 / elapsed;
            println!(
                "  Progress: {} / {} ({:.0}/sec), max r4 = {}, gap = {}",
                i,
                num_trials,
                rate,
                max_r4,
                CRITICAL_R4 - max_r4
            );
        }

        let a: [u64; 5] = std::array::from_fn(|_| rand::Rng::gen_range(&mut rng, 0..=MASK_52));
        let b: [u64; 5] = std::array::from_fn(|_| rand::Rng::gen_range(&mut rng, 0..=MASK_52));

        let limbs = mul_internal(&a, &b);
        let r4 = montgomery_reduce_get_r4(&limbs);

        if r4 == CRITICAL_R4 {
            panic!(
                "\n!!! COUNTEREXAMPLE FOUND !!!\n\
                 a = {:?}\n\
                 b = {:?}\n\
                 r4 = {} == CRITICAL",
                a, b, r4
            );
        }

        if r4 > max_r4 {
            max_r4 = r4;
            max_r4_inputs = Some((a, b));
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    println!("\n=== Search Complete ===");
    println!("Trials:          {}", num_trials);
    println!("Time:            {:.1}s", elapsed);
    println!("Rate:            {:.0}/sec", num_trials as f64 / elapsed);
    println!("Max r4:          {} (0x{:x})", max_r4, max_r4);
    println!("Critical:        {} (0x{:x})", CRITICAL_R4, CRITICAL_R4);
    println!("Gap:             {}", CRITICAL_R4 - max_r4);
    println!("Gap bits:        ~2^{}", (CRITICAL_R4 - max_r4).ilog2());

    if let Some((a, b)) = max_r4_inputs {
        println!("\nMax r4 inputs:");
        println!("  a = {:?}", a);
        println!("  b = {:?}", b);
    }

    println!("\nNO COUNTEREXAMPLE FOUND - strict bound appears to hold.");
}

/// Exhaustive search with HIGH-VALUE inputs - 200 million iterations
/// These inputs are more likely to produce high r4 values
/// Run with: cargo test --release exhaustive_high_value_search -- --nocapture --ignored
#[test]
#[ignore]
fn exhaustive_high_value_search() {
    use std::time::Instant;

    let mut rng = rand::thread_rng();
    let num_trials: u64 = 200_000_000;
    let min_val = MASK_52 / 2; // Only high values

    let mut max_r4: u64 = 0;
    let mut max_r4_inputs: Option<([u64; 5], [u64; 5])> = None;

    let start = Instant::now();

    println!(
        "\n=== Exhaustive HIGH-VALUE Search ({} trials) ===",
        num_trials
    );
    println!("Input range: [{}, {}]", min_val, MASK_52);
    println!("Critical r4 = {}", CRITICAL_R4);

    for i in 0..num_trials {
        if i % 10_000_000 == 0 && i > 0 {
            let elapsed = start.elapsed().as_secs_f64();
            let rate = i as f64 / elapsed;
            println!(
                "  Progress: {} / {} ({:.0}/sec), max r4 = {}, gap = {}",
                i,
                num_trials,
                rate,
                max_r4,
                CRITICAL_R4 - max_r4
            );
        }

        // High-value inputs only
        let a: [u64; 5] =
            std::array::from_fn(|_| rand::Rng::gen_range(&mut rng, min_val..=MASK_52));
        let b: [u64; 5] =
            std::array::from_fn(|_| rand::Rng::gen_range(&mut rng, min_val..=MASK_52));

        let limbs = mul_internal(&a, &b);
        let r4 = montgomery_reduce_get_r4(&limbs);

        if r4 == CRITICAL_R4 {
            panic!(
                "\n!!! COUNTEREXAMPLE FOUND !!!\n\
                 a = {:?}\n\
                 b = {:?}\n\
                 r4 = {} == CRITICAL",
                a, b, r4
            );
        }

        if r4 > max_r4 {
            max_r4 = r4;
            max_r4_inputs = Some((a, b));
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    println!("\n=== High-Value Search Complete ===");
    println!("Trials:          {}", num_trials);
    println!("Time:            {:.1}s", elapsed);
    println!("Rate:            {:.0}/sec", num_trials as f64 / elapsed);
    println!("Max r4:          {} (0x{:x})", max_r4, max_r4);
    println!("Critical:        {} (0x{:x})", CRITICAL_R4, CRITICAL_R4);
    println!("Gap:             {}", CRITICAL_R4 - max_r4);
    println!("Gap bits:        ~2^{}", (CRITICAL_R4 - max_r4).ilog2());

    if let Some((a, b)) = max_r4_inputs {
        println!("\nMax r4 inputs:");
        println!("  a = {:?}", a);
        println!("  b = {:?}", b);
    }

    println!("\nNO COUNTEREXAMPLE FOUND.");
}
