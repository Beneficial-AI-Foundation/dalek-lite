# Compatibility Approaches in Curve25519-Dalek-Lite

Since the requested branches `compat_reset2`, `compat_reset`, and `compatibility` don't exist in the repository, this document provides a comprehensive comparison of the various compatibility approaches found in the current codebase.

## Overview

The curve25519-dalek-lite repository implements several compatibility strategies to maintain backwards compatibility while introducing new features and verification systems.

## 1. Legacy Compatibility Feature

### Implementation
- **Feature Flag**: `legacy_compatibility`
- **Location**: `curve25519-dalek/Cargo.toml`
- **Purpose**: Maintains compatibility with older API usage patterns

### Key Components

#### Scalar::from_bits Function
```rust
#[cfg(feature = "legacy_compatibility")]
pub const fn from_bits(bytes: [u8; 32]) -> Scalar {
    let mut s = Scalar { bytes };
    // Ensure invariant #1 holds. That is, make s < 2^255 by masking the high bit.
    s.bytes[31] &= 0b0111_1111;
    s
}
```

**Characteristics:**
- Gated behind `legacy_compatibility` feature
- Allows construction of potentially unreduced scalars
- Maintains arithmetic compatibility with legacy code
- **Warning**: Arithmetic operations may be broken with unreduced scalars

### Usage Warning
From the documentation:
> "Enables `Scalar::from_bits`, which allows the user to build unreduced scalars whose arithmetic is broken. Do not use this unless you know what you're doing."

## 2. Verus Verification System Compatibility

### Implementation Strategy
The codebase includes extensive modifications to maintain compatibility with the Verus verification system while preserving original functionality.

### Key Modifications

#### Type Compatibility Wrappers
```rust
/*** <VERIFICATION NOTE> External type specification for subtle::CtOption to make it compatible with Verus </VERIFICATION NOTE> ***/
#[verifier::external_body]
fn ct_option_new<T>(value: T, choice: Choice) -> CtOption<T> {
    CtOption::new(value, choice)
}
```

#### Backend Type Focus
```rust
/*** <VERIFICATION NOTE> Focus on u64; removed all other backend types </VERIFICATION NOTE> ***/
type UnpackedScalar = backend::serial::u64::scalar::Scalar52;
```

#### Code Pattern Adaptations
Multiple patterns adapted for Verus compatibility:

1. **Manual Vector Construction**
   ```rust
   // VERIFICATION NOTE: Build vec manually instead of vec![one; n] for Verus compatibility
   ```

2. **Index-based Loops**
   ```rust
   // VERIFICATION NOTE: Rewritten with index loop instead of .zip() for Verus compatibility
   ```

3. **Manual Iteration**
   ```rust
   // VERIFICATION NOTE: Manual reverse loop instead of .rev() for Verus compatibility
   ```

4. **Function Structure**
   ```rust
   // VERIFICATION NOTE: Moved helper functions outside for Verus compatibility
   ```

## 3. API Evolution and Backwards Compatibility

### Major Changes (v4.0.0)
From CHANGELOG.md:

#### Breaking Changes
- `Scalar::from_canonical_bytes` now returns `CtOption`
- `Scalar::is_canonical` now returns `Choice`
- Remove `Scalar::from_bytes_clamped` and `Scalar::reduce`
- Deprecate and feature-gate `Scalar::from_bits` behind `legacy_compatibility`

#### Compatibility Preservation
- Replace methods `Scalar::{zero, one}` with constants `Scalar::{ZERO, ONE}`
- Add new traits requirement: `use curve25519_dalek::traits::BasepointTable`

### Feature Flag Strategy
```toml
[features]
default = ["alloc", "precomputed-tables", "zeroize"]
alloc = ["zeroize?/alloc"]
precomputed-tables = []
legacy_compatibility = []
group = ["dep:group", "rand_core"]
group-bits = ["group", "ff/bits"]
digest = ["dep:digest"]
```

## 4. Backend Compatibility

### Build System Compatibility
The build system supports multiple compatibility modes:

#### Architecture Detection
```rust
fn is_capable_simd(arch: &str, bits: DalekBits) -> bool {
    arch == "x86_64" && bits == DalekBits::Dalek64
}
```

#### Deterministic Backend Selection
- Automatic selection between `u32` and `u64` backends
- SIMD backend selection when supported
- Override mechanisms via cfg attributes

## 5. Comparison Summary

### Compatibility Approach Matrix

| Approach | Purpose | Scope | Breaking Changes | User Control |
|----------|---------|-------|------------------|--------------|
| **Legacy Compatibility** | Preserve old APIs | Limited to specific functions | Minimal | Feature flag |
| **Verus Compatibility** | Enable formal verification | Extensive code modifications | None (wrapped) | Build-time |
| **API Evolution** | Modern, safer interfaces | Public API surface | Managed via SemVer | Version selection |
| **Backend Compatibility** | Cross-platform support | Build system & runtime | None | Build configuration |

### Trade-offs Analysis

#### Legacy Compatibility
- **Pros**: Zero migration effort for old code
- **Cons**: Potential arithmetic correctness issues
- **Recommendation**: Use only when absolutely necessary

#### Verus Compatibility  
- **Pros**: Formal verification, mathematically sound
- **Cons**: Code complexity, build-time overhead
- **Recommendation**: Essential for security-critical applications

#### API Evolution
- **Pros**: Modern idioms, better safety guarantees
- **Cons**: Migration effort required
- **Recommendation**: Preferred for new projects

## 6. Migration Recommendations

### From Legacy APIs
1. Audit usage of `Scalar::from_bits`
2. Replace with `Scalar::from_bytes_mod_order` where possible
3. Use feature flags during transition period

### For Verification
1. Enable Verus-compatible build configurations
2. Review verification annotations
3. Test with formal verification tools

### For New Projects
1. Use default features without `legacy_compatibility`
2. Follow modern API patterns
3. Consider verification requirements early

## Conclusion

The curve25519-dalek-lite repository demonstrates a multi-layered approach to compatibility:

1. **Selective Legacy Support**: Via feature flags for dangerous but necessary compatibility
2. **Verification Integration**: Transparent adaptation for formal verification systems  
3. **Evolutionary API Design**: Careful deprecation and migration paths
4. **Platform Flexibility**: Automatic backend selection with override capabilities

This approach balances the competing demands of safety, verification, performance, and backwards compatibility while providing clear migration paths for users.