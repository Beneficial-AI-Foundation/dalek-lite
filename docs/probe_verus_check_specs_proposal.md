# Proposal: Replace `analyze_verus_specs_proofs.py` with `probe-verus check-specs`

**Date:** 2026-01-27  
**Status:** Discussion / Proposal

## Background

The `scripts/analyze_verus_specs_proofs.py` script uses regex-based parsing to analyze Verus specs and proofs in the codebase. This document explores replacing it with a new `probe-verus check-specs` command that leverages `verus-syn` for proper AST parsing.

## Current Script: `analyze_verus_specs_proofs.py`

### Purpose
Static analysis to detect which functions have Verus specs/proofs (without running verification).

### Usage in Workflows

1. **`deploy-pages.yml`** (line 63): Generates CSV for the website dashboard on every push to main
2. **`proof-counter.yml`** (line 20): CI check on PRs to ensure CSV generation works

### Input
`functions_to_track.csv` - a curated list of functions with columns:
- `function` (e.g., `MontgomeryPoint::mul_base(&Scalar)`)
- `module` (e.g., `curve25519_dalek::montgomery`)
- `impl_block` (e.g., `Identity for ProjectivePoint`) - for disambiguation

### Output
`outputs/curve25519_functions.csv` with columns:
- `function`, `module`, `link`, `has_spec`, `has_proof`

### Detection Logic (via regex)
- **`has_spec`**: function has `requires` or `ensures` clauses, OR has `#[verifier::external_body]`
- **`has_proof`**: has_spec AND no `assume`/`admit` in body AND no `#[verifier::exec_allows_no_decreases_clause]`

### Limitations
- Regex-based parsing can have false positives (matches in comments/strings)
- Doesn't properly handle nested structures
- Ad-hoc handling of `verus!` macro blocks
- ~800 lines of Python for what should be straightforward AST queries

---

## Proposed Solution: `probe-verus check-specs`

### Why `verus-syn` is Better

`probe-verus` already uses `verus-syn` for AST parsing. Looking at `verus_parser.rs`, the `FunctionInfo` struct already captures:

```rust
pub struct FunctionInfo {
    pub name: String,
    pub file: Option<String>,
    pub spec_text: SpecText,           // line ranges
    pub specified: bool,               // has requires OR ensures
    pub has_requires: bool,
    pub has_ensures: bool,
    pub has_trusted_assumption: bool,  // contains assume() or admit()
    // ...
}
```

**Mapping to CSV columns:**
- `has_spec` = `specified` (has `requires` or `ensures`)
- `has_proof` = `specified && !has_trusted_assumption`

**Benefits of `verus-syn`:**
1. Properly parses the AST (no false positives from comments/strings)
2. Handles `verus!` and `cfg_if!` macro blocks correctly
3. Distinguishes spec fn vs proof fn vs exec fn
4. Extracts actual spec clause line ranges
5. Already battle-tested in `probe-verus`

### Proposed CLI

```bash
probe-verus check-specs ./curve25519-dalek \
  --seed functions_to_track.csv \
  --output outputs/curve25519_functions.csv \
  --format csv \
  --github-repo "Beneficial-AI-Foundation/dalek-lite"
```

### What Needs to be Added to `probe-verus`

1. **In `verus_parser.rs`**: Add `has_external_body: bool` to `FunctionInfo` by checking for `#[verifier::external_body]` attribute

2. **New command `check-specs`** that:
   - Parses all functions using existing `verus-syn` infrastructure
   - Optionally filters against a seed file (CSV with function, module, impl_block)
   - Matches functions by module path + impl context for disambiguation
   - Generates GitHub links (repo URL + file path + line number)
   - Outputs CSV with columns: `function, module, link, has_spec, has_proof`

3. **Update `main.rs`** to add the new subcommand

---

## Comparison

| Feature | Python Script (regex) | `probe-verus check-specs` (verus-syn) |
|---------|----------------------|--------------------------------------|
| **Parsing accuracy** | Regex (error-prone) | AST (accurate) |
| **Handles comments** | May have false positives | Correct |
| **verus! macro** | Ad-hoc handling | Proper parsing |
| **cfg_if! macro** | Not handled | Proper parsing |
| **External body detection** | Regex | Attribute check |
| **assume/admit detection** | Regex in body | AST body traversal |
| **Maintenance** | ~800 lines Python | Reuses existing Rust code |
| **Dependencies** | Python + beartype | Already in probe-verus |
| **Speed** | Fast | Fast (no verification) |

---

## Comparison with `probe-verus verify`

Note: `check-specs` is different from `verify`:

| Feature | `check-specs` (proposed) | `verify` (existing) |
|---------|-------------------------|---------------------|
| **Runs Verus** | No | Yes |
| **Speed** | Fast (seconds) | Slow (minutes) |
| **Purpose** | Static analysis of specs | Actual verification |
| **Output** | has_spec/has_proof heuristic | verified/failed/sorries |

The `verify` command gives ground truth (did Verus accept the proof?), but `check-specs` is sufficient for dashboard tracking and is much faster.

---

## Migration Path

1. Implement `probe-verus check-specs` command
2. Test output matches current Python script for existing functions
3. Update `deploy-pages.yml` to use `probe-verus check-specs`
4. Update `proof-counter.yml` similarly
5. Deprecate `analyze_verus_specs_proofs.py`

---

## Open Questions

1. **Seed file format**: Keep CSV or switch to JSON?
2. **Impl block disambiguation**: How does `probe-verus` currently handle this? May need SCIP symbols.
3. **External body**: Need to add attribute detection to `verus_parser.rs`
4. **GitHub links**: Should this be in probe-verus or handled by the workflow?

---

## Files Referenced

- `scripts/analyze_verus_specs_proofs.py` - Current Python script
- `functions_to_track.csv` - Seed file with tracked functions
- `.github/workflows/deploy-pages.yml` - Dashboard deployment
- `.github/workflows/proof-counter.yml` - PR CI check
- `probe-verus/src/verus_parser.rs` - verus-syn parsing
- `probe-verus/src/commands/functions.rs` - list-functions command
- `probe-verus/src/main.rs` - CLI definition
