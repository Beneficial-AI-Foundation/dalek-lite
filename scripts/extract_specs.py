#!/usr/bin/env python3
"""
Extract Verus spec functions and verified function contracts for the specs browser.

Outputs JSON with two sections:
  - spec_functions: 56 spec fn definitions (full body)
  - verified_functions: 34 implementation function contracts (signature + requires/ensures only)

Default (hybrid) mode re-extracts live code from .rs source files.

Usage:
    python scripts/extract_specs.py [--output docs/specs_data.json]
    python scripts/extract_specs.py --csv-only [--output docs/specs_data.json]
"""

import argparse
import csv
import json
import os
import re
import sys
from pathlib import Path

GITHUB_BASE = "https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/"

# Regex to match spec fn declarations
SPEC_FN_PATTERN = re.compile(
    r"^(\s*)"
    r"((?:pub(?:\([^)]*\))?\s+)?(?:(?:open|closed|uninterp)\s+)*spec\s+fn)\s+"
    r"(\w+)"
)

# Regex to match regular fn declarations (for verified functions)
IMPL_FN_PATTERN = re.compile(
    r"^(\s*)(?:pub\s+)?fn\s+(\w+)"
)

FUZZY_LINE_RANGE = 40

DEFAULT_SPEC_CSV = "data/libsignal_verus_specs/generated/spec_functions.csv"
DEFAULT_VERIFIED_CSV = "data/libsignal_verus_specs/generated/verified_functions.csv"


# ── Shared helpers ────────────────────────────────────────────────────

def derive_module(filepath: str) -> str:
    """Derive a short module name from a file path."""
    rel = filepath.replace("curve25519-dalek/src/", "")
    rel = rel.replace(".rs", "").replace("/", "::")
    if rel.endswith("::mod"):
        rel = rel[: -len("::mod")]
    return rel


def derive_short_module(filepath: str) -> str:
    """Get just the file stem (edwards, scalar, ristretto, montgomery)."""
    return Path(filepath).stem


def extract_doc_comment(lines: list[str], fn_line_idx: int) -> str:
    """Extract /// doc comment lines immediately above a function."""
    doc_lines = []
    i = fn_line_idx - 1
    while i >= 0 and lines[i].strip().startswith("#["):
        i -= 1
    while i >= 0:
        stripped = lines[i].strip()
        if stripped.startswith("///"):
            doc_lines.insert(0, stripped[3:].strip())
            i -= 1
        else:
            break
    return "\n".join(doc_lines) if doc_lines else ""


def extract_function_body(lines: list[str], start_idx: int) -> tuple[str, int]:
    """Extract full function body by tracking brace depth."""
    body_lines = []
    brace_depth = 0
    found_open_brace = False
    i = start_idx
    while i < len(lines):
        line = lines[i]
        body_lines.append(line)
        for ch in line:
            if ch == "{":
                brace_depth += 1
                found_open_brace = True
            elif ch == "}":
                brace_depth -= 1
        if found_open_brace and brace_depth <= 0:
            return "\n".join(body_lines), i
        i += 1
    return "\n".join(body_lines), i - 1


def dedent_body(body: str, indent: str) -> str:
    if not indent:
        return body
    return "\n".join(
        line[len(indent):] if line.startswith(indent) else line
        for line in body.split("\n")
    )


def extract_signature(lines: list[str], start_idx: int, end_idx: int, indent: str) -> str:
    sig_lines = []
    for si in range(start_idx, min(end_idx + 1, len(lines))):
        sig_line = lines[si]
        if indent and sig_line.startswith(indent):
            sig_line = sig_line[len(indent):]
        sig_lines.append(sig_line)
        if "{" in lines[si]:
            last = sig_lines[-1]
            sig_lines[-1] = last[: last.index("{")].rstrip()
            break
    return re.sub(r"\s+", " ", " ".join(s.strip() for s in sig_lines)).strip()


# ── Source file cache ─────────────────────────────────────────────────

_file_cache: dict[str, list[str] | None] = {}


def _read_file_lines(filepath: str) -> list[str] | None:
    if filepath not in _file_cache:
        try:
            with open(filepath, "r", encoding="utf-8") as f:
                _file_cache[filepath] = f.read().split("\n")
        except (IOError, UnicodeDecodeError) as e:
            print(f"  Warning: Could not read {filepath}: {e}", file=sys.stderr)
            _file_cache[filepath] = None
    return _file_cache[filepath]


# ── Spec function extraction (hybrid) ─────────────────────────────────

def find_spec_fn_in_source(filepath: str, fn_name: str, hint_line: int) -> dict | None:
    lines = _read_file_lines(filepath)
    if lines is None:
        return None

    hint_idx = hint_line - 1
    search_start = max(0, hint_idx - FUZZY_LINE_RANGE)
    search_end = min(len(lines), hint_idx + FUZZY_LINE_RANGE)

    for search_range in [(search_start, search_end), (0, len(lines))]:
        for line_idx in range(search_range[0], search_range[1]):
            match = SPEC_FN_PATTERN.match(lines[line_idx])
            if not match or match.group(3) != fn_name:
                continue
            indent = match.group(1)
            qualifier = match.group(2).strip()
            body, end_idx = extract_function_body(lines, line_idx)
            body = dedent_body(body, indent)
            signature = extract_signature(lines, line_idx, end_idx, indent)
            doc_comment = extract_doc_comment(lines, line_idx)
            return {
                "body": body.rstrip(),
                "signature": signature,
                "doc_comment": doc_comment,
                "line": line_idx + 1,
                "visibility": qualifier,
            }
    return None


def extract_spec_functions(csv_path: str) -> list[dict]:
    """Hybrid extraction of spec functions."""
    specs = []
    found = fell_back = 0

    with open(csv_path, "r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            name = row.get("spec_function", "").strip()
            source_path = row.get("source_path", "").strip()
            source_line = int(row.get("source_line", 0))
            csv_def = row.get("definition", "").strip().replace("\\n", "\n")
            csv_doc = row.get("doc_comment", "").strip()
            math_interp = row.get("math_interpretation", "").strip()
            informal_interp = row.get("informal_interpretation", "").strip()

            module = derive_module(source_path)
            result = find_spec_fn_in_source(source_path, name, source_line)

            if result:
                body = result["body"]
                signature = result["signature"]
                doc_comment = result["doc_comment"] or csv_doc
                actual_line = result["line"]
                visibility = result["visibility"]
                found += 1
            else:
                body = csv_def
                doc_comment = csv_doc
                actual_line = source_line
                first_line = csv_def.split("\n")[0] if csv_def else ""
                signature = first_line[: first_line.index("{")].rstrip() if "{" in first_line else first_line.rstrip()
                signature = re.sub(r"\s+", " ", signature).strip()
                vis_match = re.match(r"((?:pub(?:\([^)]*\))?\s+)?(?:(?:open|closed|uninterp)\s+)*spec\s+fn)", signature)
                visibility = vis_match.group(1).strip() if vis_match else ""
                if csv_def:
                    fell_back += 1
                else:
                    continue

            fn_id = f"{module.replace('::', '__')}__{name}"
            github_link = f"{GITHUB_BASE}{source_path}#L{actual_line}"

            specs.append({
                "id": fn_id,
                "name": name,
                "signature": signature,
                "body": body,
                "file": source_path,
                "line": actual_line,
                "module": module,
                "visibility": visibility,
                "doc_comment": doc_comment,
                "math_interpretation": math_interp,
                "informal_interpretation": informal_interp,
                "github_link": github_link,
                "category": "spec",
            })

    print(f"  Spec functions: {found} from source, {fell_back} from CSV")
    return specs


# ── Contract extraction for verified functions ────────────────────────

def extract_contract_from_source(
    filepath: str, fn_name: str, hint_line: int
) -> dict | None:
    """
    Find a function near hint_line and extract its contract:
    signature + requires + ensures (everything before the opening { of the body).
    """
    lines = _read_file_lines(filepath)
    if lines is None:
        return None

    hint_idx = hint_line - 1
    search_start = max(0, hint_idx - FUZZY_LINE_RANGE)
    search_end = min(len(lines), hint_idx + FUZZY_LINE_RANGE)

    for search_range in [(search_start, search_end), (0, len(lines))]:
        for line_idx in range(search_range[0], search_range[1]):
            # Match fn declarations -- look for fn {name}(
            # Must handle: pub fn name, fn name, pub fn name(
            stripped = lines[line_idx].strip()
            # Check if this line declares the function we're looking for
            fn_pattern = re.search(r'\bfn\s+' + re.escape(fn_name) + r'\s*[\(<]', stripped)
            if not fn_pattern:
                # Also try multiline: fn name(\n
                fn_pattern = re.search(r'\bfn\s+' + re.escape(fn_name) + r'\s*\(', stripped)
                if not fn_pattern:
                    continue

            # Found the function declaration. Now extract the contract
            # (everything from this line up to the opening { of the body)
            contract_lines = []
            indent = lines[line_idx][: len(lines[line_idx]) - len(lines[line_idx].lstrip())]
            requires_clauses = []
            ensures_clauses = []
            current_section = None  # "requires" or "ensures"
            current_clause_lines = []

            i = line_idx
            while i < len(lines):
                raw_line = lines[i]
                # Dedent
                if indent and raw_line.startswith(indent):
                    display_line = raw_line[len(indent):]
                else:
                    display_line = raw_line

                # Check if we've hit the opening brace of the body
                # The body starts with { at the end of requires/ensures block
                brace_stripped = raw_line.lstrip()
                if brace_stripped.startswith("{") and i > line_idx:
                    # We've reached the body -- stop
                    # Flush any pending clause
                    if current_clause_lines:
                        clause_text = " ".join(l.strip() for l in current_clause_lines).strip()
                        if clause_text:
                            if current_section == "requires":
                                requires_clauses.append(clause_text)
                            elif current_section == "ensures":
                                ensures_clauses.append(clause_text)
                    break

                # Check for { appearing at the end of a line (e.g., "ensures foo, {")
                if "{" in raw_line and i > line_idx:
                    # Take everything before the brace
                    pre_brace = display_line[: display_line.index("{")].rstrip()
                    if pre_brace.strip():
                        contract_lines.append(pre_brace)
                        # Also add to clause
                        current_clause_lines.append(pre_brace)
                    # Flush clause
                    if current_clause_lines:
                        clause_text = " ".join(l.strip() for l in current_clause_lines).strip()
                        if clause_text and clause_text not in ("requires", "ensures"):
                            if current_section == "requires":
                                requires_clauses.append(clause_text)
                            elif current_section == "ensures":
                                ensures_clauses.append(clause_text)
                    break

                contract_lines.append(display_line)

                # Track requires/ensures sections
                trimmed = display_line.strip()
                # Strip leading // comments from clause tracking
                clause_line = trimmed
                if clause_line.startswith("//"):
                    clause_line = ""

                if trimmed == "requires" or trimmed.startswith("requires "):
                    # Flush previous clause
                    if current_clause_lines:
                        clause_text = " ".join(l.strip() for l in current_clause_lines).strip()
                        if clause_text and clause_text not in ("requires", "ensures"):
                            if current_section == "requires":
                                requires_clauses.append(clause_text)
                            elif current_section == "ensures":
                                ensures_clauses.append(clause_text)
                    current_section = "requires"
                    current_clause_lines = []
                elif trimmed == "ensures" or trimmed.startswith("ensures "):
                    if current_clause_lines:
                        clause_text = " ".join(l.strip() for l in current_clause_lines).strip()
                        if clause_text and clause_text not in ("requires", "ensures"):
                            if current_section == "requires":
                                requires_clauses.append(clause_text)
                            elif current_section == "ensures":
                                ensures_clauses.append(clause_text)
                    current_section = "ensures"
                    current_clause_lines = []
                elif current_section and clause_line:
                    # If line ends with comma, it's a clause boundary
                    current_clause_lines.append(clause_line)
                    if clause_line.rstrip().endswith(","):
                        clause_text = " ".join(l.strip() for l in current_clause_lines).strip()
                        if clause_text and clause_text not in ("requires", "ensures"):
                            if current_section == "requires":
                                requires_clauses.append(clause_text)
                            elif current_section == "ensures":
                                ensures_clauses.append(clause_text)
                        current_clause_lines = []

                i += 1

            contract_text = "\n".join(contract_lines).rstrip()
            doc_comment = extract_doc_comment(lines, line_idx)
            actual_line = line_idx + 1

            return {
                "contract": contract_text,
                "requires": requires_clauses,
                "ensures": ensures_clauses,
                "doc_comment": doc_comment,
                "line": actual_line,
            }

    return None


def extract_verified_functions(csv_path: str, spec_names: set[str]) -> list[dict]:
    """
    Extract verified function contracts from source, guided by CSV.
    Also detects which spec function names appear in the contract.
    """
    verified = []
    found = 0

    with open(csv_path, "r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            name = row.get("function_name", "").strip()
            source_path = row.get("source_path", "").strip()
            source_line = int(row.get("source_line", 0))
            impl_type = row.get("impl_type", "").strip()
            math_interp = row.get("math_interpretation", "").strip()
            informal_interp = row.get("informal_interpretation", "").strip()

            module = derive_short_module(source_path)
            result = extract_contract_from_source(source_path, name, source_line)

            if result:
                contract = result["contract"]
                requires = result["requires"]
                ensures = result["ensures"]
                doc_comment = result["doc_comment"]
                actual_line = result["line"]
                found += 1
            else:
                print(f"  Warning: {name} not found in {source_path}:{source_line}", file=sys.stderr)
                contract = f"fn {name}(...)  // contract not found in source"
                requires = []
                ensures = []
                doc_comment = ""
                actual_line = source_line

            # Detect referenced spec functions
            contract_text = contract + " " + " ".join(requires) + " " + " ".join(ensures)
            referenced = sorted([s for s in spec_names if re.search(r'\b' + re.escape(s) + r'\b', contract_text)])

            # Build unique ID: include impl_type to disambiguate (e.g., edwards::compress vs ristretto::compress)
            type_prefix = impl_type.lower().replace("::", "_") if impl_type else module
            fn_id = f"{type_prefix}__{name}"
            github_link = f"{GITHUB_BASE}{source_path}#L{actual_line}"

            # Display name includes the impl type
            display_name = f"{impl_type}::{name}" if impl_type else name

            verified.append({
                "id": fn_id,
                "name": name,
                "display_name": display_name,
                "impl_type": impl_type,
                "contract": contract,
                "requires": requires,
                "ensures": ensures,
                "referenced_specs": referenced,
                "file": source_path,
                "line": actual_line,
                "module": module,
                "doc_comment": doc_comment,
                "math_interpretation": math_interp,
                "informal_interpretation": informal_interp,
                "github_link": github_link,
                "category": "verified",
            })

    print(f"  Verified functions: {found} contracts extracted from source")
    return verified


# ── Main ──────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="Extract Verus specs for the browser website")
    parser.add_argument("--output", "-o", default="docs/specs_data.json")
    parser.add_argument("--spec-csv", default=DEFAULT_SPEC_CSV)
    parser.add_argument("--verified-csv", default=DEFAULT_VERIFIED_CSV)
    parser.add_argument("--csv-only", action="store_true", help="Skip source re-extraction")
    parser.add_argument("--src-dir", default="curve25519-dalek/src")
    args = parser.parse_args()

    # 1. Extract spec functions
    if not os.path.exists(args.spec_csv):
        print(f"Error: {args.spec_csv} not found.", file=sys.stderr)
        sys.exit(1)

    print(f"Extracting spec functions from {args.spec_csv}...")
    spec_functions = extract_spec_functions(args.spec_csv)
    spec_functions.sort(key=lambda s: (s["module"], s["name"]))

    # Build set of spec function names for cross-referencing
    spec_names = {s["name"] for s in spec_functions}

    # 2. Extract verified function contracts
    if os.path.exists(args.verified_csv):
        print(f"Extracting verified function contracts from {args.verified_csv}...")
        verified_functions = extract_verified_functions(args.verified_csv, spec_names)
        verified_functions.sort(key=lambda s: (s["module"], s["display_name"]))
    else:
        print(f"Warning: {args.verified_csv} not found, skipping verified functions.", file=sys.stderr)
        verified_functions = []

    # 3. Output combined JSON
    output = {
        "spec_functions": spec_functions,
        "verified_functions": verified_functions,
    }

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2, ensure_ascii=False)

    # Summary
    spec_mods = sorted(set(s["module"] for s in spec_functions))
    print(f"\n{len(spec_functions)} spec functions from {len(spec_mods)} modules")
    verified_mods = sorted(set(s["module"] for s in verified_functions))
    print(f"{len(verified_functions)} verified functions from {len(verified_mods)} modules")

    # Show cross-reference stats
    total_refs = sum(len(v["referenced_specs"]) for v in verified_functions)
    unique_refs = set()
    for v in verified_functions:
        unique_refs.update(v["referenced_specs"])
    print(f"{total_refs} total spec references, {len(unique_refs)} unique spec functions referenced")
    print(f"\nOutput written to {out_path}")


if __name__ == "__main__":
    main()
