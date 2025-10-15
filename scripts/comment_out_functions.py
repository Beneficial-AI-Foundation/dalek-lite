#!/usr/bin/env python3
"""
Script to automatically comment out unused functions in Rust files.
For each function, it comments it out, runs cargo check, and either keeps or reverts the change.
"""

import argparse
import subprocess
import re
import sys
from pathlib import Path
from typing import List, Tuple, Optional

def find_function_bounds(lines: List[str], start_idx: int) -> Optional[Tuple[int, int]]:
    """
    Find the start and end line indices for a function starting at start_idx.
    Returns (doc_start, fn_end) where doc_start includes /// comments before fn.
    """
    # Find the start of doc comments
    doc_start = start_idx
    i = start_idx - 1
    while i >= 0 and (lines[i].strip().startswith('///') or
                       lines[i].strip().startswith('#[') or
                       lines[i].strip() == ''):
        if lines[i].strip().startswith('///') or lines[i].strip().startswith('#['):
            doc_start = i
        i -= 1

    # Find the end of the function by tracking braces
    brace_count = 0
    in_function = False
    fn_end = start_idx

    for i in range(start_idx, len(lines)):
        line = lines[i]

        # Skip comments and strings (simple heuristic)
        cleaned = re.sub(r'//.*', '', line)
        cleaned = re.sub(r'"[^"]*"', '', cleaned)

        for char in cleaned:
            if char == '{':
                brace_count += 1
                in_function = True
            elif char == '}':
                brace_count -= 1
                if in_function and brace_count == 0:
                    return (doc_start, i)

        fn_end = i

    return None

def find_impl_block_bounds(lines: List[str], start_idx: int) -> Optional[Tuple[int, int]]:
    """
    Find the start and end line indices for an impl block starting at start_idx.
    Returns (doc_start, impl_end) where doc_start includes /// and #[] comments before impl.
    """
    # Find the start of doc comments
    doc_start = start_idx
    i = start_idx - 1
    while i >= 0 and (lines[i].strip().startswith('///') or
                       lines[i].strip().startswith('#[') or
                       lines[i].strip() == ''):
        if lines[i].strip().startswith('///') or lines[i].strip().startswith('#['):
            doc_start = i
        i -= 1

    # Find the end of the impl block by tracking braces
    brace_count = 0
    in_block = False
    impl_end = start_idx

    for i in range(start_idx, len(lines)):
        line = lines[i]

        # Skip comments and strings (simple heuristic)
        cleaned = re.sub(r'//.*', '', line)
        cleaned = re.sub(r'"[^"]*"', '', cleaned)

        for char in cleaned:
            if char == '{':
                brace_count += 1
                in_block = True
            elif char == '}':
                brace_count -= 1
                if in_block and brace_count == 0:
                    return (doc_start, i)

        impl_end = i

    return None

def find_functions_and_impls(filepath: str) -> List[Tuple[int, int, str, str]]:
    """
    Find all function definitions and impl blocks in a Rust file.
    Returns list of (start_line, end_line, name, type) tuples where type is 'fn' or 'impl'.
    """
    with open(filepath, 'r') as f:
        lines = f.readlines()

    items = []

    for i, line in enumerate(lines):
        # Skip already commented out lines
        stripped = line.strip()
        if stripped.startswith('//'):
            continue

        # Match impl blocks (impl Foo, impl Trait for Foo, impl<T> Foo<T>, etc.)
        impl_match = re.search(r'\bimpl\b(?:\s*<[^>]*>)?\s+(?:(?:\w+\s+for\s+)?(\w+))', line)
        if impl_match:
            impl_name = impl_match.group(1) or "trait"
            bounds = find_impl_block_bounds(lines, i)
            if bounds:
                doc_start, impl_end = bounds
                items.append((doc_start, impl_end, f"impl {impl_name}", "impl"))
                continue

        # Match function definitions (pub fn, fn, pub(crate) fn, etc.)
        fn_match = re.search(r'\b(pub(?:\([^)]*\))?\s+)?fn\s+(\w+)', line)
        if fn_match:
            fn_name = fn_match.group(2)
            bounds = find_function_bounds(lines, i)
            if bounds:
                doc_start, fn_end = bounds
                items.append((doc_start, fn_end, fn_name, "fn"))

    return items

def comment_out_lines(filepath: str, start_line: int, end_line: int) -> List[str]:
    """
    Comment out lines from start_line to end_line (inclusive, 0-indexed).
    Returns the original lines for potential revert.
    """
    with open(filepath, 'r') as f:
        lines = f.readlines()

    original_lines = lines[start_line:end_line+1].copy()

    # Comment out each line (including doc comments and attributes)
    for i in range(start_line, end_line + 1):
        lines[i] = '// ' + lines[i]

    with open(filepath, 'w') as f:
        f.writelines(lines)

    return original_lines

def revert_lines(filepath: str, start_line: int, end_line: int, original_lines: List[str]):
    """Revert lines to their original state."""
    with open(filepath, 'r') as f:
        lines = f.readlines()

    lines[start_line:end_line+1] = original_lines

    with open(filepath, 'w') as f:
        f.writelines(lines)

def run_cargo_check(check_dir: str, check_cmd: str, timeout: int) -> bool:
    """
    Run cargo check command. Returns True if successful, False otherwise.
    """
    try:
        # Use shell=True to handle complex commands like "nix-shell --run 'cargo check'"
        result = subprocess.run(
            check_cmd,
            cwd=check_dir,
            capture_output=True,
            text=True,
            timeout=timeout,
            shell=True
        )
        return result.returncode == 0
    except subprocess.TimeoutExpired:
        print("  ⏱️  Cargo check timed out")
        return False
    except Exception as e:
        print(f"  ❌ Error running cargo check: {e}")
        return False

def process_file(filepath: str, check_dir: str, check_cmd: str, timeout: int, verbose: bool = False) -> Tuple[int, int, int, int]:
    """
    Process a single Rust file, trying to comment out functions and impl blocks.
    First pass: try to comment out entire impl blocks.
    Second pass: try to comment out individual functions (including those in remaining impl blocks).
    Returns (total_fns, total_impls, commented_fns, commented_impls).
    """
    print(f"\n📝 Processing {filepath}")

    items = find_functions_and_impls(filepath)
    impl_blocks = [(s, e, n, t) for s, e, n, t in items if t == "impl"]
    functions = [(s, e, n, t) for s, e, n, t in items if t == "fn"]

    print(f"   Found {len(impl_blocks)} impl blocks and {len(functions)} functions")

    commented_impls = 0
    commented_fns = 0

    # FIRST PASS: Process impl blocks in reverse order to maintain line numbers
    if impl_blocks:
        print(f"\n  === PASS 1: Trying to comment out impl blocks ===")
        for start_line, end_line, name, item_type in reversed(impl_blocks):
            print(f"\n  🔍 Trying to comment out: {name} (lines {start_line+1}-{end_line+1})")

            # Comment out the impl block
            original_lines = comment_out_lines(filepath, start_line, end_line)

            # Test with cargo check
            print(f"     Running cargo check...", end='', flush=True)
            if run_cargo_check(check_dir, check_cmd, timeout):
                print(" ✅ Success! Impl block is unused.")
                commented_impls += 1
            else:
                print(" ❌ Failed. Reverting.")
                revert_lines(filepath, start_line, end_line, original_lines)

    # SECOND PASS: Re-scan for functions and process them
    # This will include functions that were in impl blocks that couldn't be removed
    print(f"\n  === PASS 2: Trying to comment out individual functions ===")
    items = find_functions_and_impls(filepath)
    functions = [(s, e, n, t) for s, e, n, t in items if t == "fn"]
    print(f"   Found {len(functions)} remaining functions to try")

    initial_fn_count = len(functions)

    for start_line, end_line, name, item_type in reversed(functions):
        print(f"\n  🔍 Trying to comment out: {name} (lines {start_line+1}-{end_line+1})")

        # Comment out the function
        original_lines = comment_out_lines(filepath, start_line, end_line)

        # Test with cargo check
        print(f"     Running cargo check...", end='', flush=True)
        if run_cargo_check(check_dir, check_cmd, timeout):
            print(" ✅ Success! Function is unused.")
            commented_fns += 1
        else:
            print(" ❌ Failed. Reverting.")
            revert_lines(filepath, start_line, end_line, original_lines)

    return initial_fn_count, len(impl_blocks), commented_fns, commented_impls

def main():
    parser = argparse.ArgumentParser(
        description='Automatically comment out unused functions in Rust files by testing with cargo check'
    )
    parser.add_argument(
        'files',
        nargs='+',
        type=str,
        help='Rust source files to process'
    )
    parser.add_argument(
        '--check-dir',
        type=str,
        default='../libsignal',
        help='Directory to run cargo check in (default: ../libsignal)'
    )
    parser.add_argument(
        '--check-cmd',
        type=str,
        default='nix-shell --run "cargo check"',
        help='Command to run for checking (default: "nix-shell --run \\"cargo check\\"")'
    )
    parser.add_argument(
        '--timeout',
        type=int,
        default=120,
        help='Timeout in seconds for cargo check (default: 120)'
    )
    parser.add_argument(
        '--verbose',
        '-v',
        action='store_true',
        help='Verbose output'
    )

    args = parser.parse_args()

    # Verify that cargo check passes before making any changes
    print("🔍 Verifying that cargo check passes before making changes...")
    if not run_cargo_check(args.check_dir, args.check_cmd, args.timeout):
        print("❌ ERROR: Cargo check failed on libsignal without any changes!")
        print("   Please ensure libsignal builds successfully before running this script.")
        sys.exit(1)
    print("✅ Initial check passed\n")

    total_fns = 0
    total_impls = 0
    total_commented_fns = 0
    total_commented_impls = 0

    for filepath in args.files:
        if not Path(filepath).exists():
            print(f"❌ File not found: {filepath}")
            continue

        fns, impls, commented_fns, commented_impls = process_file(
            filepath,
            args.check_dir,
            args.check_cmd,
            args.timeout,
            verbose=args.verbose
        )
        total_fns += fns
        total_impls += impls
        total_commented_fns += commented_fns
        total_commented_impls += commented_impls

    total_items = total_fns + total_impls
    total_commented = total_commented_fns + total_commented_impls

    print(f"\n{'='*60}")
    print(f"✨ Summary:")
    print(f"   Total items processed: {total_items} ({total_fns} fns, {total_impls} impls)")
    print(f"   Successfully commented out: {total_commented} ({total_commented_fns} fns, {total_commented_impls} impls)")
    print(f"   Remaining: {total_items - total_commented} ({total_fns - total_commented_fns} fns, {total_impls - total_commented_impls} impls)")
    print(f"{'='*60}")

if __name__ == '__main__':
    main()
