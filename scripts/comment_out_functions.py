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

def find_functions(filepath: str) -> List[Tuple[int, int, str]]:
    """
    Find all function definitions in a Rust file.
    Returns list of (start_line, end_line, function_name) tuples.
    """
    with open(filepath, 'r') as f:
        lines = f.readlines()

    functions = []

    for i, line in enumerate(lines):
        # Skip already commented out lines
        stripped = line.strip()
        if stripped.startswith('//'):
            continue

        # Match function definitions (pub fn, fn, pub(crate) fn, etc.)
        match = re.search(r'\b(pub(?:\([^)]*\))?\s+)?fn\s+(\w+)', line)
        if match:
            fn_name = match.group(2)
            bounds = find_function_bounds(lines, i)
            if bounds:
                doc_start, fn_end = bounds
                functions.append((doc_start, fn_end, fn_name))

    return functions

def comment_out_lines(filepath: str, start_line: int, end_line: int) -> List[str]:
    """
    Comment out lines from start_line to end_line (inclusive, 0-indexed).
    Returns the original lines for potential revert.
    """
    with open(filepath, 'r') as f:
        lines = f.readlines()

    original_lines = lines[start_line:end_line+1].copy()

    # Comment out each line
    for i in range(start_line, end_line + 1):
        if not lines[i].strip().startswith('//'):
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

def process_file(filepath: str, check_dir: str, check_cmd: str, timeout: int, verbose: bool = False) -> Tuple[int, int]:
    """
    Process a single Rust file, trying to comment out functions.
    Returns (total_functions, commented_out_count).
    """
    print(f"\n📝 Processing {filepath}")

    functions = find_functions(filepath)
    print(f"   Found {len(functions)} functions")

    commented_out = 0

    # Process functions in reverse order to maintain line numbers
    for start_line, end_line, fn_name in reversed(functions):
        print(f"\n  🔍 Trying to comment out: {fn_name} (lines {start_line+1}-{end_line+1})")

        # Comment out the function
        original_lines = comment_out_lines(filepath, start_line, end_line)

        # Test with cargo check
        print(f"     Running cargo check...", end='', flush=True)
        if run_cargo_check(check_dir, check_cmd, timeout):
            print(" ✅ Success! Function is unused.")
            commented_out += 1
        else:
            print(" ❌ Failed. Reverting.")
            revert_lines(filepath, start_line, end_line, original_lines)

    return len(functions), commented_out

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

    total_fns = 0
    total_commented = 0

    for filepath in args.files:
        if not Path(filepath).exists():
            print(f"❌ File not found: {filepath}")
            continue

        fns, commented = process_file(
            filepath,
            args.check_dir,
            args.check_cmd,
            args.timeout,
            verbose=args.verbose
        )
        total_fns += fns
        total_commented += commented

    print(f"\n{'='*60}")
    print(f"✨ Summary:")
    print(f"   Total functions processed: {total_fns}")
    print(f"   Successfully commented out: {total_commented}")
    print(f"   Remaining: {total_fns - total_commented}")
    print(f"{'='*60}")

if __name__ == '__main__':
    main()
