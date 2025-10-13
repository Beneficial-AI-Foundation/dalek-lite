#!/usr/bin/env python3
"""
Extract Rust function definitions from specified files.
Outputs CSV with function name, filename, and GitHub permalink.
Filters out commented functions and those containing 'proof', 'spec', or 'main'.

Usage:
    python scripts/extract_rust_functions.py $(fd -e rs .)
"""

import argparse
import csv
import re
import sys
from pathlib import Path


def extract_functions(rust_files):
    """Extract function definitions from Rust files."""
    functions = []

    # GitHub repository and commit info
    github_repo = "https://github.com/Beneficial-AI-Foundation/dalek-lite"
    commit_hash = "4c0358ebf1ded29a1963b09c62e9e9dfb6da37df"

    # Pattern to match function definitions
    # Matches: fn function_name or pub fn function_name, etc.
    fn_pattern = re.compile(r'(?:^|\s)fn\s+(\w+)')

    for filepath in rust_files:
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                for line_num, line in enumerate(f, start=1):
                    # Skip lines that are comments (starting with //)
                    stripped = line.lstrip()
                    if stripped.startswith('//'):
                        continue

                    # Check if line contains fn
                    if ' fn' in line or line.startswith('fn'):
                        # Skip if contains /, proof, spec, or main
                        if '/' in line or 'proof' in line or 'spec' in line or 'main' in line:
                            continue

                        # Extract function name
                        match = fn_pattern.search(line)
                        if match:
                            fn_name = match.group(1)
                            # Create GitHub permalink
                            permalink = f"{github_repo}/blob/{commit_hash}/{filepath}#L{line_num}"
                            functions.append((fn_name, str(filepath), permalink))

        except Exception as e:
            print(f"Error processing {filepath}: {e}", file=sys.stderr)

    # Sort by filename, then by line number (extracted from permalink)
    functions.sort(key=lambda x: (x[1], int(x[2].split('#L')[1])))

    return functions


def main():
    parser = argparse.ArgumentParser(
        description='Extract Rust function definitions and output as CSV'
    )
    parser.add_argument(
        'files',
        nargs='+',
        type=Path,
        help='Rust files to process'
    )

    args = parser.parse_args()

    functions = extract_functions(args.files)

    # Output CSV
    writer = csv.writer(sys.stdout)
    writer.writerow(["function_name", "filename", "github_link"])

    for fn_name, filename, permalink in functions:
        writer.writerow([fn_name, filename, permalink])


if __name__ == '__main__':
    main()
