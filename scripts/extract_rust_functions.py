#!/usr/bin/env python3
"""
Extract Rust function definitions from specified files.
Outputs TSV with function name, filename, and line number.
Filters out commented functions and those containing 'proof', 'spec', or 'main'.

Usage:
    python scripts/extract_rust_functions.py $(fd -e rs .)
"""

import argparse
import re
import sys
from pathlib import Path


def extract_functions(rust_files):
    """Extract function definitions from Rust files."""
    functions = []

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
                            functions.append((fn_name, str(filepath), line_num))

        except Exception as e:
            print(f"Error processing {filepath}: {e}", file=sys.stderr)

    # Sort by filename, then line number
    functions.sort(key=lambda x: (x[1], x[2]))

    return functions


def main():
    parser = argparse.ArgumentParser(
        description='Extract Rust function definitions and output as TSV'
    )
    parser.add_argument(
        'files',
        nargs='+',
        type=Path,
        help='Rust files to process'
    )

    args = parser.parse_args()

    functions = extract_functions(args.files)

    # Output TSV header
    print("function_name\tfilename\tline_number")

    # Output TSV rows
    for fn_name, filename, line_num in functions:
        print(f"{fn_name}\t{filename}\t{line_num}")


if __name__ == '__main__':
    main()
