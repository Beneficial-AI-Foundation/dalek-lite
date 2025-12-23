#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = [
#   "beartype",
# ]
# ///
"""
Initialize verilib structure files from functions_to_track.csv.

Analyzes source code using analyze_verus_specs_proofs to identify tracked functions,
then generates .md structure files with YAML frontmatter containing code-path,
code-line, and scip-name fields.

Usage:
    uv run scripts/structure_initial.py
"""

import io
import sys
from collections import Counter
from contextlib import redirect_stdout
from pathlib import Path

from analyze_verus_specs_proofs import analyze_functions

PROJECT_ROOT = Path(__file__).parent.parent
TRACKED_PATH = PROJECT_ROOT / "functions_to_track.csv"
VERILIB_PATH = PROJECT_ROOT / ".verilib"

def tweak_disambiguate(tracked: dict) -> dict:
    """
    Disambiguate tracked items that have the same qualified_name.

    When multiple functions share the same qualified_name, appends a numeric
    suffix to make them unique: XXX becomes XXX_0, XXX_1, ..., XXX_N.

    Args:
        tracked: Dictionary mapping key to tuple of function metadata.
                 Index 5 of each tuple is the qualified_name.

    Returns:
        New dictionary with disambiguated qualified_names in the tuples.
    """
    qualified_names = [value[5] for value in tracked.values()]
    name_counts = Counter(qualified_names)

    # Find duplicates
    duplicates = {name for name, count in name_counts.items() if count > 1}

    if not duplicates:
        return tracked

    # Track current index for each duplicate name
    name_indices: dict[str, int] = {name: 0 for name in duplicates}

    # Create new tracked dict with disambiguated names
    new_tracked = {}
    for key, value in tracked.items():
        qualified_name = value[5]
        if qualified_name in duplicates:
            # Create new name with suffix
            new_name = f"{qualified_name}_{name_indices[qualified_name]}"
            name_indices[qualified_name] += 1
            # Create new tuple with updated qualified_name
            new_value = value[:5] + (new_name,) + value[6:]
            new_tracked[key] = new_value
        else:
            new_tracked[key] = value

    return new_tracked


def parse_github_link(github_link: str) -> tuple[str, int]:
    """
    Extract code path and line number from a GitHub link.

    Args:
        github_link: GitHub URL of form ".../blob/main/<path>#L<line>"

    Returns:
        Tuple of (code_path, line_number). Returns ("", 0) if parsing fails.

    Example:
        >>> parse_github_link("https://github.com/org/repo/blob/main/src/lib.rs#L42")
        ("src/lib.rs", 42)
    """
    if not github_link or "/blob/main/" not in github_link:
        return "", 0

    path_part = github_link.split("/blob/main/")[1]
    if "#L" in path_part:
        code_path, line_str = path_part.rsplit("#L", 1)
        return code_path, int(line_str)
    return path_part, 0


def generate_structure_files(tracked: dict, verilib_dir: Path) -> int:
    """
    Generate structure .md files for each tracked function.

    Creates a markdown file with YAML frontmatter for each function in the tracked
    dictionary. Files are organized by code path under the verilib directory.

    Args:
        tracked: Dictionary mapping key to tuple of function metadata.
                 Index 4 is the github_link, index 5 is the qualified_name.
        verilib_dir: Directory where structure files will be created.

    Returns:
        Number of structure files created.

    File structure:
        <verilib_dir>/<code-path>/<qualified_name>.md

    Frontmatter fields:
        - code-path: Relative path to source file
        - code-line: Line number where function starts
        - scip-name: null (populated later by structure_deploy.py)
    """
    created_count = 0

    for value in tracked.values():
        github_link, qualified_name = value[4], value[5]
        code_path, line_start = parse_github_link(github_link)

        if not code_path:
            continue

        # Convert qualified_name to filename (replace :: with .)
        func_name = qualified_name.replace('::', '.')
        file_path = verilib_dir / code_path / f"{func_name}.md"
        file_path.parent.mkdir(parents=True, exist_ok=True)

        if file_path.exists():
            print(f"WARNING: File already exists, overwriting: {file_path}")

        content = f"""---
code-path: {code_path}
code-line: {line_start}
scip-name: null
---
"""
        file_path.write_text(content, encoding='utf-8')
        created_count += 1

    return created_count


def main() -> None:
    """
    Initialize verilib structure files from functions_to_track.csv.

    Steps:
        1. Analyze source code to identify tracked functions
        2. Disambiguate duplicate function names
        3. Generate structure .md files in .verilib/
    """

    if not TRACKED_PATH.exists():
        print(f"Error: {TRACKED_PATH} not found", file=sys.stderr)
        sys.exit(1)

    print("Analyzing source code to derive list of functions to track...")
    with redirect_stdout(io.StringIO()):
        tracked = analyze_functions(TRACKED_PATH, PROJECT_ROOT)

    tracked = tweak_disambiguate(tracked)

    print("\nGenerating structure files...")
    structure_count = generate_structure_files(tracked, VERILIB_PATH)
    print(f"Created {structure_count} structure files in {VERILIB_PATH}")


if __name__ == "__main__":
    main()
