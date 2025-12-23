#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = [
#   "requests",
#   "intervaltree",
#   "python-frontmatter"
# ]
# ///
"""
Deploy verilib structure files by syncing with SCIP atoms.

This script:
1. Runs scip-atoms to generate source code intelligence data
2. Filters atoms by crate prefix (curve25519-dalek)
3. Builds an interval tree index for line-based lookups
4. Syncs structure .md files with SCIP atom data
5. Generates .meta.verilib and .atom.verilib metadata files

Usage:
    uv run scripts/structure_deploy.py
"""

import hashlib
import json
import os
import shutil
import subprocess
from collections import Counter, defaultdict
from pathlib import Path

import requests
import frontmatter
from intervaltree import IntervalTree

# Project paths
PROJECT_ROOT = Path(__file__).resolve().parent.parent
VERILIB_PATH = PROJECT_ROOT / ".verilib"
SCIP_ATOMS_PATH = VERILIB_PATH / "scip_atoms.json"
DEBUG_PATH = VERILIB_PATH / "structure_deploy.log"
METADATA_PATH = VERILIB_PATH / "metadata.json"


# SCIP configuration
SCIP_ATOMS_REPO = "https://github.com/Beneficial-AI-Foundation/scip-atoms"
SCIP_PREFIX = "curve25519-dalek"


def check_scip_atoms_or_exit() -> None:
    """Check if scip-atoms is installed, exit with instructions if not."""
    installed = shutil.which("scip-atoms") is not None
    if not installed:
        print("Error: scip-atoms is not installed.")
        print(f"Please visit {SCIP_ATOMS_REPO} for installation instructions.")
        print("\nQuick install:")
        print("  git clone", SCIP_ATOMS_REPO)
        print("  cd scip-atoms")
        print("  cargo install --path .")
        raise SystemExit(1)


def generate_scip_atoms() -> dict[str, dict]:
    """
    Run scip-atoms on this repo and save results to .verilib/scip_atoms.json.

    Executes the scip-atoms CLI tool to analyze source code and generate
    SCIP (Source Code Intelligence Protocol) data. Validates that there are
    no duplicate scip-names, then converts the list to a dictionary.

    Returns:
        Dictionary mapping scip-name to atom data. Each atom contains:
        - code-path: Relative path to source file
        - code-text: Dict with lines-start, lines-end, and source text
        - dependencies: List of scip-names this function depends on

    Raises:
        SystemExit: If scip-atoms is not installed or fails to run.
        ValueError: If duplicate scip-names are found.
    """
    check_scip_atoms_or_exit()

    # Ensure .verilib directory exists
    SCIP_ATOMS_PATH.parent.mkdir(parents=True, exist_ok=True)

    print(f"Running scip-atoms on {PROJECT_ROOT}...")
    result = subprocess.run(
        ["scip-atoms", str(PROJECT_ROOT), str(SCIP_ATOMS_PATH), "-r"],
        capture_output=True,
        text=True,
    )

    if result.returncode != 0:
        print("Error: scip-atoms failed.")
        if result.stderr:
            print(result.stderr)
        raise SystemExit(1)

    # Clean up generated intermediate files
    for cleanup_file in ["data/index.scip", "data/index.scip.json"]:
        cleanup_path = PROJECT_ROOT / cleanup_file
        if cleanup_path.exists():
            cleanup_path.unlink()

    # Remove data/ folder if empty
    data_dir = PROJECT_ROOT / "data"
    if data_dir.exists() and data_dir.is_dir() and not any(data_dir.iterdir()):
        data_dir.rmdir()

    print(f"Results saved to {SCIP_ATOMS_PATH}")

    # Read the generated JSON file
    with open(SCIP_ATOMS_PATH, encoding='utf-8') as f:
        data = json.load(f)

    if check_duplicates(data):
        raise ValueError("Duplicates found in scip names")

    # Convert to dictionary keyed by scip-name
    result: dict[str, dict] = {}
    for item in data:
        scip_name = item.get('scip-name', '')
        if scip_name:
            atom_data = {k: v for k, v in item.items() if k != 'scip-name'}
            result[scip_name] = atom_data

    return result


def check_duplicates(data: list[dict]) -> bool:
    """
    Check for duplicate scip-names in SCIP atoms data.

    Warns if any dependencies reference duplicate scip-names, as this could
    cause ambiguity during lookups.

    Args:
        data: List of SCIP atom dictionaries, each with a 'scip-name' field.

    Returns:
        True if duplicates were found, False otherwise.
    """
    scip_names = [item.get('scip-name', '') for item in data]
    name_counts = Counter(scip_names)
    duplicates = {name for name, count in name_counts.items() if count > 1 and name}

    if not duplicates:
        return False

    # Warn about dependencies that reference duplicate names
    for item in data:
        for dep in item.get('dependencies', []):
            if dep in duplicates:
                print(f"WARNING: Dependency '{dep}' is a duplicate scip-name "
                      f"(referenced by '{item.get('scip-name', '')}')")
    return True


def generate_scip_index(scip_atoms: dict[str, dict]) -> dict[str, IntervalTree]:
    """
    Build an interval tree index for fast line-based lookups.

    Creates a dictionary of IntervalTree structures, one per source file,
    allowing efficient lookup of which function contains a given line number.

    Args:
        scip_atoms: Dictionary mapping scip-name to atom data.

    Returns:
        Dictionary mapping code-path to IntervalTree. Each tree stores
        intervals [lines-start, lines-end+1) with the scip-name as data.

    Example:
        >>> index = generate_scip_index(atoms)
        >>> tree = index["src/lib.rs"]
        >>> matches = tree[42]  # Find all functions containing line 42
    """
    trees: dict[str, IntervalTree] = defaultdict(IntervalTree)

    for scip_name, atom_data in scip_atoms.items():
        code_path = atom_data.get('code-path')
        code_text = atom_data.get('code-text', {})

        if not code_path:
            continue

        lines_start = code_text.get('lines-start')
        lines_end = code_text.get('lines-end')

        if lines_start is None or lines_end is None:
            continue

        # IntervalTree uses half-open intervals [start, end)
        # Add 1 to lines_end to make it inclusive
        interval_end = lines_end + 1

        trees[code_path].addi(lines_start, interval_end, scip_name)

    return dict(trees)


def filter_scip_atoms(scip_atoms: dict[str, dict], prefix: str) -> dict[str, dict]:
    """
    Filter SCIP atoms to only those where scip-name starts with prefix.

    Args:
        scip_atoms: Dictionary mapping scip-name to atom data
        prefix: Prefix to filter scip-name by

    Returns:
        Dictionary mapping scip-name to the atom object, filtered by prefix
    """
    return {
        scip_name: atom_data
        for scip_name, atom_data in scip_atoms.items()
        if scip_name.startswith(prefix)
    }


def sync_structure_with_atoms(
    scip_index: dict[str, IntervalTree],
    scip_atoms: dict[str, dict],
    verilib_path: Path
) -> None:
    """
    Sync structure files with SCIP atoms index.

    For each .md file in verilib_path:
    - If it has a scip-name, look it up in scip_atoms and verify code-path/code-line match
    - If it doesn't have a scip-name, look up by code-path and code-line in scip_index

    Args:
        scip_index: Dictionary mapping code-path to IntervalTree
        scip_atoms: Dictionary mapping scip-name to atom data
        verilib_path: Path to the .verilib directory
    """
    updated_count = 0
    not_found_count = 0

    for md_file in verilib_path.rglob("*.md"):
        post = frontmatter.load(md_file)

        code_path = post.get('code-path')
        line_start = post.get('code-line')
        existing_scip_name = post.get('scip-name')

        # If scip-name exists, verify against scip_atoms
        if existing_scip_name:
            if existing_scip_name not in scip_atoms:
                print(f"WARNING: scip-name '{existing_scip_name}' not found in scip_atoms for {md_file}")
                not_found_count += 1
                continue

            atom = scip_atoms[existing_scip_name]
            atom_code_path = atom.get('code-path')
            atom_code_text = atom.get('code-text', {})
            atom_line_start = atom_code_text.get('lines-start')

            # Verify code-path matches
            if code_path != atom_code_path:
                print(f"WARNING: code-path mismatch for {md_file}: "
                      f"structure has '{code_path}', scip_atoms has '{atom_code_path}'")

            # Verify code-line matches
            if line_start != atom_line_start:
                print(f"WARNING: code-line mismatch for {md_file}: "
                      f"structure has {line_start}, scip_atoms has {atom_line_start}")

            # Update with values from scip_atoms
            post['code-path'] = atom_code_path
            post['code-line'] = atom_line_start

        else:
            # No scip-name, look up by code-path and code-line
            if not code_path or line_start is None:
                print(f"WARNING: Missing code-path or code-line in {md_file}")
                not_found_count += 1
                continue

            if code_path not in scip_index:
                print(f"WARNING: code-path '{code_path}' not found in scip_index for {md_file}")
                not_found_count += 1
                continue

            tree = scip_index[code_path]

            # Find intervals that contain the start line
            matching_intervals = tree[line_start]

            # Filter to only intervals that start exactly at line_start
            exact_matches = [iv for iv in matching_intervals if iv.begin == line_start]

            if not exact_matches:
                print(f"WARNING: No interval starting at line {line_start} in {code_path} for {md_file}")
                not_found_count += 1
                continue

            if len(exact_matches) > 1:
                print(f"WARNING: Multiple intervals starting at line {line_start} in {code_path} for {md_file}")

            # Use the first match
            interval = exact_matches[0]
            scip_name = interval.data

            # Update the frontmatter
            post['scip-name'] = scip_name

        # Write updated content
        with open(md_file, 'w', encoding='utf-8') as f:
            f.write(frontmatter.dumps(post))

        updated_count += 1

    print(f"Structure files updated: {updated_count}")
    print(f"Not found/skipped: {not_found_count}")


def extract_code_module(scip_name: str) -> str:
    """
    Extract code-module from scip-name.

    The scip-name format is: "<crate> <version> <path>/<func>()"
    The code-module is the path prefix before the final "/", reversed.

    Example:
        "curve25519-dalek 4.1.3 field/u64/serial/backend/&FieldElement51#..."
        -> "backend/serial/u64/field"

    Args:
        scip_name: The scip-name string

    Returns:
        The code-module string with path segments reversed
    """
    parts = scip_name.split(' ', 2)
    if len(parts) != 3:
        return ""

    func_path = parts[2]

    # Find the last "/" to get the module path
    last_slash = func_path.rfind('/')
    if last_slash == -1:
        return ""

    module_path = func_path[:last_slash]

    # Reverse the path segments
    segments = module_path.split('/')
    return '/'.join(reversed(segments))


def populate_structure_metadata(
    scip_atoms: dict[str, dict],
    verilib_path: Path,
    project_root: Path
) -> None:
    """
    Generate metadata files for each structure .md file.

    For each XXX.md file in verilib_path, creates two companion files:

    XXX.meta.verilib (JSON):
        - code-path: Relative path to source file
        - code-lines: {start, end} line numbers
        - code-module: Module path (reversed segments from scip-name)
        - dependencies: List of scip-names this function depends on
        - scip-name: The SCIP identifier
        - visible: Boolean flag (always True)

    XXX.atom.verilib:
        - Raw source code extracted from the original file

    Args:
        scip_atoms: Dictionary mapping scip-name to atom data.
        verilib_path: Path to the .verilib directory containing .md files.
        project_root: Path to project root for resolving source file paths.
    """
    created_count = 0
    skipped_count = 0

    for md_file in verilib_path.rglob("*.md"):
        post = frontmatter.load(md_file)

        scip_name = post.get('scip-name')
        if not scip_name or scip_name not in scip_atoms:
            print(f"WARNING: Missing or invalid scip-name in {md_file}")
            skipped_count += 1
            continue

        atom = scip_atoms[scip_name]
        code_path = atom.get('code-path')
        code_text = atom.get('code-text', {})
        lines_start = code_text.get('lines-start')
        lines_end = code_text.get('lines-end')
        dependencies = atom.get('dependencies', [])

        if not code_path or lines_start is None or lines_end is None:
            print(f"WARNING: Missing code-path or line info for {md_file}")
            skipped_count += 1
            continue

        # Extract code-module from scip-name
        code_module = extract_code_module(scip_name)

        # Create XXX.meta.verilib
        meta_data = {
            "scip-name": scip_name,
            "code-path": code_path,
            "code-lines": {
                "start": lines_start,
                "end": lines_end
            },
            "code-module": code_module,
            "dependencies": dependencies,
            "specified": False,
            "visible": True
        }

        meta_file = md_file.with_suffix('.meta.verilib')
        with open(meta_file, 'w', encoding='utf-8') as f:
            json.dump(meta_data, f, indent=2)

        # Create XXX.atom.verilib by extracting source code
        source_file = project_root / code_path
        if not source_file.exists():
            print(f"WARNING: Source file not found: {source_file}")
            skipped_count += 1
            continue

        with open(source_file, encoding='utf-8') as f:
            all_lines = f.readlines()

        # Extract lines (1-indexed, inclusive)
        extracted_lines = all_lines[lines_start - 1:lines_end]
        atom_content = ''.join(extracted_lines)

        atom_file = md_file.with_suffix('.atom.verilib')
        with open(atom_file, 'w', encoding='utf-8') as f:
            f.write(atom_content)

        created_count += 1

    print(f"Metadata files created: {created_count}")
    print(f"Skipped: {skipped_count}")


def structure_to_tree(verilib_path: Path) -> list[dict]:
    """
    Convert structure files to a JSON tree format.

    Walks the VERILIB_PATH folder recursively and builds a nested tree structure
    where:
    - Folder hierarchy determines the children relationships
    - Identifiers use paths derived from .md file locations
    - Content comes from .atom.verilib files
    - Dependencies are mapped from scip-names to paths

    Args:
        verilib_path: Path to the .verilib directory containing structure files.

    Returns:
        List of root tree nodes. Each node is a dict with:
        - identifier: Path for files, folder path for folders
        - content: Source code text (empty for folders)
        - children: List of child nodes
        - file_type: "file" or "folder"
        - dependencies: List of dependency paths (files only)
        - specified: Boolean flag (files only)
    """
    # First pass: build scip-name to path mapping
    scip_to_path: dict[str, str] = {}
    for md_file in verilib_path.rglob("*.md"):
        meta_file = md_file.with_suffix(".meta.verilib")
        if not meta_file.exists():
            continue

        with open(meta_file, encoding="utf-8") as f:
            meta_data = json.load(f)

        scip_name = meta_data.get("scip-name", "")
        if not scip_name:
            continue

        # Construct path from .md file location relative to verilib_path
        relative_path = md_file.relative_to(verilib_path)
        # Remove .md extension and prepend /
        path = "/" + str(relative_path.with_suffix(""))
        scip_to_path[scip_name] = path

    def build_tree_recursive(dir_path: Path, parent_identifier: str = "") -> list[dict]:
        """Recursively build tree nodes from directory structure."""
        nodes = []

        # Get all items in directory, sorted for consistent ordering
        items = sorted(dir_path.iterdir())

        # Separate directories and files
        subdirs = [item for item in items if item.is_dir()]
        md_files = [item for item in items if item.is_file() and item.suffix == ".md"]

        # Process subdirectories as folder nodes
        for subdir in subdirs:
            folder_name = subdir.name
            folder_identifier = f"{parent_identifier}/{folder_name}" if parent_identifier else folder_name

            children = build_tree_recursive(subdir, folder_identifier)

            # Only add folder if it has children
            if children:
                folder_node = {
                    "identifier": folder_identifier,
                    "content": "",
                    "children": children,
                    "file_type": "folder",
                }
                nodes.append(folder_node)

        # Process .md files as file nodes
        for md_file in md_files:
            meta_file = md_file.with_suffix(".meta.verilib")
            atom_file = md_file.with_suffix(".atom.verilib")

            # Skip if meta file doesn't exist
            if not meta_file.exists():
                continue

            # Read metadata
            with open(meta_file, encoding="utf-8") as f:
                meta_data = json.load(f)

            scip_name = meta_data.get("scip-name", "")
            if not scip_name:
                continue

            # Get identifier from path mapping
            identifier = scip_to_path.get(scip_name, "")
            if not identifier:
                continue

            # Get content from atom file
            content = ""
            if atom_file.exists():
                content = atom_file.read_text(encoding="utf-8")

            # Get dependencies and map to paths
            scip_dependencies = meta_data.get("dependencies", [])
            dependencies = [scip_to_path.get(dep, dep) for dep in scip_dependencies]

            # Get specified flag
            specified = meta_data.get("specified", False)

            file_node = {
                "identifier": identifier,
                "content": content,
                "children": [],
                "file_type": "file",
                "dependencies": dependencies,
                "specified": specified,
            }
            nodes.append(file_node)

        return nodes

    # Build tree starting from verilib_path
    return build_tree_recursive(verilib_path)


def deploy(url, repo, api_key, tree, debug=False, debug_path=DEBUG_PATH):
    """Send POST request to deploy endpoint.

    Args:
        url: Base URL of the deployment server
        repo: Repository ID
        tree: Tree structure to deploy
        api_key: API key for authorization
        debug: If True, write json_body to file for debugging
        debug_path: Path to the debug log file
    """
    # Create json_body from tree
    json_body = {"tree": tree}

    deploy_url = f"{url}/v2/repo/deploy/{repo}"

    headers = {
        "Content-Type": "application/json",
        "Accept": "application/json",
        "Authorization": f"ApiKey {api_key}",
    }

    # Write json_body to file with pretty printing (only if debug mode)
    if debug:
        debug_path.parent.mkdir(parents=True, exist_ok=True)
        with open(debug_path, "a", encoding="utf-8") as f:
            f.write("\n=== deploy json_body ===\n")
            json.dump(json_body, f, indent=4)
            f.write("\n")
        print(f"json_body written to {debug_path}")

    # Send POST request with JSON body
    response = requests.post(deploy_url, headers=headers, json=json_body)

    # Print response details
    print(f"Status Code: {response.status_code}")
    print(f"Response Headers: {dict(response.headers)}")
    print(f"Response Body: {response.text}")

    return response


def main() -> None:
    """
    Deploy verilib structure files by syncing with SCIP atoms.

    Steps:
        1. Generate SCIP atoms from source code
        2. Filter to only curve25519-dalek atoms
        3. Build interval tree index for line lookups
        4. Sync structure .md files with SCIP data
        5. Generate metadata files (.meta.verilib, .atom.verilib)
        6. Construct tree from structure files
        7. Deploy tree to server
    """
    # Load config
    with open(METADATA_PATH, encoding="utf-8") as f:
        config = json.load(f)
    repo = config["repo"]["id"]
    url = config["repo"]["url"]

    # Get API key from environment
    api_key = os.environ.get("VERILIB_API_KEY")
    if not api_key:
        raise ValueError("VERILIB_API_KEY environment variable is not set")

    # Get debug flag
    debug = os.environ.get("VERILIB_DEBUG", "").lower() in ("true", "1", "yes")

    # # Generate and sync SCIP atoms
    # scip_atoms = generate_scip_atoms()
    # scip_atoms = filter_scip_atoms(scip_atoms, SCIP_PREFIX)
    # scip_index = generate_scip_index(scip_atoms)
    # sync_structure_with_atoms(scip_index, scip_atoms, VERILIB_PATH)
    # populate_structure_metadata(scip_atoms, VERILIB_PATH, PROJECT_ROOT)

    print(f"api key {api_key}")
    # Construct tree from structure files and deploy
    print("Constructing tree from structure files...")
    tree = structure_to_tree(VERILIB_PATH)
    print(f"Tree constructed with {len(tree)} root node(s)")

    print("Deploying tree...")
    deploy(url, repo, api_key, tree, debug=debug)


if __name__ == "__main__":
    main()
