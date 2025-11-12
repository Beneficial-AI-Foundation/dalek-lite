#!/usr/bin/env python3
"""
Script to send HTTP POST request to deploy endpoint.
"""

import json
import os
import requests
from csv import DictReader
from pathlib import Path
from dotenv import load_dotenv

load_dotenv()

# Get the project root
PROJECT_ROOT = Path(__file__).resolve().parent.parent
DEBUG_PATH = PROJECT_ROOT / ".verilib" / "verilib_deploy.log"
OLD_TREE_PATH = PROJECT_ROOT / ".verilib" / "debug_deploy_tree.json"
METADATA_PATH = PROJECT_ROOT / ".verilib" / "metadata.json"
PVF_PATH = PROJECT_ROOT / ".verilib" / "curve25519_functions.pvf"
TREE_PATH = PROJECT_ROOT / ".verilib" / "curve25519_functions.tree"
CSV_PATH = PROJECT_ROOT / "outputs" / "curve25519_functions.csv"


def build_tree_node(identifier, pvf):
    """
    Recursively build a tree node and all its children.

    Args:
        identifier: The identifier of the current node
        pvf: The flat PVF data dictionary

    Returns:
        A tree node dict with nested children
    """
    if identifier not in pvf:
        return None

    entry = pvf[identifier]
    file_type = entry.get("file_type", "")

    # Build the base node structure
    node = {
        "identifier": identifier,
        "content": entry.get("content", ""),
        "children": [],
        "file_type": file_type,
    }

    # Add file-specific fields
    if file_type == "file":
        # Add dependencies
        dependencies = list(entry.get("dependencies", {}).keys())
        # Convert dependencies to have leading "/" if they don't already
        dependencies = [
            "/" + dep if not dep.startswith("/") else dep for dep in dependencies
        ]
        node["dependencies"] = dependencies

        # Add specified field
        node["specified"] = entry.get("specified", False)

    # Recursively build children
    children_ids = entry.get("children", {}).keys()
    for child_id in children_ids:
        child_node = build_tree_node(child_id, pvf)
        if child_node:
            node["children"].append(child_node)

    return node


def find_root_nodes(pvf):
    """
    Find root nodes (nodes that are not children of any other node).

    Args:
        pvf: The flat PVF data dictionary

    Returns:
        List of root node identifiers
    """
    all_identifiers = set(pvf.keys())
    all_children = set()

    # Collect all identifiers that appear as children
    for entry in pvf.values():
        children = list(entry.get("children", {}).keys())
        all_children.update(children)

    # Root nodes are those not appearing as children
    root_nodes = all_identifiers - all_children

    return sorted(root_nodes)


def pvf_to_tree(pvf, debug=False, debug_path=DEBUG_PATH):
    print(f"Found {len(pvf)} entries in PVF file")

    print("Finding root nodes...")
    root_identifiers = find_root_nodes(pvf)
    print(f"Found {len(root_identifiers)} root nodes: {root_identifiers}")

    print("Building nested tree structure...")
    tree = []
    for root_id in root_identifiers:
        root_node = build_tree_node(root_id, pvf)
        if root_node:
            tree.append(root_node)

    print("Done!")

    # Debug output
    if debug:
        debug_path.parent.mkdir(parents=True, exist_ok=True)
        with open(debug_path, "a", encoding="utf-8") as f:
            f.write("\n=== pvf_to_tree result ===\n")
            json.dump(tree, f, indent=4)
            f.write("\n")

    return tree


def ensure_parent_exists(identifier, pvf):
    """
    Ensure all parent folders exist in the hierarchy, creating them if necessary.
    Also ensures the identifier is added as a child to its parent.

    Args:
        identifier: The identifier to ensure parents for
        pvf: The PVF data dictionary (modified in place)

    Returns:
        Number of newly created parent folders
    """
    created_count = 0
    parent_id = identifier.rsplit("/", 1)[0] if "/" in identifier else None

    if parent_id is None:
        # At root level, no parent needed
        return created_count

    # Recursively ensure grandparents exist first
    if parent_id not in pvf:
        # Create the parent folder
        pvf[parent_id] = {
            "children": {},
            "file_type": "folder",
            "url": "",
            "visible": True,
        }
        created_count += 1

        # Recursively ensure grandparents exist
        created_count += ensure_parent_exists(parent_id, pvf)

    # Add identifier as child of parent if not already present
    parent_entry = pvf[parent_id]
    children = parent_entry["children"]
    if identifier not in children:
        children[identifier] = {"visible": True}

    return created_count


def csv_to_pvf(csv, OLD_TREE_PATH=OLD_TREE_PATH, debug=False, debug_path=DEBUG_PATH):
    # Read old tree
    print(f"Reading old tree {OLD_TREE_PATH}...")
    with open(OLD_TREE_PATH, "r", encoding="utf-8") as f:
        old_tree = json.load(f)
    old_pvf = tree_to_pvf(old_tree)
    print(f"Found {len(old_pvf)} identifiers in old PVF file")

    pvf = {}
    updated_count = 0
    added_count = 0
    folders_created = 0

    for identifier in csv.keys():
        # Get CSV field values
        csv_entry = csv[identifier]
        specified = csv_entry["specified"]
        verified = csv_entry["verified"]
        new_identifier = csv_entry["new_identifier"]
        url = csv_entry["url"]
        content = ""
        dependencies = {}

        # Check if this identifier exists in old pvf file
        if identifier in old_pvf:
            old_entry = old_pvf[identifier]

            # Only update if it's a file type entry
            if old_entry.get("file_type") == "file":
                content = old_entry["content"]
                for dependency in old_entry["dependencies"]:
                    if dependency in csv:
                        dep_new_ident = csv[dependency]["new_identifier"]
                        dependencies[dep_new_ident] = {"visible": True}
                updated_count += 1
            else:
                raise ValueError(f"Identifier {identifier} is not a file but a folder")
        else:
            # Add new entry to pvf file
            added_count += 1

        pvf[new_identifier] = {
            "dependencies": dependencies,
            "content": content,
            "file_type": "file",
            "specified": specified,
            "verified": verified,
            "url": url,
            "visible": True,
        }
        # Ensure parent hierarchy exists
        folders_created += ensure_parent_exists(new_identifier, pvf)

    print(f"Updated {updated_count} existing entries in pvf file")
    print(f"Added {added_count} new entries to pvf file")
    print(f"Created {folders_created} new folder entries")
    print(f"Final count: {len(pvf)} identifiers")
    print("Done!")

    # Debug output
    if debug:
        debug_path.parent.mkdir(parents=True, exist_ok=True)
        with open(debug_path, "a", encoding="utf-8") as f:
            f.write("\n=== csv_to_pvf result ===\n")
            json.dump(pvf, f, indent=4)
            f.write("\n")

    return pvf


def pvf_to_csv(pvf, debug=False, debug_path=DEBUG_PATH):
    """
    Convert PVF dict to CSV dict format.

    Args:
        pvf: PVF dictionary
        debug: If True, append result to DEBUG_PATH
        debug_path: Path to the debug log file

    Returns:
        dict: CSV dictionary with rows as list of dicts
    """
    print("Processing file entries...")

    # Extract file entries only
    csv = {}
    for identifier, entry in pvf.items():
        if entry.get("file_type") == "file":
            link = entry.get("url")

            # Extract function_path from link (between "main/" and "#L")
            if "main/" in link and "#L" in link:
                start_idx = link.find("main/") + len("main/")
                end_idx = link.find("#L")
                function_path = link[start_idx:end_idx]
            else:
                raise ValueError(f"Unexpected link format {link}")

            # Check if function_path matches module (after replacing "::" with "/")
            if function_path.endswith("/mod.rs"):
                module_path = function_path[: -len("/mod.rs")]
            elif function_path.endswith(".rs"):
                module_path = function_path[: -len(".rs")]
            else:
                raise ValueError(f"Function path {function_path} does not end with .rs")
            module_path = module_path.replace("-", "_")
            module_path = module_path.replace("src/", "")

            if not identifier.startswith(module_path):
                raise ValueError(
                    f"Identifier {identifier} does not have format of module path."
                )

            # Extract function_identifier (everything after first module_path/)
            function_identifier = identifier[len(module_path) + 1 :]
            # Convert module_path back to module
            module = module_path.replace("/", "::")

            # Convert function_identifier back to function
            function = function_identifier.replace("/", "::")

            # Reconstruct old identifier
            if "::" in function:
                function_stem = function.split("::")[-1]
            else:
                function_stem = function
            old_identifier = f"{function_path}/{function_stem}"

            csv[old_identifier] = {
                "new_identifier": identifier,
                "function": function,
                "module": module,
                "specified": entry.get("specified"),
                "verified": entry.get("verified"),
                "url": entry.get("url"),
            }

    print(f"Found {len(csv)} file entries")

    # Debug output
    if debug:
        debug_path.parent.mkdir(parents=True, exist_ok=True)
        with open(debug_path, "a", encoding="utf-8") as f:
            f.write("\n=== pvf_to_csv result ===\n")
            json.dump(csv, f, indent=4)
            f.write("\n")

    print("Done!")
    print(f"Created CSV dict with {len(csv)} rows")

    return csv


def read_csv(csv_path=CSV_PATH, debug=False, debug_path=DEBUG_PATH):
    """
    Read CSV file and create a dictionary mapping function paths to module::function.

    Args:
        csv_path: Path to the CSV file
        debug: If True, append result to DEBUG_PATH

    Returns:
        dict: Keys are {function_path}/{function_stem}, values are dict with function info
    """

    result = {}
    function_path_module_mismatches = []

    with open(csv_path, "r", encoding="utf-8") as f:
        reader = DictReader(f)
        for row in reader:
            if row["has_spec"].lower() not in ["yes", "no", ""]:
                print(
                    f"WARNING: Row `{row['function']}`, `{row['module']}` has unexpected has_spec value `{row['has_spec']}`"
                )
            function = row["function"]
            module = row["module"]
            link = row["link"]
            specified = row["has_spec"].lower() == "yes"
            verified = row["has_proof"].lower() == "yes"

            # Extract function_path from link (between "main/" and "#L")
            if "main/" in link and "#L" in link:
                start_idx = link.find("main/") + len("main/")
                end_idx = link.find("#L")
                function_path = link[start_idx:end_idx]
            else:
                raise ValueError(f"Unexpected link format {link}")

            # Check if function_path matches module (after replacing "::" with "/")
            module_path = module.replace("::", "/")
            if function_path.endswith("/mod.rs"):
                function_path_modified = function_path[: -len("/mod.rs")]
            elif function_path.endswith(".rs"):
                function_path_modified = function_path[: -len(".rs")]
            else:
                raise ValueError(f"Function path {function_path} does not end with .rs")
            function_path_modified = function_path_modified.replace("-", "_")
            function_path_modified = function_path_modified.replace("src/", "")
            if function_path_modified != module_path:
                function_path_module_mismatches.append(
                    {
                        "function_path_modified": function_path_modified,
                        "module_path": module_path,
                    }
                )

            # Extract function_stem (part after last "::" in function)
            function_identifier = function.replace("::", "/")
            if "::" in function:
                function_stem = function.split("::")[-1]
            else:
                function_stem = function

            # Create key and value
            key = f"{function_path}/{function_stem}"
            value = {
                "new_identifier": f"{module_path}/{function_identifier}",
                "function": function,
                "module": module,
                "specified": specified,
                "verified": verified,
                "url": link,
            }

            # Check for duplicate keys
            if key in result:
                raise ValueError(
                    f"Duplicate key found: {key} (existing: {result[key]}, new: {value})"
                )

            result[key] = value

    print(f"Function path and module mismatches: {function_path_module_mismatches}")

    # Debug output
    if debug:
        debug_path.parent.mkdir(parents=True, exist_ok=True)
        with open(debug_path, "a", encoding="utf-8") as f:
            f.write("\n=== read_csv result ===\n")
            json.dump(result, f, indent=4)
            f.write("\n")

    return result


def write_csv(csv, csv_path=CSV_PATH, debug=False, debug_path=DEBUG_PATH):
    """
    Write CSV dictionary to a CSV file.

    Args:
        csv: Dictionary with keys as identifiers and values containing function info
        csv_path: Path to write the CSV file
        debug: If True, append debug info to DEBUG_PATH
        debug_path: Path to the debug log file

    Returns:
        None
    """
    import csv as csv_module

    print(f"Writing to {csv_path}...")

    # Convert dict to CSV rows
    csv_rows = []
    for identifier, entry in csv.items():
        function = entry["function"]
        module = entry["module"]
        url = entry["url"]
        specified = entry["specified"]
        verified = entry["verified"]

        # Convert boolean to yes/no
        has_spec = "yes" if specified else ""
        has_proof = "yes" if verified else ""

        csv_rows.append(
            {
                "function": function,
                "module": module,
                "link": url,
                "has_spec": has_spec,
                "has_proof": has_proof,
            }
        )

    # Write to CSV file
    with open(csv_path, "w", encoding="utf-8", newline="") as f:
        fieldnames = ["function", "module", "link", "has_spec", "has_proof"]
        writer = csv_module.DictWriter(f, fieldnames=fieldnames)

        writer.writeheader()
        writer.writerows(csv_rows)

    print(f"Wrote {len(csv_rows)} rows to {csv_path}")

    # Debug output
    if debug:
        debug_path.parent.mkdir(parents=True, exist_ok=True)
        with open(debug_path, "a", encoding="utf-8") as f:
            f.write("\n=== write_csv result ===\n")
            f.write(f"Wrote {len(csv_rows)} rows to {csv_path}\n")

    print("Done!")


def extract_nodes_recursive(node, node_map):
    """
    Recursively traverse the tree structure and extract all data.

    Args:
        node: Current node in the tree (dict or list)
        node_map: Dictionary to populate with identifier -> data mapping
    """
    if isinstance(node, dict):
        # Extract identifier from current node
        identifier = node.get("identifier")

        if identifier:
            # Extract children identifiers
            children = node.get("children", [])
            children_identifiers = {
                child.get("identifier"): {"visible": True}
                for child in children
                if isinstance(child, dict) and child.get("identifier")
            }

            # Extract other fields
            dependencies = node.get("dependencies", [])
            # Remove leading "/" from each dependency and convert to dictionary
            dependencies = {
                (dep[1:] if isinstance(dep, str) and dep.startswith("/") else dep): {
                    "visible": True
                }
                for dep in dependencies
            }
            content = node.get("content", "")
            file_type = node.get("file_type", "")
            specified = node.get("specified", False)

            # Store the data for this identifier
            # Different structure for folder vs file entries
            if file_type == "folder":
                node_map[identifier] = {
                    "children": children_identifiers,
                    "file_type": file_type,
                    "url": "",
                    "visible": True,
                }
            else:
                node_map[identifier] = {
                    "dependencies": dependencies,
                    "content": content,
                    "file_type": file_type,
                    "specified": specified,
                    "verified": True,
                    "url": "",
                    "visible": True,
                }

        # Recursively process children
        children = node.get("children", [])
        if children:
            for child in children:
                extract_nodes_recursive(child, node_map)

    elif isinstance(node, list):
        # If node is a list, process each item
        for item in node:
            extract_nodes_recursive(item, node_map)


def tree_to_pvf(tree):
    pvf = {}
    extract_nodes_recursive(tree, pvf)
    return pvf


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


if __name__ == "__main__":
    # Load metadata (repo and url)
    with open(METADATA_PATH, "r", encoding="utf-8") as f:
        metadata = json.load(f)
    repo = metadata["repo"]["id"]
    url = metadata["repo"]["url"]

    # Get API key from environment
    api_key = os.environ.get("VERILIB_API_KEY")
    if not api_key:
        raise ValueError("VERILIB_API_KEY environment variable is not set")

    # Get debug flag
    debug = os.environ.get("VERILIB_DEBUG", "").lower() in ("true", "1", "yes")

    csv = read_csv(csv_path=CSV_PATH, debug=debug)
    pvf = csv_to_pvf(csv, debug=debug)
    tree = pvf_to_tree(pvf, debug=debug)
    deploy(url, repo, api_key, tree, debug=debug)

    # new_csv = pvf_to_csv(pvf, debug=debug)
    # new_csv_path = PROJECT_ROOT / ".verilib" / "curve25519_functions.csv"
    # write_csv(new_csv, csv_path=new_csv_path, debug=debug)
