#!/usr/bin/env python3
"""
Script to extract comments from Rust files in curve25519-dalek/src folder and save to a file.
For each file, creates a header with the file path and lists comments after removing
comment symbols like //, ///, and //! from the start of each line.
Outputs in Markdown format with proper headers.
"""

import os
import re
from pathlib import Path

def extract_comments_from_rust_file(file_path):
    """
    Extract comments from a Rust file.
    
    Args:
        file_path (str): Path to the Rust file
        
    Returns:
        list: List of comment lines with comment symbols removed, preserving empty lines and uncommented newlines
    """
    comments = []
    in_comment_block = False
    consecutive_empty_lines = 0
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
            
        for line in lines:
            line = line.rstrip()
            
            # Match different types of Rust comments
            # //! - module-level documentation
            # /// - item-level documentation  
            # // - regular line comments
            # /* */ - block comments (handle basic cases)
            
            # Remove leading whitespace
            stripped = line.lstrip()
            
            # Check if this line is a comment
            is_comment = False
            comment_content = ""
            
            # Check for //! comments
            if stripped.startswith('//!'):
                comment_content = stripped[3:].lstrip()
                is_comment = True
                    
            # Check for /// comments
            elif stripped.startswith('///'):
                comment_content = stripped[3:].lstrip()
                is_comment = True
                    
            # Check for // comments (but not //! or ///)
            elif stripped.startswith('//') and not stripped.startswith('///'):
                comment_content = stripped[2:].lstrip()
                is_comment = True
                    
            # Handle block comments /* ... */
            elif '/*' in stripped and '*/' in stripped:
                # Simple block comment on single line
                start = stripped.find('/*')
                end = stripped.find('*/')
                if start != -1 and end != -1 and end > start:
                    comment_content = stripped[start+2:end].strip()
                    if comment_content:
                        is_comment = True
            
            # Process the line
            if is_comment:
                # Filter out emacs-style mode lines and other pre-matter
                if should_skip_comment(comment_content):
                    continue
                    
                # We're in a comment block
                if not in_comment_block:
                    # Starting a new comment block
                    in_comment_block = True
                    # Add empty line if we had uncommented lines before
                    if consecutive_empty_lines > 0:
                        comments.append("")
                
                # Add the comment content
                comments.append(comment_content)
                consecutive_empty_lines = 0
                
            else:
                # This is not a comment line
                if in_comment_block:
                    # We're transitioning from comment block to non-comment
                    in_comment_block = False
                    consecutive_empty_lines = 1
                else:
                    # We're in a non-comment section
                    if not line.strip():
                        # Empty line
                        consecutive_empty_lines += 1
                    else:
                        # Non-empty non-comment line
                        consecutive_empty_lines = 0
                        
    except Exception as e:
        print(f"Error reading file {file_path}: {e}")
        return []
        
    return comments

def should_skip_comment(comment_content):
    """
    Check if a comment should be skipped (filtered out).
    
    Args:
        comment_content (str): The comment content
        
    Returns:
        bool: True if the comment should be skipped
    """
    # Skip emacs-style mode lines
    if comment_content.strip() in [
        "-*- mode: rust; -*-",
        "-*- mode: rust; coding: utf-8; -*-",
        "-*- mode: rust; coding: utf-8 -*-",
        "-*- coding: utf-8 -*-",
        "-*- coding: utf-8; -*-"
    ]:
        return True
    
    # # Skip other common pre-matter patterns
    # skip_patterns = [
    #     "vim:",
    #     "vi:",
    #     "coding:",
    #     "mode:",
    #     "This file is part of",
    #     "Copyright (c) ",
    #     "See LICENSE for licensing information.",
    #     "Authors:",
    #     "Authors:",
    #     "Portions Copyright"
    # ]
    
    # comment_lower = comment_content.lower()
    # for pattern in skip_patterns:
    #     if pattern.lower() in comment_lower:
    #         return True
    
    return False

def find_rust_files(directory):
    """
    Recursively find all .rs files in the given directory.
    
    Args:
        directory (str): Directory to search
        
    Returns:
        list: List of paths to .rs files
    """
    rust_files = []
    
    try:
        for root, dirs, files in os.walk(directory):
            for file in files:
                if file.endswith('.rs'):
                    rust_files.append(os.path.join(root, file))
    except Exception as e:
        print(f"Error walking directory {directory}: {e}")
        
    return sorted(rust_files)

def convert_latex_delimiters(text):
    """
    Convert LaTeX formula delimiters in the text.
    
    Args:
        text (str): The text to convert
        
    Returns:
        str: Text with converted LaTeX delimiters
    """
    # Convert \( and \) to $ (inline math)
    text = text.replace(r'\\(', '$')
    text = text.replace(r'\\)', '$')
    
    # Convert \[ and \] to $$ (display math)
    text = text.replace(r'\\[', '$$')
    text = text.replace(r'\\]', '$$')
    
    # Convert \^ to ^ within LaTeX formulas
    text = text.replace(r'\^', '^')
    
    # Convert \_ to _ within LaTeX formulas
    text = text.replace(r'\_', '_')
    
    return text

def format_comments_for_markdown(comments):
    """
    Format comments for Markdown output, preserving the original spacing structure.
    Converts comment headers (lines starting with #) into Markdown headers by appending ##.
    Converts dashed header patterns into ### headers.
    Converts LaTeX formula delimiters: \\(/\\) to $ and \\[/\\] to $$.
    
    Args:
        comments (list): List of comment lines
        
    Returns:
        str: Formatted markdown text
    """
    if not comments:
        return "(No comments found)"
    
    formatted_lines = []
    i = 0
    
    while i < len(comments):
        comment = comments[i]
        
        # Check if this is a dashed header pattern
        if (i + 2 < len(comments) and 
            comment.strip().startswith('-') and comment.strip().endswith('-') and
            comments[i + 1].strip() and not comments[i + 1].strip().startswith('-') and
            comments[i + 2].strip().startswith('-') and comments[i + 2].strip().endswith('-')):
            
            # This is a dashed header pattern, convert to ### header
            header_text = comments[i + 1].strip()
            formatted_lines.append(f"### {header_text}")
            # Skip the next two lines (the header text and the closing dashes)
            i += 3
        else:
            # Check if this is a header (starts with # and has content)
            if comment.strip().startswith('#') and len(comment.strip()) > 1:
                # Append ## to make it a Markdown header
                formatted_lines.append(f"##{comment.strip()}")
            else:
                # Regular comment line - convert LaTeX delimiters
                converted_comment = convert_latex_delimiters(comment)
                formatted_lines.append(converted_comment)
            i += 1
    
    # Join with newlines to preserve the original spacing
    return "\n".join(formatted_lines)

def main():
    """Main function to extract comments from all Rust files and save to a file."""
    
    # Path to the src directory
    src_dir = "curve25519-dalek/src"
    
    # Output file
    output_file = "rust_comments_extracted.md"
    
    # Check if the directory exists
    if not os.path.exists(src_dir):
        print(f"Error: Directory {src_dir} does not exist.")
        return
    
    # Find all Rust files
    rust_files = find_rust_files(src_dir)
    
    if not rust_files:
        print(f"No .rs files found in {src_dir}")
        return
    
    print(f"Found {len(rust_files)} Rust files in {src_dir}")
    print(f"Extracting comments to {output_file}...")
    
    # Open output file for writing
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(f"# Comments extracted from {len(rust_files)} Rust files in {src_dir}\n\n")
        
        # Process each file
        for file_path in rust_files:
            # Get relative path for cleaner output
            rel_path = os.path.relpath(file_path, "curve25519-dalek")
            
            # Extract comments
            comments = extract_comments_from_rust_file(file_path)
            
            # Write file header as markdown
            f.write(f"## {rel_path}\n\n")
            
            # Format and write comments
            formatted_comments = format_comments_for_markdown(comments)
            f.write(formatted_comments)
            f.write("\n\n")
    
    print(f"Comments extracted successfully to {output_file}")

if __name__ == "__main__":
    main() 