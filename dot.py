#!/usr/bin/env python3
"""
Rule-based transformer for Lean dot syntax ('·') statements.
Processes lines starting with '·' to remove the dot and adjust indentation by one level.
Skips processing inside def blocks.
"""

import os
import re
import fnmatch
from pathlib import Path
from typing import List, Tuple, Optional


# --------------------------------------------------
# Configuration
# --------------------------------------------------
BLOCKLIST = [
    "Archive.lean",
    "Counterexamples.lean",
    "docs.lean",
    "lakefile.lean",
    "Mathlib.lean",
]


def blocked(rel_path: str) -> bool:
    """Check if a path should be blocked from processing."""
    # skip hidden dirs / files at any depth
    if any(seg.startswith('.') for seg in rel_path.split('/')):
        return True
    # skip user-defined patterns
    return any(fnmatch.fnmatch(rel_path, pat) for pat in BLOCKLIST)


def get_indentation(line: str) -> int:
    """Get the number of leading spaces in a line."""
    return len(line) - len(line.lstrip())


def strip_trailing_spaces(line: str) -> str:
    """Remove trailing spaces from a line."""
    return line.rstrip()


def is_dot_line(line: str) -> bool:
    """Check if a line starts with '·' (after stripping indentation)."""
    stripped = line.lstrip()
    return stripped.startswith('·')


def is_def_line(line: str) -> bool:
    """Check if a line starts a def block."""
    return 'def ' in line


def find_block_end(lines: List[str], start_idx: int) -> int:
    """
    Find the end of a block (until empty line or end of document).
    Returns the index of the last line in the block.
    """
    if start_idx >= len(lines) - 1:
        return len(lines) - 1

    # Block ends at first empty line or end of document
    for i in range(start_idx + 1, len(lines)):
        if lines[i].strip() == '':
            return i - 1

    return len(lines) - 1


def parse_dot_components(line: str) -> Optional[Tuple[str, str, int]]:
    """
    Parse a '· content' line.
    Returns (content, indent, dot_space_count) or None if not matching pattern.
    dot_space_count is the number of characters occupied by '·' and following spaces.
    """
    stripped = line.lstrip()
    if not stripped.startswith('·'):
        return None

    # Find how much space the dot and following spaces take
    dot_match = re.match(r'·\s*', stripped)
    if not dot_match:
        return None

    dot_space_count = len(dot_match.group(0))  # '·' + following spaces
    content = stripped[dot_space_count:]  # Content after dot and spaces
    indent = ' ' * get_indentation(line)  # Original indentation of the '·'

    return (content, indent, dot_space_count)


def find_dot_environment_end(lines: List[str], start_idx: int) -> int:
    """
    Find the end of a dot environment.
    Returns the index of the last line in the environment.
    """
    if start_idx >= len(lines) - 1:
        return start_idx

    dot_indent = get_indentation(lines[start_idx])

    for i in range(start_idx + 1, len(lines)):
        line_indent = get_indentation(lines[i])
        # Empty lines don't break the environment
        if lines[i].strip() == '':
            continue
        # If indentation is not greater than dot line, environment ends
        if line_indent <= dot_indent:
            return i - 1

    return len(lines) - 1


def reduce_indentation(line: str, reduction: int) -> str:
    """Reduce line indentation by specified amount."""
    current_indent = get_indentation(line)
    if current_indent >= reduction:
        return line[reduction:]
    return line.lstrip()


def process_dot_environment(lines: List[str], start_idx: int, end_idx: int) -> List[str]:
    """Process a dot environment (single or multi-line)."""
    dot_line = lines[start_idx]
    components = parse_dot_components(dot_line)
    if not components:
        return lines[start_idx:end_idx+1]

    content, indent, dot_space_count = components
    result = []

    # Add the content after dot at the same indentation as the original dot
    if content:
        result.append(strip_trailing_spaces(indent + content))

    # For subsequent lines, reduce indentation by the dot space count
    for i in range(start_idx + 1, end_idx + 1):
        reduced_line = reduce_indentation(lines[i], dot_space_count)
        result.append(strip_trailing_spaces(reduced_line))

    return result


def process_lean_file(file_path: Path) -> int:
    """Process a single Lean file. Returns count of transformed dot statements."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return 0

    # Remove newlines
    lines = [line.rstrip('\n') for line in lines]

    result = []
    i = 0
    transformed_count = 0

    while i < len(lines):
        line = lines[i]

        # Check if we're entering a def block
        if is_def_line(line):
            # Find the end of def block (until empty line or end)
            block_end = find_block_end(lines, i)
            # Copy all lines in def block without processing
            for j in range(i, block_end + 1):
                result.append(strip_trailing_spaces(lines[j]))
            i = block_end
        elif is_dot_line(line):
            # This is a '·' line - process only one level
            env_end = find_dot_environment_end(lines, i)
            transformed_count += 1

            # Process the dot environment
            processed = process_dot_environment(lines, i, env_end)
            result.extend(processed)
            i = env_end  # Skip to end of environment
        else:
            # Not our target pattern, keep as is (but strip trailing spaces)
            result.append(strip_trailing_spaces(line))

        i += 1

    # Write back to file
    try:
        with open(file_path, 'w', encoding='utf-8') as f:
            for line in result:
                f.write(line + '\n')
        if transformed_count > 0:
            print(f"Processed: {file_path} (transformed {transformed_count} dot statements)")
    except Exception as e:
        print(f"Error writing {file_path}: {e}")
        return 0

    return transformed_count


def main():
    """Main function to process all Lean files."""
    root_dir = Path.cwd()

    # Find all .lean files
    lean_files = []
    for path in root_dir.rglob("*.lean"):
        rel_path = str(path.relative_to(root_dir))
        if not blocked(rel_path):
            lean_files.append(path)

    print(f"Found {len(lean_files)} Lean files to process")

    # Process each file and collect statistics
    total_transformed = 0
    files_modified = 0

    for file_path in lean_files:
        count = process_lean_file(file_path)
        if count > 0:
            files_modified += 1
            total_transformed += count

    print("\n" + "="*50)
    print(f"Processing complete!")
    print(f"Total files processed: {len(lean_files)}")
    print(f"Files modified: {files_modified}")
    print(f"Total '·' statements transformed: {total_transformed}")
    print("="*50)


if __name__ == "__main__":
    main()
