#!/usr/bin/env python3
"""
Rule-based transformer for Lean 'have' statements.
Step 1: Only process 'have hx : type := by' cases.
Filters out cases where have is used as a proof term.
Skips processing inside def blocks and proof term blocks.
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
    "Mathlib/Tactic/Have.lean",  # skip a specific file
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


def normalize_spaces(text: str) -> str:
    """Replace multiple spaces with single space."""
    return re.sub(r'\s+', ' ', text)


def strip_trailing_spaces(line: str) -> str:
    """Remove trailing spaces from a line."""
    return line.rstrip()


def is_have_line(line: str) -> bool:
    """Check if a line starts with 'have' (after stripping indentation)."""
    stripped = line.lstrip()
    return stripped.startswith('have ')


def parse_have_components(line: str) -> Optional[Tuple[str, str, str, str]]:
    """
    Parse a 'have ... : ... := by ...' line.
    Returns (have_name, type, by_content, indent) or None if not matching pattern.
    """
    # Find ':=' position
    assign_match = re.search(r':=', line)
    if not assign_match:
        return None

    assign_pos = assign_match.start()
    before_assign = line[:assign_pos]
    after_assign = line[assign_pos+2:]  # Skip ':='

    # Check if there's a colon before :=
    colon_match = re.search(r':', before_assign)
    if not colon_match:
        return None

    colon_pos = colon_match.start()

    # Check if := is followed by 'by' (with any amount of whitespace)
    by_match = re.match(r'\s*by\s*(.*)', after_assign)
    if not by_match:
        return None

    # Extract components
    indent = ' ' * get_indentation(line)
    have_part = line[:colon_pos].strip()  # e.g., 'have hx'
    type_part = before_assign[colon_pos+1:].strip()  # type between : and :=
    by_content = by_match.group(1).strip()  # content after 'by'

    # Normalize have_part to ensure single space after 'have'
    have_match = re.match(r'(have)\s+(.+)', have_part)
    if have_match:
        have_part = f"have {have_match.group(2)}"

    return (have_part, type_part, by_content, indent)


def has_colon_assign_by_pattern(line: str) -> bool:
    """Check if line has pattern: have ... : ... := by ..."""
    return parse_have_components(line) is not None


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


def starts_proof_term_block(lines: List[str], idx: int) -> bool:
    """
    Check if the previous line indicates start of a proof term block.
    This is when previous non-empty line ends with ':=', '=>', or '→'
    """
    if idx == 0:
        return False

    # Look for previous non-empty line
    for i in range(idx - 1, -1, -1):
        stripped = lines[i].strip()
        if stripped:  # Found non-empty line
            return (stripped.endswith(':=') or
                    stripped.endswith('=>') or
                    stripped.endswith('→'))

    return False


def is_def_line(line: str) -> bool:
    """Check if a line starts a def block."""
    return 'def ' in line


def find_have_environment_end(lines: List[str], start_idx: int) -> int:
    """
    Find the end of a have environment.
    Returns the index of the last line in the environment.
    """
    if start_idx >= len(lines) - 1:
        return start_idx

    have_indent = get_indentation(lines[start_idx])

    for i in range(start_idx + 1, len(lines)):
        line_indent = get_indentation(lines[i])
        # Empty lines don't break the environment
        if lines[i].strip() == '':
            continue
        # If indentation is not greater than have line, environment ends
        if line_indent <= have_indent:
            return i - 1

    return len(lines) - 1


def process_single_line_have_by(line: str) -> List[str]:
    """Process a single-line 'have : t := by e' statement."""
    components = parse_have_components(line)
    if not components:
        return [line]

    have_part, type_part, by_content, indent = components

    # Build result with normalized spacing
    new_have = f"{indent}{have_part} : {type_part}"
    result = [strip_trailing_spaces(new_have)]

    # If there's content after 'by', add it on next line
    if by_content:
        result.append(strip_trailing_spaces(indent + by_content))

    return result


def reduce_indentation(line: str, reduction: int) -> str:
    """Reduce line indentation by specified amount."""
    current_indent = get_indentation(line)
    if current_indent >= reduction:
        return line[reduction:]
    return line.lstrip()


def process_multi_line_have_by(lines: List[str], start_idx: int, end_idx: int) -> List[str]:
    """Process a multi-line 'have : t := by ...' environment."""
    have_line = lines[start_idx]
    components = parse_have_components(have_line)
    if not components:
        return lines[start_idx:end_idx+1]

    have_part, type_part, by_content, indent = components

    # Build result with normalized spacing
    new_have = f"{indent}{have_part} : {type_part}"
    result = [strip_trailing_spaces(new_have)]

    # If there's content after 'by' on same line, add it
    if by_content:
        result.append(strip_trailing_spaces(indent + by_content))

    # Determine indentation reduction
    have_indent = get_indentation(have_line)
    indent_reduction = 0
    for i in range(start_idx + 1, end_idx + 1):
        if lines[i].strip():
            indent_reduction = get_indentation(lines[i]) - have_indent
            break

    if indent_reduction <= 0:
        indent_reduction = 2  # Default to 2 spaces

    # Add subsequent lines with reduced indentation
    for i in range(start_idx + 1, end_idx + 1):
        reduced_line = reduce_indentation(lines[i], indent_reduction)
        result.append(strip_trailing_spaces(reduced_line))

    return result


def process_lean_file(file_path: Path) -> int:
    """Process a single Lean file. Returns count of transformed have statements."""
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

        # Check if we're in a proof term block (previous line ends with :=, =>, or →)
        if starts_proof_term_block(lines, i):
            # Skip entire block until empty line
            block_end = find_block_end(lines, i)
            for j in range(i, block_end + 1):
                result.append(strip_trailing_spaces(lines[j]))
            i = block_end
        # Check if we're entering a def block
        elif is_def_line(line):
            # Find the end of def block (until empty line or end)
            block_end = find_block_end(lines, i)
            # Copy all lines in def block without processing
            for j in range(i, block_end + 1):
                result.append(strip_trailing_spaces(lines[j]))
            i = block_end
        elif is_have_line(line) and has_colon_assign_by_pattern(line):
            # This is a 'have : t := by' line used as a tactic
            env_end = find_have_environment_end(lines, i)
            transformed_count += 1

            if env_end == i:
                # Single-line environment
                processed = process_single_line_have_by(line)
                result.extend(processed)
            else:
                # Multi-line environment
                processed = process_multi_line_have_by(lines, i, env_end)
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
            print(f"Processed: {file_path} (transformed {transformed_count} have statements)")
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
    print(f"Total 'have := by' statements transformed: {total_transformed}")
    print("="*50)


if __name__ == "__main__":
    main()
