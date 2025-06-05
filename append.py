#!/usr/bin/env python3
"""
have_import.py  – add/remove `import Mathlib.Tactic.Have`
to/from every .lean file under the current directory, except BLOCKLIST.

Edit BLOCKLIST as needed, then run:
    python have_import.py
Comment out either add() or remove() at the bottom to choose the action.
"""

import pathlib, fnmatch

# ---- paths (relative to project root) to skip ----
BLOCKLIST = [
    # "tests/*",            # skip everything in tests/
    "Mathlib/Tactic/Have.lean", # skip a specific file
    "Archive.lean",
    "docs.lean",
    "lakefile.lean",
    "Mathlib.lean",
]
# --------------------------------------------------

IMPORT_LINE = "import Mathlib.Tactic.Have"
IMPORT_LINE_NL = IMPORT_LINE + "\n"

def blocked(rel_path: str) -> bool:
    # skip hidden dirs / files at any depth
    if any(seg.startswith('.') for seg in rel_path.split('/')):
        return True
    # skip user-defined patterns
    return any(fnmatch.fnmatch(rel_path, pat) for pat in BLOCKLIST)

def add(root: str = ".") -> None:
    """Prepend IMPORT_LINE to every .lean file (silent if duplicates)."""
    root_path = pathlib.Path(root).resolve()
    for f in root_path.rglob("*.lean"):
        rel = f.relative_to(root_path).as_posix()
        if blocked(rel):
            continue
        text = f.read_text(encoding="utf-8")
        f.write_text(IMPORT_LINE_NL + text, encoding="utf-8")

def remove(root: str = ".") -> None:
    """Remove IMPORT_LINE if it appears as the first line."""
    root_path = pathlib.Path(root).resolve()
    for f in root_path.rglob("*.lean"):
        rel = f.relative_to(root_path).as_posix()
        if blocked(rel):
            continue
        lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
        if lines and lines[0].strip() == IMPORT_LINE:
            f.write_text("".join(lines[1:]), encoding="utf-8")

# --------------------------------------------------
if __name__ == "__main__":
    add()      # <-- run this to ADD the import line
    # remove() # <-- uncomment this (and comment add()) to REMOVE it
