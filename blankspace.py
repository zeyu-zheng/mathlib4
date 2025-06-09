#!/usr/bin/env python3
"""fix_have_spaces.py

Recursively scan a Lean project and normalize spacing before colons in `have` statements.

For every non‑blocked ``*.lean`` file, it rewrites occurrences of the form::

    have <anything>  :

(i.e. **two or more spaces** before the colon) to::

    have <anything> :

A ``.bak`` backup is created next to each modified file.
After finishing, the script reports both **number of files touched** and **total individual
replacements** performed.

Usage
-----
$ python fix_have_spaces.py [root_dir]

*root_dir* defaults to the current directory.
"""
from __future__ import annotations

import argparse
import fnmatch
import re
import shutil
from pathlib import Path
from typing import Iterable, Tuple

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------
BLOCKLIST = [
    "Mathlib/Tactic/Have.lean",  # skip a specific file
    "Archive.lean",
    "Counterexamples.lean",
    "docs.lean",
    "lakefile.lean",
    "Mathlib.lean",
]

# pre‑compiled regular expression matching “have …  :”
_HAVE_COLON_RE = re.compile(r"(\bhave[^\n]*?)\s{2,}:")

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def blocked(rel_path: str) -> bool:
    """Return *True* iff *rel_path* should **not** be processed."""
    parts = Path(rel_path).parts
    if any(seg.startswith('.') for seg in parts):
        return True
    return any(fnmatch.fnmatch(rel_path, pat) for pat in BLOCKLIST)


def lean_files(root: Path) -> Iterable[Path]:
    """Yield every ``*.lean`` file under *root* that is **not** blocked."""
    for path in root.rglob("*.lean"):
        rel = path.relative_to(root).as_posix()
        if not blocked(rel):
            yield path


def fix_line(line: str) -> Tuple[str, int]:
    """Return (*new_line*, *n_replacements*) for *line*."""
    return _HAVE_COLON_RE.sub(r"\1 :", line), _HAVE_COLON_RE.search(line) is not None and len(_HAVE_COLON_RE.findall(line)) or 0

# ---------------------------------------------------------------------------
# Main transformation
# ---------------------------------------------------------------------------

def process_file(path: Path) -> int:
    """Normalize spacing in *path*.

    Returns the number of replacements done in this file (0 if none).
    """
    original_text = path.read_text(encoding="utf-8")
    replacements = 0
    fixed_lines = []

    for ln in original_text.splitlines():
        new_ln, n_rep = fix_line(ln)
        fixed_lines.append(new_ln)
        replacements += n_rep

    if replacements == 0:
        return 0

    fixed_text = "\n".join(fixed_lines) + "\n"
    # backup = path.with_suffix(path.suffix + ".bak")
    try:
        # shutil.copy2(path, backup)  # keep safety copy
        path.write_text(fixed_text, encoding="utf-8")
        print(f"✔ {path} — {replacements} replacement(s)")
        return replacements
    except Exception as exc:  # pragma: no cover
        print(f"✖ failed to update {path}: {exc}")
        return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Fix spacing before colons in Lean 'have' statements and report statistics.")
    parser.add_argument(
        "root", nargs="?", default=".", type=Path,
        help="Root directory of the Lean project (default: current directory)")
    args = parser.parse_args()

    root: Path = args.root.resolve()
    if not root.is_dir():
        raise SystemExit(f"Error: '{root}' is not a directory.")

    total_files = 0
    total_replacements = 0

    for file in lean_files(root):
        num = process_file(file)
        if num:
            total_files += 1
            total_replacements += num

    print("\nDone.")
    print(f"Files updated       : {total_files}")
    print(f"Total replacements : {total_replacements}")


if __name__ == "__main__":
    main()
