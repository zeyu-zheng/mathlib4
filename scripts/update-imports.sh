#!/usr/bin/env bash

# # Update `Mathlib.lean`

# Run this script from the root of mathlib using:
# ./scripts/update-imports.sh
# to update the contents of `Mathlib.lean`.

find Mathlib -name "*.lean" | env LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > Mathlib.lean
