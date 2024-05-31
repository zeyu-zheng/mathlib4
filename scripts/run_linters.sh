#!/usr/bin/env bash

# Meant for automation usage only.
./scripts/update-style-exceptions.sh
env LEAN_ABORT_ON_PANIC=1 lake exe runLinter --update Mathlib
