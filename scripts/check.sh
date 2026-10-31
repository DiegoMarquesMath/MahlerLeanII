#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

mkdir -p build
{
  lean --version
  lake build
  for source_file in MahlerLeanII/*.lean; do
    lake env lean -DwarningAsError=true "$source_file"
  done
  lake env lean -DwarningAsError=true scripts/Audit.lean
  printf '%s\n' 'Build and axiom audit passed for the current declared scope.'
} 2>&1 | tee build/verification.log
