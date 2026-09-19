#!/usr/bin/env bash
# Runs the axiom audit in MixedElasticEigenvalues/Axioms.lean and prints its report.
# The audit itself fails (non-zero exit) if a declaration of the proven modules uses an axiom
# other than propext, Classical.choice, Quot.sound (e.g. sorryAx).
set -euo pipefail
cd "$(dirname "$0")/.."

if ! out=$(lake env lean MixedElasticEigenvalues/Axioms.lean 2>&1); then
  echo "$out"
  echo "::error::axiom audit failed"
  exit 1
fi
echo "$out"
echo "$out" | grep -q "axiom audit passed" || { echo "::error::audit summary missing"; exit 1; }
