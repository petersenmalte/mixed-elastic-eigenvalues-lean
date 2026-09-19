#!/usr/bin/env bash
# Fails if `sorry` occurs in the fully proven layers (Stage 1: material algebra, Stage 2:
# abstract eigenvalue identities), or if `axiom` / `native_decide` occur anywhere.
set -euo pipefail
cd "$(dirname "$0")/.."

proven=(
  MixedElasticEigenvalues/Material.lean
  MixedElasticEigenvalues/EigenvalueIdentities.lean
  MixedElasticEigenvalues/Statements/Framework.lean
  MixedElasticEigenvalues/Statements/EigenvalueRate.lean
  MixedElasticEigenvalues/Statements/PostprocessedEigenvalue.lean
  MixedElasticEigenvalues/Statements/Postprocessing.lean
  MixedElasticEigenvalues/Statements/Boffi.lean
  MixedElasticEigenvalues/Statements/APosteriori.lean
)

status=0
for f in "${proven[@]}"; do
  if grep -n -w "sorry" "$f"; then
    echo "::error file=$f::'sorry' is not allowed in $f"
    status=1
  fi
done

if grep -rn -E '^\s*(private |protected |noncomputable )*axiom\s' --include='*.lean' \
    MixedElasticEigenvalues.lean MixedElasticEigenvalues; then
  echo "::error::'axiom' declarations are not allowed"
  status=1
fi

if grep -rn -w "native_decide" --include='*.lean' MixedElasticEigenvalues.lean MixedElasticEigenvalues; then
  echo "::error::'native_decide' is not allowed"
  status=1
fi

if [ "$status" -eq 0 ]; then
  echo "no sorry in ${proven[*]}; no axiom / native_decide anywhere"
fi
exit "$status"
