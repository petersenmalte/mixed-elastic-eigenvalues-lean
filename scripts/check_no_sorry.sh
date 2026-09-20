#!/usr/bin/env bash
# Reject unfinished proofs and extra axiom declarations in every project Lean file.
set -euo pipefail
cd "$(dirname "$0")/.."

status=0
if grep -rn -w -E 'sorry|admit' --include='*.lean' \
    MixedElasticEigenvalues.lean MixedElasticEigenvalues; then
  echo "::error::unfinished proofs are not allowed"
  status=1
fi

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
  echo "no unfinished proofs, axiom declarations or native_decide in any project Lean file"
fi
exit "$status"
