import Lean
import MixedElasticEigenvalues.Material
import MixedElasticEigenvalues.EigenvalueIdentities
import MixedElasticEigenvalues.Statements.APosteriori
import MixedElasticEigenvalues.Statements.PostprocessedEigenvalue
import MixedElasticEigenvalues.Statements.Boffi

/-!
# Axiom audit

`#check_axioms_of M₁ M₂ …` runs `#print axioms` for every declaration of the modules
`M₁ M₂ …` and fails — so that `lake build` fails — if one of them depends on an axiom
other than `propext`, `Classical.choice` and `Quot.sound`. In particular `sorryAx` is
rejected, so the modules listed at the end of this file are guaranteed to contain
complete proofs.

The audit runs during `lake build` (this file is part of the library) and again in the CI
step `scripts/check_axioms.sh`, which shows the full report.
-/

open Lean Elab Command

namespace MixedElasticEigenvalues.Audit

/-- The axioms of standard classical mathematics in Lean/Mathlib. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Print the axioms used by every (non-internal) declaration of the given modules and fail
if one of them uses an axiom outside `allowedAxioms`. -/
elab "#check_axioms_of " mods:ident+ : command => do
  let env ← getEnv
  let mut bad : Array (Name × Array Name) := #[]
  let mut count : Nat := 0
  for m in mods do
    let modName := m.getId
    let some idx := env.getModuleIdx? modName
      | throwError "axiom audit: module {modName} is not imported"
    let data := env.header.moduleData[idx.toNat]!
    for n in data.constNames do
      if n.isInternal then continue
      let axs ← collectAxioms n
      count := count + 1
      logInfo m!"'{n}' depends on axioms: {axs.toList}"
      if axs.any (fun a => !allowedAxioms.contains a) then
        bad := bad.push (n, axs)
  if bad.isEmpty then
    logInfo m!"axiom audit passed: {count} declarations use only {allowedAxioms}"
  else
    throwError "axiom audit failed, disallowed axioms in: {bad}"

/-- Print the axioms used by every declaration of the given modules without failing; used
for the statement modules, whose theorems depend on `sorryAx` by design. -/
elab "#report_axioms_of " mods:ident+ : command => do
  let env ← getEnv
  for m in mods do
    let modName := m.getId
    let some idx := env.getModuleIdx? modName
      | throwError "axiom report: module {modName} is not imported"
    let data := env.header.moduleData[idx.toNat]!
    for n in data.constNames do
      if n.isInternal then continue
      let axs ← collectAxioms n
      if axs.contains ``sorryAx then
        logInfo m!"'{n}' depends on axioms: {axs.toList} (statement only)"

end MixedElasticEigenvalues.Audit

#check_axioms_of MixedElasticEigenvalues.Material MixedElasticEigenvalues.EigenvalueIdentities
  MixedElasticEigenvalues.Statements.Framework MixedElasticEigenvalues.Statements.EigenvalueRate
  MixedElasticEigenvalues.Statements.PostprocessedEigenvalue
  MixedElasticEigenvalues.Statements.Postprocessing
  MixedElasticEigenvalues.Statements.Boffi

#report_axioms_of MixedElasticEigenvalues.Statements.Cea
  MixedElasticEigenvalues.Statements.APosteriori
