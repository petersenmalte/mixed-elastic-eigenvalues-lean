# Postprocessing of mixed elastic eigenvalues – Lean formalization

Master's thesis in mathematics by Malte Petersen (Institut für Numerische Simulation,
Universität Bonn, 2022; advisor Prof. Dr. Joscha Gedicke, second advisor Prof. Dr. Ira Neitzel).

The thesis improves the eigenvalue approximation of the Falk mixed finite element method
for elasticity with weakly imposed symmetry by a local postprocessing, and proves a priori
and a posteriori error estimates.

- `thesis/` – the thesis as PDF
- `MixedElasticEigenvalues/` – Lean 4 formalization (work in progress, currently empty)
- `ROADMAP.md` – which results of the thesis are to be formalized, and in which order

## Build

```sh
lake update          # resolves Mathlib and syncs lean-toolchain
lake exe cache get   # download prebuilt Mathlib
lake build
```

## Rights

The thesis PDF is © Malte Petersen. No license has been granted for it.
