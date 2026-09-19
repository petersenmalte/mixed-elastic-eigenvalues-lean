# Postprocessing of mixed elastic eigenvalues – Lean formalization

[![Lean CI](https://github.com/petersenmalte/mixed-elastic-eigenvalues-lean/actions/workflows/lean_ci.yml/badge.svg)](https://github.com/petersenmalte/mixed-elastic-eigenvalues-lean/actions/workflows/lean_ci.yml)

Master's thesis in mathematics by Malte Petersen (Institut für Numerische Simulation,
Universität Bonn, 2022; advisor Prof. Dr. Joscha Gedicke, second advisor Prof. Dr. Ira Neitzel),
partially formalized in Lean 4 with Mathlib.

The thesis improves the eigenvalue approximation of the Falk mixed finite element method
for elasticity with weakly imposed symmetry by a local postprocessing, and proves a priori
and a posteriori error estimates.

- `thesis/` – the thesis as PDF (page numbers below refer to the printed page numbers)
- `MixedElasticEigenvalues/` – the Lean 4 formalization (see the table below)
- `ROADMAP.md` – what remains to be done, and in which order
- `scripts/` – the checks run by CI

## What is formalized

Three layers, in increasing distance from the thesis's proofs:

1. **Material algebra** (`Material.lean`): pointwise linear algebra of `2×2` tensors,
   Chapter 2. Fully proved.
2. **Abstract eigenvalue identities** (`EigenvalueIdentities.lean`): Lemma 4.9 and
   Lemma 5.6 in an abstract real inner product space, with the variational equations
   (36), (37) and (53) as hypotheses. Fully proved. Square roots `C^{±1/2}` of the
   material operator are avoided by working with the quadratic forms `⟪Cξ, ξ⟫`
   and `⟪C⁻¹τ, τ⟫` (definition (5)).
3. **Theorem statements** (`Statements/`): the main theorems of Chapters 3–6 as
   Lean statements over abstract families of discrete spaces, with every finite
   element property (stability, approximation, postprocessing, interpolation) as a
   typed hypothesis (`structure`), each with a trivial model showing the hypotheses are
   satisfiable. Theorems 4.10, 5.1 and 5.7 are proved; the remaining proofs (Theorems
   3.1, 4.7, 6.2, 6.4) are open (`sorry`, each with a comment on what the proof in the
   thesis needs).

| Lean file / declaration | Thesis | Source | Status |
|---|---|---|---|
| `Material.lean`: `frob`, `frobSq`, `skw`, `sym`, `dev`, `matC`, `matCinv` | Ch. 2, pp. 7–10; (3), (4) | thesis | definitions |
| `sym_add_skw`, `skw_transpose`, `skw_eq_self_iff`, `trace_skw`, `frob_sym_skw` | p. 7 | thesis | proved |
| `frob_trace_smul_one`, `frob_dev_dev`, `trace_dev`, `frob_dev_one` | (12), p. 13 | thesis | proved |
| `frobSq_dev_le`, `trace_sq_le_two_mul_frobSq`, `sqrt_frobSq_dev_le`, `abs_trace_le` | `‖dev τ‖ ≤ ‖τ‖`, `‖τ‖ ≥ c‖tr τ‖`, p. 13 | thesis | proved (`c = 1/√2`) |
| `matC_matCinv`, `matCinv_matC` | (4), p. 9 | thesis | proved |
| `frob_matCinv`, `frob_matCinv_symm` | (6), p. 10 | thesis | proved |
| `frob_matCinv_dev_trace` | reformulation of `a(σ,τ)`, p. 13 | thesis | proved |
| `frob_matCinv_self_ge` | `a(τ,τ) ≥ ‖τ‖²/(2(λ+μ))`, p. 13 | thesis | proved (`λ ≥ 0`) |
| `dev_matCinv` | `dev(C⁻¹τ) = dev τ/(2μ)`, p. 14 | thesis | proved |
| `frob_matC_symm`, `frob_matC_self`, `frob_matC_self_nonneg`, `frob_matC_self_pos` | symmetry and positive definiteness of `C` | thesis | proved (`μ > 0`, `λ + μ > 0`) |
| `matC_of_skew`, `matCinv_of_skew`, `frob_matC_skew` | `Cγ = 2μγ` for skew `γ`, p. 30 | thesis | proved |
| `EigenvalueIdentities.lean`: `MaterialOperator`, `MixedEigenpair`, `DiscreteMixedEigenpair` | (36), (37), p. 26 | thesis | definitions (hypotheses) |
| `energy_Cinv_add` | `‖C⁻¹e + d‖²_{C^{1/2}}` expansion, p. 30 | thesis | proved |
| `eigenvalue_identity`, `eigenvalue_identity_raw` | Lemma 4.9, p. 30 | thesis | proved |
| `postprocessedEigenvalue` | Definition 5.5, (59), p. 41 | thesis | definition |
| `postprocessed_eigenvalue_identity`, `…_raw` | Lemma 5.6, (60), pp. 41–42 | thesis | proved (see errata) |
| `Statements/Framework.lean`: `DiscreteFamily`, `MixedSource`, `DiscreteMixedSource`, `IsKernel`, `IsDiscreteKernel`, `hdivNorm`, `SobolevNorms` | (11), (17), (18), pp. 6, 14 | thesis | definitions |
| `Statements/Cea.lean`: `CeaHypotheses`, `cea_estimate` | Theorem 3.1, p. 16 | [5, Thm 3.1], [9] | `sorry`: Brezzi-type estimate not carried out; needs an `L²`-quasi-optimal Fortin operator as extra hypothesis |
| `CeaHypotheses.coercive_discrete` | coercivity on `ker(Bₕ + Cₕ)`, p. 15 | thesis | proved |
| `Statements/Boffi.lean`: `BoffiHypotheses`, `uniform_convergence` | Theorem 4.7, Def. 4.4–4.6, pp. 27–28 | [3, Thm 14.6] | `sorry`: reduces to Theorem 3.1 plus approximability; strong approximability of `X⁰` added as hypothesis |
| `Statements/EigenvalueRate.lean`: `EigenfunctionRates`, `eigenvalue_rate` | Theorem 4.10, p. 30 | thesis | proved from Lemma 4.9 and the rate hypotheses (squared form, see errata) |
| `Statements/Postprocessing.lean`: `Postprocessing`, `PostprocessingRates` | (52), (53), pp. 37–38 | thesis, [18], [24] | definitions (hypotheses) |
| `proj_unique`, `proj_eq_self`, `proj_sub`, `pstar_eq`, `ph_ustar` | (50), (51), (52), p. 36 | thesis | proved |
| `postprocessed_eigenfunction_rate` | Theorem 5.1, pp. 38–40 | thesis, [18], [24] | proved from (51), (55), (57), (58), Poincaré and inverse estimates |
| `Statements/PostprocessedEigenvalue.lean`: `PostprocessedEigenvalueRates`, `postprocessed_eigenvalue_rate` | Theorem 5.7, p. 43 | thesis | proved from Lemma 5.6, the rate hypotheses and a Rayleigh-quotient bound for `κ*ₕ`, for `h ≤ h₀` (squared form, see errata) |
| `Statements/APosteriori.lean`: `APosterioriData`, `estimatorSq`, `estimator`, `Postprocessing.hot` | estimator `η`, (62), (67), pp. 44–48 | thesis, [11] | definitions |
| `APosterioriData.reliability` | Theorem 6.2, p. 48 | thesis, [11] | `sorry`: Lemma 6.1 (residual estimates with Scott–Zhang) plus (67) |
| `APosterioriData.eigenvalue_reliability` | Theorem 6.4, p. 50 | thesis | `sorry`: Lemma 5.6, Gauss' theorem, Young, Theorem 6.2, (67) |
| Proposition 2.1, Lemma 2.2, Theorem 3.2, Proposition 3.4, Lemma 3.5, Remark 3.6, Theorem 3.3 | pp. 13–22 | [4], [5], [7], [8], [10], [14] | not formalizable at this level (Sobolev spaces on domains, `H(div)`, Stokes, BDM interpolation) |
| Theorem 4.8, Lemma 4.11, Lemma 4.14, Theorem 6.3 | pp. 29–34, 49 | thesis, [17] | not formalized (their content enters Stage 3 as rate hypotheses) |
| Chapter 7 | pp. 51–67 | thesis | numerical experiments, not formalizable |

Every statement of layer 3 carries a docstring quoting the theorem of the thesis with its
number and page, an explicit constant (`∃ C > 0` uniform in the mesh index), and
mesh-dependent rates as `C * h i ^ k * (…)` over an abstract family of meshes
`i : ι` with mesh size `h i → 0` along a filter.

## Verification

The [CI workflow](https://github.com/petersenmalte/mixed-elastic-eigenvalues-lean/actions/workflows/lean_ci.yml)
(`.github/workflows/lean_ci.yml`) runs on every push:

1. `lake build` of every module under `MixedElasticEigenvalues/` (the `globs` in
   `lakefile.toml` make sure that files that are not imported are still checked);
2. `scripts/check_no_sorry.sh`: fails if `sorry` occurs in any of the proved modules
   (`Material.lean`, `EigenvalueIdentities.lean`, `Statements/Framework.lean`,
   `Statements/EigenvalueRate.lean`, `Statements/Postprocessing.lean`,
   `Statements/PostprocessedEigenvalue.lean`), or if `axiom` / `native_decide` occur
   anywhere;
3. the axiom audit `MixedElasticEigenvalues/Axioms.lean` (run during `lake build` and again by
   `scripts/check_axioms.sh`): `#print axioms` for every declaration of the proved
   modules; the build fails if any axiom other than `propext`, `Classical.choice` and
   `Quot.sound` is used (in particular `sorryAx`). For the remaining statement modules
   the audit only reports which declarations depend on `sorryAx`.

## Build

```sh
lake exe cache get   # download prebuilt Mathlib (lake-manifest.json pins the version)
lake build
```

## The abstract model

`H` (tensors, `L²(Ω;ℝ²ˣ²)`) and `U` (vectors, `L²(Ω;ℝ²)`) are real inner product spaces,
`div : H →ₗ[ℝ] U` is a linear map, `X ⊆ H` is the subspace of skew-symmetric tensors and
`S₀ ⊆ H` the test space of the first equation. The material law is an operator
`C : H →L[ℝ] H` with inverse `C⁻¹`, symmetric, nonnegative and with `Cη = 2μη` on `X`
(`MaterialOperator`); `Material.lean` shows that the pointwise isotropic tensor
`Cε = λ tr ε I + 2μ ε` has exactly these properties. Discrete spaces are conforming
finite-dimensional subspaces `Sₕ ⊆ S₀`, `Uₕ ⊆ U`, `Xₕ ⊆ X` with `div Sₕ ⊆ Uₕ`
(`DiscreteFamily`), as for Falk's element. Sobolev norms `‖·‖_s`, `|·|_s` are abstract
nonnegative functions (`SobolevNorms`) that only appear in regularity hypotheses.

## Limits

- **Concrete triangulations, `BDMₖ` / Falk spaces, polynomial spaces** (Section 3.2) are
  not modelled; the discrete spaces are abstract subspaces, and their properties
  (inf-sup, Fortin operator, interpolation estimates (34), (35), (58), inverse
  estimates, Poincaré on `Ũₕ`, Scott–Zhang interpolation, the jump estimate (67)) are
  hypotheses.
- **Sobolev spaces on domains, traces, `H(div)`** are not available in Mathlib
  (Mathlib has Lax–Milgram, the spectral theorem for compact self-adjoint operators,
  and Sobolev spaces on `ℝⁿ` via Bessel potentials / distributions, but no bounded
  domains, traces, `H(div)`, finite elements, triangulations or Brezzi's splitting
  theorem). Hence Proposition 2.1, Lemma 2.2, Theorem 3.2, the BDM interpolation of
  Section 3.2 and the duality arguments of Section 4.2 are out of reach at this level,
  and the `H(div)`-norm is modelled as `‖τ‖ + ‖div τ‖`.
- **Element-wise quantities** `Σ_T h_T² ‖·‖²_T` and `Σ_E h_E⁻¹ ‖[·]‖²_E` of Chapter 6 are
  replaced by `h² ‖·‖²` (uniform mesh, p. 8) and by an abstract jump seminorm.
- **Chapter 7** (numerical experiments) has no formal counterpart.
- The existence and uniqueness of the postprocessing (52) (pp. 37–38) and of the
  continuous problems (Chapter 2) are not formalized; solutions are part of the data.

## Errata

Found while formalizing; none affects the results of the thesis.

1. **Proof of Lemma 5.6, p. 41.** The first display ends with `+ (γ, σₕ)`; the correct
   term is `+ 2(γ, σₕ)` (as in the proof of Lemma 4.9, p. 30). The next line and the
   identity (60) are correct: `postprocessed_eigenvalue_identity` proves (60) exactly as
   stated.
2. **Theorem 4.10, p. 30.** The proof via Lemma 4.9 and Theorem 4.8 gives
   `|κ - κₕ| ≤ C h^{2k} (‖σ‖_k + ‖u‖_k + ‖γ‖_k)²`; the thesis states the right-hand
   side without the square. The order `h^{2k}` is unaffected. `eigenvalue_rate` states
   the squared form.
3. **Theorem 5.7, p. 43.** Likewise the proof via Lemma 5.6 gives
   `|κ - κ*ₕ| ≤ C h^{2k+2} (|u|_{k+2} + |σ|_{k+1} + |γ|_{k+1})²`.
   `postprocessed_eigenvalue_rate` states the squared form.
4. **Theorem 3.1, p. 16**, quotes [5, Theorem 3.1] with `L²` norms on both sides. In the
   abstract setting this needs an `L²`-quasi-optimal Fortin operator (available for
   Falk's element by Section 3 and Lee [21]); `CeaHypotheses` makes this explicit.
5. **Theorem 4.7, p. 28**, lists approximability of `U⁰` only; the third component
   `‖Tf − Tₕf‖₀` also needs strong approximability of `X⁰` (`BoffiHypotheses.strongX`),
   which holds for Falk's element by the same argument.

## Rights

The thesis PDF is © Malte Petersen. No license has been granted for it.
