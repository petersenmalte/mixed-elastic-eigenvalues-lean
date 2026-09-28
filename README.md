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

Four layers, in increasing distance from the thesis's proofs:

1. **Material algebra** (`Material.lean`): pointwise linear algebra of `2×2` tensors,
   Chapter 2. Fully proved.
2. **Abstract eigenvalue identities** (`EigenvalueIdentities.lean`): Lemma 4.9 and
   Lemma 5.6 in an abstract real inner product space, with the variational equations
   (36), (37) and (53) as hypotheses. Fully proved. `IsotropicMaterial.lean` shows that the
   isotropic material law of layer 1 is an instance of the abstract `MaterialOperator`. Square roots `C^{±1/2}` of the
   material operator are avoided by working with the quadratic forms `⟪Cξ, ξ⟫`
   and `⟪C⁻¹τ, τ⟫` (definition (5)).
3. **Theorem statements** (`Statements/`): the main theorems of Chapters 3–6 as
   Lean statements over abstract families of discrete spaces, with every finite
   element property (stability, approximation, postprocessing, interpolation) as a
   typed hypothesis (`structure`), each with a trivial model showing the hypotheses are
   satisfiable. Theorems 3.1, 4.7, 4.10, 5.1, 5.7, 6.2 and 6.4 are proved under these
   hypotheses. No project theorem contains an unfinished proof. Realizing the hypotheses
   for concrete finite elements remains open; see **Limits** and `ROADMAP.md`.
4. **The continuous problem** (`Continuous/`): Proposition 2.1, Lemma 2.2, the
   continuous inf-sup condition (13) and the coercivity (16) uniformly in `λ`, on
   abstract `L²` spaces. The trace and deviator on `L²(Ω; ℝ²ˣ²)` are a
   `TraceStructure` (two identities, from which the estimates of p. 13 follow), realized
   on the actual Lebesgue spaces `MeasureTheory.Lp` together with `L²₀(Ω)`; the
   analytic input — Green's formula for `H¹₀`, a bounded right inverse of
   `div : H¹₀ → L²₀` (Bogovskiĭ), and the two stress liftings of [5] — is a typed
   hypothesis, and the proofs from it are complete.

## Status at a glance

| | meaning |
|---|---|
| ✅ | **Proved.** Complete Lean proof, checked by the axiom audit, resting on no unproved project hypothesis. |
| 🟡 | **Proved conditionally.** Complete, machine-checked Lean proof — but from a typed hypothesis structure whose fields are *not* proved here (Sobolev/`H(div)` facts, or finite element properties). The implication is verified, the premises are not. |
| ❌ | **Not formalized.** |

A 🟡 result is as rigorous as its hypotheses: the Lean proof contains no gap, but it
assumes standard analysis or finite element theory that Mathlib does not have yet. The
last column names what is assumed. Realizing those hypotheses is steps 6–7 of
`ROADMAP.md`.

### Chapter 2 — Notations and preliminaries

| | Result | Assumed |
|---|---|---|
| ✅ | Material law (3), (4), (6), identities (12); pointwise `2×2` algebra | — |
| ✅ | Isotropic law is an abstract `MaterialOperator` (`IsotropicMaterial.lean`) | — |
| ✅ | Trace, deviator and `L²₀(Ω)` on the Lebesgue spaces `MeasureTheory.Lp` | — |
| ✅ | `‖dev τ‖₀ ≤ ‖τ‖₀`, `‖τ‖₀ ≥ ‖tr τ‖₀/√2` (p. 13) | — |
| 🟡 | **Proposition 2.1** (p. 13) | `InfSupData`: right inverse of `div`, skew lifting |
| 🟡 | inf-sup condition **(13)** | `InfSupData` |
| 🟡 | **Lemma 2.2**, dev–div inequality (p. 14) | `DevDivData`: Green's formula, Bogovskiĭ |
| 🟡 | coercivity **(16)**, uniformly in `λ` (p. 14) | via Lemma 2.2 |
| 🟡 | uniqueness for the source problem **(11)** | (16) and (13) |
| ❌ | existence for **(11)** (Brezzi's splitting theorem in `H(div)`) | — |

### Chapter 3 — Finite elements

| | Result | Assumed |
|---|---|---|
| 🟡 | **Theorem 3.1** (Céa): uniqueness, error estimate, existence | `CeaHypotheses`: (19), inf-sup (20), Fortin operator |
| ❌ | **Theorem 3.2** (Stokes well-posedness) | — |
| ❌ | **Theorem 3.3** (projection estimate, Bramble–Hilbert) | — |
| ❌ | **Proposition 3.4**, **Lemma 3.5** (BDM degrees of freedom, `Πₕ`, (33), (34)) | — |
| ❌ | Triangulations, `BDMₖ`, Falk's element, polynomial spaces (Section 3.2) | — |

### Chapter 4 — A priori error analysis

| | Result | Assumed |
|---|---|---|
| ❌ | Definitions 4.1–4.2, **Proposition 4.3** (gap, convergence of eigenvalue problems) | — |
| 🟡 | Definitions 4.4–4.6 (weak/strong approximability, Fortid) | stated as `BoffiHypotheses` fields |
| 🟡 | **Theorem 4.7** (uniform convergence of `R`, `S`, `T`) | `BoffiHypotheses`, Theorem 3.1 |
| ❌ | **Theorem 4.8** (a priori estimates for the source problem) | — |
| ✅ | **Lemma 4.9** (eigenvalue identity, p. 30) | — |
| 🟡 | **Theorem 4.10** (a priori eigenvalue error) | `EigenfunctionRates` (content of Thm 4.8) |
| ❌ | **Lemma 4.11**, **Lemma 4.14** (`‖Pₕu − uₕ‖₀`, duality) | — |

### Chapter 5 — Postprocessing

| | Result | Assumed |
|---|---|---|
| ✅ | `L²`-projections; `P*ₕ = Pₕ + P̃ₕ` **(51)** | — |
| 🟡 | Postprocessing **(52)**, **(53)**: existence and uniqueness | `PostprocessingSpaces`: `dim Ũₕ < ∞`, `∇` injective (Poincaré) |
| 🟡 | **Theorem 5.1** (postprocessed eigenfunction) | `PostprocessingRates`: (55), (57), (58), Poincaré, inverse estimate |
| ✅ | Definition 5.5 (`κ*ₕ` as Rayleigh quotient) | — |
| ✅ | **Lemma 5.6**, identity **(60)** (p. 41) | — |
| 🟡 | **Theorem 5.7** (postprocessed eigenvalue) | input derived from Thms 4.10 and 5.1 (`RateChain.lean`) |

### Chapter 6 — A posteriori error analysis

| | Result | Assumed |
|---|---|---|
| 🟡 | Primal mixed problem **(62)**, estimator `η` | `APosterioriData` |
| 🟡 | **Lemma 6.1** (residual estimate) | `APosterioriData`: stability, Scott–Zhang |
| 🟡 | **Theorem 6.2** (reliability) | `APosterioriData`, (67) |
| ❌ | **Theorem 6.3** (efficiency) | — |
| 🟡 | **Theorem 6.4** (postprocessed eigenvalue error `≲ η² + h.o.t.`) | Lemma 5.6, Theorem 6.2 |

### Chapter 7

| | Result | Assumed |
|---|---|---|
| ❌ | Numerical experiments — no formal counterpart | — |

**Summary.** Of the 21 numbered results of the thesis:

* ✅ **2 proved outright** — Lemmas 4.9 and 5.6. Chapter 2's unnumbered material algebra,
  the trace and deviator estimates of p. 13 and the projection identity (51) are proved
  outright as well.
* 🟡 **10 proved conditionally** — Proposition 2.1, Lemma 2.2, Theorems 3.1, 4.7, 4.10,
  5.1, 5.7, Lemma 6.1, Theorems 6.2 and 6.4.
* ❌ **9 not formalized** — Theorems 3.2, 3.3, Proposition 3.4, Lemma 3.5,
  Proposition 4.3, Theorem 4.8, Lemmas 4.11 and 4.14, Theorem 6.3.

No proof in the project contains a gap: `sorry` is rejected in every file and the axiom
audit covers every declaration of every mathematical module.

## Detailed status

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
| `IsotropicMaterial.lean`: `Tens2`, `skewSubspace`, `isotropicMaterial` | Frobenius inner product (p. 7), `X` (9), `C`, `C⁻¹` (3), (4) as a `MaterialOperator` | thesis | proved: `Mat2` with `σ : τ` is an inner product space, and `matC`/`matCinv` satisfy every field of `MaterialOperator` for `μ > 0`, `λ + μ > 0` |
| `isotropicMaterial_pos`, `isotropicMaterial_inner_Cinv`, `isotropicMaterial_Cinv_coercive`, `inner_sym_skew` | positive definiteness of `C`; `a(σ,τ)` via `dev`/`tr` and its coercivity, p. 13; `sym ⟂ skw`, p. 7 | thesis | proved |
| `EigenvalueIdentities.lean`: `MaterialOperator`, `MixedEigenpair`, `DiscreteMixedEigenpair` | (36), (37), p. 26 | thesis | definitions (hypotheses) |
| `energy_Cinv_add` | `‖C⁻¹e + d‖²_{C^{1/2}}` expansion, p. 30 | thesis | proved |
| `eigenvalue_identity`, `eigenvalue_identity_raw` | Lemma 4.9, p. 30 | thesis | proved |
| `postprocessedEigenvalue` | Definition 5.5, (59), p. 41 | thesis | definition |
| `postprocessed_eigenvalue_identity`, `postprocessed_eigenvalue_identity_raw` | Lemma 5.6, (60), pp. 41–42 | thesis | proved (see errata) |
| `DiscreteFamily.exists_h_le`, `eventually_h_lt`, `nonempty_index` | arbitrarily fine meshes exist (nontrivial refinement filter) | — | proved |
| `Statements/Framework.lean`: `DiscreteFamily`, `MixedSource`, `DiscreteMixedSource`, `IsKernel`, `IsDiscreteKernel`, `hdivNorm`, `SobolevNorms` | (11), (17), (18), pp. 6, 14 | thesis | definitions |
| `Statements/Cea.lean`: `CeaHypotheses` | Theorem 3.1 hypotheses, pp. 15–16 | [5, Thm 3.1], [9] | definitions; needs an `L²`-quasi-optimal Fortin operator as extra hypothesis |
| `CeaHypotheses.coercive_discrete`, `div_eq_zero_of_isDiscreteKernel` | coercivity on `ker(Bₕ + Cₕ)`, p. 15; `div Σₕ ⊆ Uₕ`, p. 28 | thesis | proved |
| `cea_unique` | uniqueness part of Theorem 3.1, p. 16 | thesis, [9] | proved from (19), (16) and (20) |
| `cea_quasi_optimal`, `cea_estimate` | estimate of Theorem 3.1, p. 16 | [5, Thm 3.1], [9] | proved (best-approximation form, and the `inf` form of the thesis) |
| `cea_existence` | existence part of Theorem 3.1, p. 16 | [9] | proved: the discrete system is an injective map to its dual, hence surjective by equality of finite dimensions |
| `Statements/DiscreteSolution.lean`: `CeaHypotheses.solve`, `σOp`, `uOp`, `γOp`, `DiscreteMixedSource.add`, `.smul` | discrete solution operators of (17), Theorem 3.1 | thesis | constructed from `cea_existence`; linear by `cea_unique` |
| `DiscreteMixedSource.div_eq`, `div_σOp` | `div σₕ = -f` for `f ∈ Uₕ` (`div Σₕ ⊆ Uₕ`, p. 28) | thesis | proved |
| `uOp_eigenpair`, `eigenpair_eq_ops`, `eigenpairOfEigenvector`, `DiscreteMixedEigenpair.toSource` | (37) is the eigenproblem `Tₕuₕ = κₕ⁻¹uₕ` of the discrete solution operator | thesis, [3] | proved (both directions) |
| `solve_estimate` | Theorem 3.1 for the constructed solutions | thesis | proved |
| `Statements/ContinuousSource.lean`: `SourceHypotheses`, `source_unique` | uniqueness for (11) from (16) and the continuous inf-sup condition, pp. 13–14 | thesis, [5] | proved; existence (Brezzi) is the hypothesis `exists_sol` |
| `SourceHypotheses.σOp`, `uOp`, `γOp`, `div_σOp`, `uOp_eigenpair`, `eigenpairOfEigenvector` | solution operator `T`; (36) is the eigenproblem `Tu = κ⁻¹u` | thesis, [3] | proved |
| `SourceHypotheses.op_error` | Theorem 3.1 as an estimate of `T f - Tₕ f` | thesis | proved |
| `Statements/Boffi.lean`: `BoffiHypotheses` | Def. 4.4–4.6, pp. 27–28 | [3] | definitions; strong approximability of `X⁰` added as hypothesis |
| `uniform_convergence` | Theorem 4.7, p. 28 | [3, Thm 14.6] | proved from `cea_estimate` plus approximability and regularity |
| `Statements/EigenvalueRate.lean`: `EigenfunctionRates`, `eigenvalue_rate` | Theorem 4.10, p. 30 | thesis | proved from Lemma 4.9 and the rate hypotheses (squared form, see errata) |
| `Statements/Postprocessing.lean`: `Postprocessing`, `PostprocessingRates` | (52), (53), pp. 37–38 | thesis, [18], [24] | definitions (hypotheses) |
| `proj_unique`, `proj_eq_self`, `proj_sub`, `pstar_eq`, `ph_ustar` | (50), (51), (52), p. 36 | thesis | proved |
| `postprocessed_eigenfunction_rate` | Theorem 5.1, pp. 38–40 | thesis, [18], [24] | proved from (51), (55), (57), (58), Poincaré and inverse estimates |
| `Statements/PostprocessingExistence.lean`: `exists_grad_galerkin`, `exists_postprocessed`, `postprocessed_unique` | existence and uniqueness of the postprocessing (52), p. 37 | thesis | proved (finite-dimensional Lax–Milgram on `Ũₕ`; `∇` injective on `Ũₕ` by Poincaré, `grad_inj_of_poincare`) |
| `PostprocessingSpaces.toPostprocessing`, `Postprocessing.ustar_unique`, `PostprocessingRates.ustar_unique` | `u*ₕ` constructed from the spaces (50)–(51); every `Postprocessing` uses the unique `u*ₕ` | thesis | proved |
| `Statements/PostprocessedEigenvalue.lean`: `PostprocessedEigenvalueRates`, `postprocessed_eigenvalue_rate` | Theorem 5.7, p. 43 | thesis | proved from Lemma 5.6, the rate hypotheses and a Rayleigh-quotient bound for `κ*ₕ`, for `h ≤ h₀` (squared form, see errata) |
| `Statements/RateChain.lean`: `MixedEigenpair.div_eq`, `EigenpairFamily.div_sub_eq`, `norm_div_sub_le` | `div σ = -κu`; `div(σ - σₕ) = κₕuₕ - κu`, p. 43 | thesis | proved |
| `EigenpairFamily.div_rate` | `‖div(σ - σₕ)‖₀ ≤ C hᵏ(…)` from Theorems 4.8 and 4.10, p. 43 | thesis | proved |
| `PostprocessingRates.toPostprocessedEigenvalueRates`, `postprocessed_eigenvalue_rate_of_rates` | Theorem 5.7 from the input of Theorems 4.10 and 5.1, p. 43 | thesis | proved (plus a comparison of the Sobolev norms of orders `k` and `k+1`, `k+2`) |
| `Statements/APosteriori.lean`: `APosterioriData`, `estimatorSq`, `estimator`, `Postprocessing.hot` | estimator `η`, (62), (67), pp. 44–48 | thesis, [11] | definitions |
| `APosterioriData.skw_sol_eq_zero`, `skw_sub_eq` | third equation of (62), p. 44 | thesis | proved |
| `APosterioriData.residual_bound` | central estimate of Lemma 6.1, p. 47 | thesis, [11], [23] | proved (Gauss, Scott–Zhang, (37), (52)) |
| `sq_estimator`, `res_le_estimator`, `vol_le_estimator`, `skw_le_estimator`, `jump_le_estimatorSq`, `grad_avg_le`, `avg_le` | components of `η²`, and (67), pp. 48, 50 | thesis, [20] | proved |
| `APosterioriData.reliability` | Theorem 6.2, p. 48 | thesis, [11] | proved from `stab`, `residual_bound`, `skw_sub_eq` and (67) |
| `APosterioriData.eigenvalue_reliability` | Theorem 6.4, p. 50 | thesis | proved from Lemma 5.6, Gauss, Young, Theorem 6.2 and (67); no additional bound on `κ*ₕ` |
| `Continuous/Trace.lean`: `TraceStructure`, `dev` | trace and deviator on `L²(Ω; ℝ²ˣ²)`, pp. 9–10 | thesis | definitions (two identities: (12) integrated, `tr I = 2`) |
| `tr_dev`, `dev_add`, `idm_tr`, `dev_idm`, `dev_dev`, `inner_dev_idm`, `norm_idm`, `norm_sq_eq` | (12) integrated, p. 13 | thesis | proved |
| `norm_dev_le`, `norm_tr_le` | `‖dev τ‖₀ ≤ ‖τ‖₀`, `‖τ‖₀ ≥ c ‖tr τ‖₀`, p. 13 | thesis | proved (`c = 1/√2`) |
| `Continuous/TraceL2.lean`: `TraceStructure.L2`, `matTrace`, `matTraceL2` | trace and deviator on the Lebesgue spaces `L²(Ω; ℝ²ˣ²)`, `L²(Ω)` | thesis | proved: a pointwise trace structure lifts to `MeasureTheory.Lp` by composition; the `2×2` structure is `tr σ = (I, σ)`, `q ↦ q I` |
| `meanZero`, `mem_meanZero_iff` | `L²₀(Ω)`, p. 14 | thesis | proved: the orthogonal complement of the constants is `{q : ∫ q = 0}` |
| `Continuous/DevDiv.lean`: `DevDivData` | analytic input of Lemma 2.2 | [5] | hypotheses: `H¹₀`, Green's formula, `L²₀`, Bogovskiĭ right inverse of `div` |
| `DevDivData.norm_tr_le`, `dev_div_estimate` | **Lemma 2.2**, p. 14 | [5, Prop. 1] | proved (for every `τ` with `∫ tr τ = 0`; no boundary condition needed) |
| `Continuous/InfSup.lean`: `InfSupData` | analytic input of Proposition 2.1 | [5], [4] | hypotheses: bounded right inverse of `div : Σ₀ → U`, skew lifting by divergence-free stresses |
| `infsup_lift`, `prop_2_1` | **Proposition 2.1**, p. 13 | [5, Prop. 2] | proved (with `Σ₀` for `Σ_g`, see errata) |
| `continuous_infsup` | inf-sup condition (13), p. 13 | [9], [5] | proved (see errata) |
| `Continuous/Coercivity.lean`: `IsIsotropicCinv`, `IsIsotropicCinv.inner_self`, `dev_le_inner`, `coercive_L2` | (4), reformulation of `a(σ,σ)` and `a(τ,τ) ≥ ‖τ‖₀²/(2(λ+μ))`, p. 13 | thesis | proved |
| `coercive_uniform`, `coercive_uniform_kernel` | coercivity (16) on `ker(B + C) ∩ L²₀`, uniformly in `λ`, p. 14 | thesis, [5] | proved from Lemma 2.2 (see errata) |
| Theorem 3.2, Proposition 3.4, Lemma 3.5, Remark 3.6, Theorem 3.3 | pp. 16–22 | [4], [7], [8], [10], [14] | not formalizable at this level (Sobolev spaces on domains, Stokes, BDM interpolation) |
| Theorem 4.8, Lemma 4.11, Lemma 4.14, Theorem 6.3 | pp. 29–34, 49 | thesis, [17] | not formalized (their content enters Stage 3 as rate hypotheses) |
| Lemma 6.1 | p. 47 | thesis, [11] | its central residual estimate is `residual_bound`; the stability and averaging argument is included in the proved Theorem 6.2 |
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
2. `scripts/check_no_sorry.sh`: rejects `sorry`, `admit`, `axiom` declarations and
   `native_decide` in every project Lean file, including newly added files;
3. the axiom audit `MixedElasticEigenvalues/Axioms.lean` (run during `lake build` and again by
   `scripts/check_axioms.sh`): recursive axiom checks for every non-internal declaration
   of all current mathematical modules, including `Cea` and `APosteriori`. The build
   fails if any axiom other than `propext`, `Classical.choice` and `Quot.sound` is used
   (in particular `sorryAx`). There are no exceptions for individual theorems.

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
  theorem). Proposition 2.1 and Lemma 2.2 are therefore proved from typed analytic
  hypotheses (Green's formula for `H¹₀`, Bogovskiĭ's right inverse of the divergence,
  the stress liftings of [5]), which are standard facts on bounded Lipschitz domains but
  are not themselves proved here. Theorem 3.2, the BDM interpolation of Section 3.2 and
  the duality arguments of Section 4.2 are out of reach at this level, and the
  `H(div)`-norm is modelled as `‖τ‖ + ‖div τ‖`.
- **Element-wise quantities** `Σ_T h_T² ‖·‖²_T` and `Σ_E h_E⁻¹ ‖[·]‖²_E` of Chapter 6 are
  replaced by `h² ‖·‖²` (uniform mesh, p. 8) and by an abstract jump seminorm.
- **Chapter 7** (numerical experiments) has no formal counterpart.
- The existence and uniqueness of the postprocessing (52) (pp. 37–38) are proved
  (`PostprocessingExistence.lean`). For the continuous source problem (11), uniqueness
  is proved from (16) and the continuous inf-sup condition (`source_unique`), but
  existence is the hypothesis `SourceHypotheses.exists_sol`: it is Brezzi's splitting
  theorem in `H(div)`, which needs the Hilbert space setting that is out of reach here.
  The eigenpairs of (36) and (37) are still part of the data.
- The a posteriori bounds retain higher-order terms involving the exact solution and
  eigenvalue. Their higher order or absorbability is not proved. In Theorem 6.4, the
  retained squared eigenvalue error bounds errors at least one; for smaller errors,
  `|κ*ₕ| ≤ |κ| + 1`. This proves the stated bound without an additional eigenvalue
  hypothesis, but does not give a computable error bound in terms of `η` alone.

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
6. **Proposition 2.1, p. 13**, asserts `τ ∈ Σ_g`. For `g ≠ 0` this contradicts the bound
   `‖τ‖_{H(div)} ≤ C (‖v‖₀ + ‖η‖₀)`, which forces `τ = 0 ∉ Σ_g` for `v = η = 0`. The
   correct space, as in [5, Proposition 2], is the test space `Σ₀`; `prop_2_1` uses it.
7. **The inf-sup condition (13), p. 13**, has `τ` outside the supremum. It should read
   `inf_{v, η} sup_{τ} (b(τ, v) + c(η, τ)) / (‖τ‖_{H(div)} (‖v‖₀ + ‖η‖₀)) ≥ β > 0`, the
   continuous analogue of (20); `continuous_infsup` proves this form.
8. **(16), p. 14**, reads `a(τ, τ) ≥ 1/(2μ) ‖dev τ‖₀ ≥ 1/(2μ) ‖τ‖₀`. The norms must be
   squared, and the last step uses Lemma 2.2, whose constant `C` is missing: correct is
   `a(τ, τ) ≥ 1/(2μ) ‖dev τ‖₀² ≥ 1/(2μC²) ‖τ‖₀²`. The conclusion (a coercivity constant
   independent of `λ`) is unaffected; `coercive_uniform` proves the corrected chain.

## Rights

The thesis PDF is © Malte Petersen. No license has been granted for it.
