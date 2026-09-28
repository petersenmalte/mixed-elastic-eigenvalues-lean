import Mathlib

/-!
# Trace and deviator on `L²(Ω; ℝ²ˣ²)` (Chapter 2, pp. 9–14)

`Material.lean` treats the trace, the identity and the deviator pointwise, for a single
`2×2` matrix. The estimates of Chapter 2 (p. 13: `‖dev τ‖₀ ≤ ‖τ‖₀`, `‖τ‖₀ ≥ c ‖tr τ‖₀`,
and Lemma 2.2) are statements about the *integrated* quantities on `L²(Ω; ℝ²ˣ²)`.

Here `H` stands for `L²(Ω; ℝ²ˣ²)` and `Q` for `L²(Ω)`; both are abstract real inner
product spaces. A `TraceStructure` consists of the pointwise trace `tr : H → Q` and its
adjoint `q ↦ q I : Q → H`, characterized by

* `(q I, σ)₀ = (q, tr σ)₀` — identity (12) `σ : tr τ I = tr σ tr τ` integrated over `Ω`;
* `tr (q I) = 2 q` — `tr I = n = 2` (p. 9).

Everything else about trace and deviator on `L²` follows from these two identities:
`dev σ = σ - ½ tr σ I` is trace free, the deviatoric and spherical parts are
`L²`-orthogonal, `‖σ‖₀² = ‖dev σ‖₀² + ½ ‖tr σ‖₀²`, and hence the two estimates of p. 13.
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace

noncomputable section

/-- The pointwise trace `tr : L²(Ω; ℝ²ˣ²) → L²(Ω)` and its adjoint `q ↦ q I`, see the
module docstring. -/
structure TraceStructure (H Q : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] where
  /-- The trace `σ ↦ tr σ`. -/
  tr : H →ₗ[ℝ] Q
  /-- The spherical tensors `q ↦ q I`. -/
  idm : Q →ₗ[ℝ] H
  /-- `(q I, σ)₀ = (q, tr σ)₀`, identity (12) integrated over `Ω`. -/
  adj : ∀ q σ, ⟪idm q, σ⟫_ℝ = ⟪q, tr σ⟫_ℝ
  /-- `tr (q I) = 2 q`, since `tr I = 2`. -/
  tr_idm : ∀ q, tr (idm q) = (2 : ℝ) • q

namespace TraceStructure

variable {H Q : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] (T : TraceStructure H Q)

/-- The deviator `dev σ = σ - ½ tr σ I` (p. 10). -/
def dev (σ : H) : H := σ - (1 / 2 : ℝ) • T.idm (T.tr σ)

theorem dev_def (σ : H) : T.dev σ = σ - (1 / 2 : ℝ) • T.idm (T.tr σ) := rfl

/-- The deviator is trace free (p. 10). -/
theorem tr_dev (σ : H) : T.tr (T.dev σ) = 0 := by
  rw [dev_def, map_sub, map_smul, T.tr_idm, smul_smul]
  norm_num

/-- Splitting into deviatoric and spherical part, `σ = dev σ + ½ tr σ I`. -/
theorem dev_add (σ : H) : T.dev σ + (1 / 2 : ℝ) • T.idm (T.tr σ) = σ := by
  rw [dev_def, sub_add_cancel]

/-- `tr σ I = 2 (σ - dev σ)`. -/
theorem idm_tr (σ : H) : T.idm (T.tr σ) = (2 : ℝ) • (σ - T.dev σ) := by
  rw [dev_def, sub_sub_cancel, smul_smul]
  norm_num

/-- Spherical tensors have vanishing deviator. -/
theorem dev_idm (q : Q) : T.dev (T.idm q) = 0 := by
  rw [dev_def, T.tr_idm, map_smul, smul_smul]
  norm_num

/-- The deviator is idempotent. -/
theorem dev_dev (σ : H) : T.dev (T.dev σ) = T.dev σ := by
  rw [T.dev_def (T.dev σ), T.tr_dev, map_zero, smul_zero, sub_zero]

/-- `(q I, p I)₀ = 2 (q, p)₀`. -/
theorem inner_idm_idm (q p : Q) : ⟪T.idm q, T.idm p⟫_ℝ = 2 * ⟪q, p⟫_ℝ := by
  rw [T.adj, T.tr_idm, real_inner_smul_right]

/-- `‖q I‖₀² = 2 ‖q‖₀²`. -/
theorem norm_idm_sq (q : Q) : ‖T.idm q‖ ^ 2 = 2 * ‖q‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, T.inner_idm_idm, real_inner_self_eq_norm_sq]

/-- `‖q I‖₀ = √2 ‖q‖₀`. -/
theorem norm_idm (q : Q) : ‖T.idm q‖ = Real.sqrt 2 * ‖q‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (T.idm q)), T.norm_idm_sq, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (norm_nonneg q)]

/-- Deviatoric and spherical tensors are `L²`-orthogonal. -/
theorem inner_dev_idm (σ : H) (q : Q) : ⟪T.dev σ, T.idm q⟫_ℝ = 0 := by
  rw [real_inner_comm, T.adj, T.tr_dev, inner_zero_right]

/-- The orthogonal splitting `‖σ‖₀² = ‖dev σ‖₀² + ½ ‖tr σ‖₀²`, the integrated form of (12). -/
theorem norm_sq_eq (σ : H) : ‖σ‖ ^ 2 = ‖T.dev σ‖ ^ 2 + (1 / 2) * ‖T.tr σ‖ ^ 2 := by
  have h := norm_add_sq_real (T.dev σ) ((1 / 2 : ℝ) • T.idm (T.tr σ))
  rw [T.dev_add, real_inner_smul_right, T.inner_dev_idm, norm_smul, mul_pow,
    T.norm_idm_sq, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
  rw [h]
  ring

/-- `‖dev σ‖₀ ≤ ‖σ‖₀` (p. 13). -/
theorem norm_dev_le (σ : H) : ‖T.dev σ‖ ≤ ‖σ‖ := by
  have h2 : ‖T.dev σ‖ ^ 2 ≤ ‖σ‖ ^ 2 := by
    rw [T.norm_sq_eq σ]
    linarith [sq_nonneg ‖T.tr σ‖]
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3

/-- `‖tr σ‖₀² ≤ 2 ‖σ‖₀²`. -/
theorem norm_tr_sq_le (σ : H) : ‖T.tr σ‖ ^ 2 ≤ 2 * ‖σ‖ ^ 2 := by
  rw [T.norm_sq_eq σ]
  linarith [sq_nonneg ‖T.dev σ‖]

/-- `‖tr σ‖₀ ≤ √2 ‖σ‖₀`, i.e. `‖σ‖₀ ≥ c ‖tr σ‖₀` with `c = 1/√2` (p. 13). -/
theorem norm_tr_le (σ : H) : ‖T.tr σ‖ ≤ Real.sqrt 2 * ‖σ‖ := by
  have h := Real.sqrt_le_sqrt (T.norm_tr_sq_le σ)
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_sq (norm_nonneg _)] at h

end TraceStructure

end

end MixedElasticEigenvalues
