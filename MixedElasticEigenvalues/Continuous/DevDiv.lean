import MixedElasticEigenvalues.Continuous.Trace

/-!
# Lemma 2.2: the dev–div inequality (p. 14, [5, Proposition 1])

`‖τ‖₀ ≤ C (‖dev τ‖₀ + ‖div τ‖₀)` for every `τ ∈ H(div; Ω; ℝ²ˣ²)` with `∫_Ω tr τ = 0`.

Sobolev spaces on domains are not available in Mathlib, so the lemma is formalized at the
same level as the rest of the project. `H = L²(Ω; ℝ²ˣ²)`, `U = L²(Ω; ℝ²)` and
`Q = L²(Ω)` are abstract real inner product spaces, the pointwise trace is a
`TraceStructure`, and the analytic input is collected in `DevDivData`:

* the space `V = H¹₀(Ω; ℝ²)` with the gradient `v ↦ ∇v`;
* Green's formula `(τ, ∇v)₀ = -(div τ, v)₀` for `v ∈ H¹₀` — there is no boundary term
  because `v` vanishes on `∂Ω`, which is why no boundary condition on `τ` is needed;
* the space `Q₀ = L²₀(Ω)` of mean-zero functions;
* a bounded right inverse of the divergence `H¹₀(Ω; ℝ²) → L²₀(Ω)` (Nečas' inequality,
  constructed e.g. by Bogovskiĭ's integral operator): every `q ∈ L²₀(Ω)` is
  `div v = tr ∇v` for some `v ∈ H¹₀` with `‖v‖₀ ≤ C_B ‖q‖₀` and `‖∇v‖₀ ≤ C_B ‖q‖₀`.

The proof from these ingredients is the classical one. With `q = tr τ` and `v` from the
Bogovskiĭ operator,
`‖q‖₀² = (q, tr ∇v)₀ = (q I, ∇v)₀ = 2 (τ - dev τ, ∇v)₀ = -2 (div τ, v)₀ - 2 (dev τ, ∇v)₀`,
so `‖tr τ‖₀ ≤ 2 C_B (‖dev τ‖₀ + ‖div τ‖₀)`, and `τ = dev τ + ½ tr τ I` gives the claim.

The thesis states the lemma for `τ ∈ Σ_g ∩ L²₀(Ω; ℝ²ˣ²)`; since the Bogovskiĭ field
vanishes on `∂Ω`, the proof needs no boundary condition, and the statement below holds
for every `τ` with `∫_Ω tr τ = 0`.
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace

noncomputable section

variable {H U Q : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/-- The analytic input of Lemma 2.2, see the module docstring: `H¹₀(Ω; ℝ²)` with the
gradient, Green's formula, `L²₀(Ω)`, and a bounded right inverse of the divergence
`H¹₀(Ω; ℝ²) → L²₀(Ω)` (Bogovskiĭ). The divergence of a vector field is the trace of its
gradient, `div v = tr ∇v`. -/
structure DevDivData (div : H →ₗ[ℝ] U) (T : TraceStructure H Q) where
  /-- `H¹₀(Ω; ℝ²)`. -/
  V : Submodule ℝ U
  /-- The gradient `v ↦ ∇v`. -/
  grad : U →ₗ[ℝ] H
  /-- Green's formula for test functions vanishing on `∂Ω`. -/
  green : ∀ τ : H, ∀ v ∈ V, ⟪τ, grad v⟫_ℝ = -⟪div τ, v⟫_ℝ
  /-- `L²₀(Ω)`, the functions with mean zero. -/
  Q₀ : Submodule ℝ Q
  /-- The constant of the right inverse of the divergence. -/
  CB : ℝ
  CB_nonneg : 0 ≤ CB
  /-- Bogovskiĭ: `div : H¹₀(Ω; ℝ²) → L²₀(Ω)` has a bounded right inverse. -/
  bogovskii : ∀ q ∈ Q₀, ∃ v ∈ V, T.tr (grad v) = q ∧ ‖v‖ ≤ CB * ‖q‖ ∧ ‖grad v‖ ≤ CB * ‖q‖

variable {div : H →ₗ[ℝ] U} {T : TraceStructure H Q}

/-- The trace part of Lemma 2.2: `‖tr τ‖₀ ≤ 2 C_B (‖dev τ‖₀ + ‖div τ‖₀)` whenever
`∫_Ω tr τ = 0`. -/
theorem DevDivData.norm_tr_le (B : DevDivData div T) {τ : H} (hτ : T.tr τ ∈ B.Q₀) :
    ‖T.tr τ‖ ≤ 2 * B.CB * (‖T.dev τ‖ + ‖div τ‖) := by
  have hCB := B.CB_nonneg
  obtain ⟨v, hv, hdiv, hv1, hv2⟩ := B.bogovskii _ hτ
  -- `‖tr τ‖² = (tr τ I, ∇v) = 2 (τ - dev τ, ∇v) = -2 (div τ, v) - 2 (dev τ, ∇v)`
  have key : ‖T.tr τ‖ ^ 2 = -2 * ⟪div τ, v⟫_ℝ - 2 * ⟪T.dev τ, B.grad v⟫_ℝ := by
    have h1 : ‖T.tr τ‖ ^ 2 = ⟪T.idm (T.tr τ), B.grad v⟫_ℝ := by
      rw [T.adj, hdiv, real_inner_self_eq_norm_sq]
    rw [h1, T.idm_tr, real_inner_smul_left, inner_sub_left, B.green τ v hv]
    ring
  have c1 : -⟪div τ, v⟫_ℝ ≤ ‖div τ‖ * ‖v‖ :=
    le_trans (neg_le_abs _) (abs_real_inner_le_norm _ _)
  have c2 : -⟪T.dev τ, B.grad v⟫_ℝ ≤ ‖T.dev τ‖ * ‖B.grad v‖ :=
    le_trans (neg_le_abs _) (abs_real_inner_le_norm _ _)
  have m1 : ‖div τ‖ * ‖v‖ ≤ ‖div τ‖ * (B.CB * ‖T.tr τ‖) :=
    mul_le_mul_of_nonneg_left hv1 (norm_nonneg _)
  have m2 : ‖T.dev τ‖ * ‖B.grad v‖ ≤ ‖T.dev τ‖ * (B.CB * ‖T.tr τ‖) :=
    mul_le_mul_of_nonneg_left hv2 (norm_nonneg _)
  have hsq : ‖T.tr τ‖ * ‖T.tr τ‖ ≤ (2 * B.CB * (‖T.dev τ‖ + ‖div τ‖)) * ‖T.tr τ‖ := by
    have : ‖T.tr τ‖ * ‖T.tr τ‖ = ‖T.tr τ‖ ^ 2 := by ring
    rw [this, key]
    linarith
  rcases eq_or_lt_of_le (norm_nonneg (T.tr τ)) with h0 | h0
  · rw [← h0]
    positivity
  · exact le_of_mul_le_mul_right hsq h0

/-- **Lemma 2.2** (p. 14, [5, Proposition 1]). There is a positive constant `C` such that
`‖τ‖₀ ≤ C (‖dev τ‖₀ + ‖div τ‖₀)` for every `τ` with `∫_Ω tr τ = 0`. -/
theorem dev_div_estimate (B : DevDivData div T) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : H, T.tr τ ∈ B.Q₀ → ‖τ‖ ≤ C * (‖T.dev τ‖ + ‖div τ‖) := by
  have hCB := B.CB_nonneg
  have hs : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  refine ⟨1 + B.CB * Real.sqrt 2, by positivity, fun τ hτ => ?_⟩
  have htr := B.norm_tr_le hτ
  -- `τ = dev τ + ½ tr τ I` and `‖½ tr τ I‖₀ = (√2 / 2) ‖tr τ‖₀`
  have hsplit : ‖τ‖ ≤ ‖T.dev τ‖ + 1 / 2 * (Real.sqrt 2 * ‖T.tr τ‖) := by
    calc ‖τ‖ = ‖T.dev τ + (1 / 2 : ℝ) • T.idm (T.tr τ)‖ := by rw [T.dev_add]
      _ ≤ ‖T.dev τ‖ + ‖(1 / 2 : ℝ) • T.idm (T.tr τ)‖ := norm_add_le _ _
      _ = ‖T.dev τ‖ + 1 / 2 * (Real.sqrt 2 * ‖T.tr τ‖) := by
          rw [norm_smul, T.norm_idm, Real.norm_eq_abs,
            abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hm := mul_le_mul_of_nonneg_left htr (by positivity : (0 : ℝ) ≤ 1 / 2 * Real.sqrt 2)
  have hdiv := norm_nonneg (div τ)
  have hdev := norm_nonneg (T.dev τ)
  have hp1 : (0 : ℝ) ≤ B.CB * Real.sqrt 2 * ‖div τ‖ := by positivity
  nlinarith [hsplit, hm]

/-! ### Consistency of the hypotheses

The trivial model: all spaces `ℝ`, `tr σ = idm σ = √2 σ` (so that `tr (q I) = 2 q`),
`div = grad = 0`, `H¹₀ = L²₀ = 0`. -/

/-- `tr = idm = √2 · id` on `ℝ` is a trace structure. -/
def trivialTrace : TraceStructure ℝ ℝ where
  tr := Real.sqrt 2 • LinearMap.id
  idm := Real.sqrt 2 • LinearMap.id
  adj := fun q σ => by simp; ring
  tr_idm := fun q => by
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_smul]
    rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The hypotheses of Lemma 2.2 are satisfiable. -/
example : DevDivData (0 : ℝ →ₗ[ℝ] ℝ) trivialTrace where
  V := ⊥
  grad := 0
  green := fun τ v hv => by simp [(Submodule.mem_bot ℝ).mp hv]
  Q₀ := ⊥
  CB := 0
  CB_nonneg := le_rfl
  bogovskii := fun q hq => ⟨0, Submodule.zero_mem _, by simp [(Submodule.mem_bot ℝ).mp hq]⟩

end

end MixedElasticEigenvalues
