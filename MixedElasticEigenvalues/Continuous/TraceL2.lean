import MixedElasticEigenvalues.Continuous.Trace

/-!
# The trace structure on the Lebesgue spaces `L²(Ω; ℝ²ˣ²)` and `L²(Ω)`

`TraceStructure` (`Trace.lean`) is realized on Mathlib's Lebesgue spaces
`Lp E 2 μ = L²(α, μ; E)` for every measure space `(α, μ)` — in particular on `L²(Ω)`
for the Lebesgue measure restricted to a domain `Ω ⊆ ℝ²`.

* `TraceStructure.L2`: a pointwise trace structure on finite-dimensional spaces `E`, `F`
  induces one on `L²(α, μ; E)` and `L²(α, μ; F)`, by composition (`compLpₗ`). Its two
  identities hold because they hold pointwise and the `L²` inner product is the integral
  of the pointwise one (`L2.inner_def`).
* `matTrace`: the pointwise structure on `2×2` matrices with the Frobenius inner
  product, `Mat2E = EuclideanSpace ℝ (Fin 2 × Fin 2)`: the trace is `σ ↦ (I, σ)`,
  the spherical tensors are `q ↦ q I`, and `(I, I) = tr I = 2`.
* `matTraceL2 μ`: the trace structure on `L²(α, μ; ℝ²ˣ²)` and `L²(α, μ)`.
* `meanZero μ`: the space `L²₀ = {q : ∫ q dμ = 0}` of mean-zero functions, as the
  orthogonal complement of the constants (for a finite measure).

Consequently the deviator, the orthogonal splitting `‖σ‖₀² = ‖dev σ‖₀² + ½ ‖tr σ‖₀²`
and the estimates of p. 13 (`TraceStructure.norm_dev_le`, `TraceStructure.norm_tr_le`)
hold on the actual space `L²(Ω; ℝ²ˣ²)`, and in Lemma 2.2 the spaces `H`, `Q`, the trace
and `L²₀` can be taken to be the actual Lebesgue spaces: only `H¹₀`, the divergence,
Green's formula and the Bogovskiĭ operator remain hypotheses (`DevDivData`).
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace
open MeasureTheory

noncomputable section

/-! ### Lifting a pointwise trace structure to `L²` -/

section Lift

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A pointwise trace structure on `E`, `F` induces one on `L²(α, μ; E)`, `L²(α, μ; F)`,
by applying `tr` and `q ↦ q I` pointwise. -/
def TraceStructure.L2 (T : TraceStructure E F) : TraceStructure (Lp E 2 μ) (Lp F 2 μ) where
  tr := (LinearMap.toContinuousLinearMap T.tr).compLpₗ (p := 2) (μ := μ)
  idm := (LinearMap.toContinuousLinearMap T.idm).compLpₗ (p := 2) (μ := μ)
  adj q σ := by
    simp only [ContinuousLinearMap.compLpₗ_apply]
    rw [L2.inner_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [ContinuousLinearMap.coeFn_compLp (LinearMap.toContinuousLinearMap T.idm) q,
      ContinuousLinearMap.coeFn_compLp (LinearMap.toContinuousLinearMap T.tr) σ] with a h1 h2
    rw [h1, h2]
    simpa using T.adj (q a) (σ a)
  tr_idm q := by
    simp only [ContinuousLinearMap.compLpₗ_apply]
    refine Lp.ext ?_
    filter_upwards [ContinuousLinearMap.coeFn_compLp (LinearMap.toContinuousLinearMap T.tr)
        ((LinearMap.toContinuousLinearMap T.idm).compLp q),
      ContinuousLinearMap.coeFn_compLp (LinearMap.toContinuousLinearMap T.idm) q,
      Lp.coeFn_smul (2 : ℝ) q] with a h1 h2 h3
    rw [h1, h2, h3]
    simpa using T.tr_idm (q a)

end Lift

/-! ### The pointwise structure on `2×2` matrices -/

/-- `2×2` matrices with the Frobenius inner product `σ : τ = ∑ᵢⱼ σᵢⱼ τᵢⱼ` (p. 7). -/
abbrev Mat2E := EuclideanSpace ℝ (Fin 2 × Fin 2)

/-- The identity matrix `I`. -/
def idMat : Mat2E := WithLp.toLp 2 (fun ij : Fin 2 × Fin 2 => if ij.1 = ij.2 then (1 : ℝ) else 0)

theorem idMat_apply (ij : Fin 2 × Fin 2) : idMat ij = if ij.1 = ij.2 then 1 else 0 := rfl

/-- `(I, σ) = σ₀₀ + σ₁₁ = tr σ`. -/
theorem inner_idMat (σ : Mat2E) : ⟪idMat, σ⟫_ℝ = σ (0, 0) + σ (1, 1) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, idMat_apply]

/-- `(I, I) = tr I = 2`. -/
theorem inner_idMat_self : ⟪idMat, idMat⟫_ℝ = 2 := by
  rw [inner_idMat, idMat_apply, idMat_apply]
  norm_num

/-- The trace structure of `2×2` matrices: `tr σ = (I, σ)` and `q ↦ q I`. -/
def matTrace : TraceStructure Mat2E ℝ where
  tr := innerₛₗ ℝ idMat
  idm := LinearMap.toSpanSingleton ℝ Mat2E idMat
  adj q σ := by
    simp only [innerₛₗ_apply_apply, LinearMap.toSpanSingleton_apply, real_inner_smul_left]
    simp [real_inner_comm]
    ring
  tr_idm q := by
    simp only [innerₛₗ_apply_apply, LinearMap.toSpanSingleton_apply, real_inner_smul_right,
      inner_idMat_self, smul_eq_mul]
    ring

/-- The trace of `matTrace` is `σ₀₀ + σ₁₁`. -/
theorem matTrace_tr (σ : Mat2E) : matTrace.tr σ = σ (0, 0) + σ (1, 1) := inner_idMat σ

/-! ### `L²(Ω; ℝ²ˣ²)` and `L²₀(Ω)` -/

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- The trace structure on `L²(α, μ; ℝ²ˣ²)` and `L²(α, μ)`, e.g. `α = Ω ⊆ ℝ²` with the
Lebesgue measure. -/
def matTraceL2 : TraceStructure (Lp Mat2E 2 μ) (Lp ℝ 2 μ) := matTrace.L2 μ

/-- The estimates of p. 13 hold on the actual space `L²(Ω; ℝ²ˣ²)`. -/
example (σ : Lp Mat2E 2 μ) :
    ‖(matTraceL2 μ).dev σ‖ ≤ ‖σ‖ ∧ ‖(matTraceL2 μ).tr σ‖ ≤ Real.sqrt 2 * ‖σ‖ :=
  ⟨(matTraceL2 μ).norm_dev_le σ, (matTraceL2 μ).norm_tr_le σ⟩

/-- `L²₀`: the functions with mean zero, as the orthogonal complement of the constants. -/
def meanZero [IsFiniteMeasure μ] : Submodule ℝ (Lp ℝ 2 μ) :=
  (ℝ ∙ indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ Set.univ) (1 : ℝ))ᗮ

theorem mem_meanZero_iff [IsFiniteMeasure μ] (q : Lp ℝ 2 μ) :
    q ∈ meanZero μ ↔ ∫ x, q x ∂μ = 0 := by
  rw [meanZero, Submodule.mem_orthogonal_singleton_iff_inner_right,
    L2.inner_indicatorConstLp_one, Measure.restrict_univ]

end

end MixedElasticEigenvalues
