import MixedElasticEigenvalues.Continuous.DevDiv
import MixedElasticEigenvalues.Statements.Framework

/-!
# Coercivity of `a(·,·)`, uniformly in `λ` (pp. 13–14, (16))

With the isotropic inverse material law (4),
`C⁻¹σ = 1/(2μ) (σ - λ/(2(μ+λ)) tr σ I)`, the bilinear form `a(σ, τ) = (C⁻¹σ, τ)₀`
satisfies (p. 13) `a(σ, σ) = 1/(2μ) ‖dev σ‖₀² + 1/(4(λ+μ)) ‖tr σ‖₀²`. Hence

* `a(τ, τ) ≥ 1/(2(λ+μ)) ‖τ‖₀²` on all of `L²` (p. 13) — a constant that degenerates in
  the incompressible limit `λ → ∞`;
* `a(τ, τ) ≥ 1/(2μ) ‖dev τ‖₀²`, and with Lemma 2.2 (`dev_div_estimate`)
  `a(τ, τ) ≥ α ‖τ‖₀²` for divergence-free `τ` with `∫_Ω tr τ = 0`, where `α` depends
  on `μ` and the constant of Lemma 2.2 only — this is (16), the coercivity on
  `ker (B + C) ∩ L²₀(Ω; ℝ²ˣ²)` uniformly in `λ`.

## Erratum

(16) reads `a(τ, τ) ≥ (dev(C⁻¹τ), dev τ) = 1/(2μ) ‖dev τ‖₀ ≥ 1/(2μ) ‖τ‖₀`. The norms must be
squared, and the last step uses Lemma 2.2, whose constant `C` is missing: correct is
`a(τ, τ) ≥ 1/(2μ) ‖dev τ‖₀² ≥ 1/(2μC²) ‖τ‖₀²`. The conclusion — a coercivity constant
independent of `λ` — is unaffected; `coercive_uniform` proves the corrected chain.
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace

noncomputable section

variable {H U Q : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/-- `C⁻¹` is the isotropic inverse material law (4) on `L²(Ω; ℝ²ˣ²)`:
`C⁻¹σ = 1/(2μ) (σ - λ/(2(μ+λ)) tr σ I)`. -/
def IsIsotropicCinv (T : TraceStructure H Q) (lam mu : ℝ) (Cinv : H →ₗ[ℝ] H) : Prop :=
  ∀ σ, Cinv σ = (1 / (2 * mu)) • (σ - (lam / (2 * (mu + lam))) • T.idm (T.tr σ))

variable {T : TraceStructure H Q} {lam mu : ℝ} {Cinv : H →ₗ[ℝ] H}

/-- The reformulation of `a(σ, σ)` via deviator and trace (p. 13):
`(C⁻¹σ, σ)₀ = 1/(2μ) ‖dev σ‖₀² + 1/(4(λ+μ)) ‖tr σ‖₀²`. -/
theorem IsIsotropicCinv.inner_self (h : IsIsotropicCinv T lam mu Cinv) (hmu : mu ≠ 0)
    (hlm : mu + lam ≠ 0) (σ : H) :
    ⟪Cinv σ, σ⟫_ℝ = 1 / (2 * mu) * ‖T.dev σ‖ ^ 2 + 1 / (4 * (mu + lam)) * ‖T.tr σ‖ ^ 2 := by
  rw [h σ, real_inner_smul_left, inner_sub_left, real_inner_smul_left, T.adj,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, T.norm_sq_eq σ]
  field_simp
  ring

/-- `a(σ, σ) ≥ 1/(2μ) ‖dev σ‖₀²` for `μ > 0`, `λ + μ > 0`. -/
theorem IsIsotropicCinv.dev_le_inner (h : IsIsotropicCinv T lam mu Cinv) (hmu : 0 < mu)
    (hlm : 0 < mu + lam) (σ : H) :
    1 / (2 * mu) * ‖T.dev σ‖ ^ 2 ≤ ⟪Cinv σ, σ⟫_ℝ := by
  rw [h.inner_self hmu.ne' hlm.ne' σ]
  have : (0 : ℝ) ≤ 1 / (4 * (mu + lam)) * ‖T.tr σ‖ ^ 2 := by positivity
  linarith

/-- Coercivity on all of `L²` with a `λ`-dependent constant (p. 13):
`a(τ, τ) ≥ 1/(2(λ+μ)) ‖τ‖₀²` for `λ ≥ 0`. The constant tends to `0` as `λ → ∞`. -/
theorem IsIsotropicCinv.coercive_L2 (h : IsIsotropicCinv T lam mu Cinv) (hmu : 0 < mu)
    (hlam : 0 ≤ lam) (σ : H) :
    1 / (2 * (lam + mu)) * ‖σ‖ ^ 2 ≤ ⟪Cinv σ, σ⟫_ℝ := by
  have hlm : 0 < mu + lam := by linarith
  have hlm' : 0 < lam + mu := by linarith
  rw [h.inner_self hmu.ne' hlm.ne' σ, T.norm_sq_eq σ]
  have h1 : 1 / (2 * (lam + mu)) ≤ 1 / (2 * mu) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have e : 1 / (2 * (lam + mu)) * (‖T.dev σ‖ ^ 2 + 1 / 2 * ‖T.tr σ‖ ^ 2)
      = 1 / (2 * (lam + mu)) * ‖T.dev σ‖ ^ 2 + 1 / (4 * (mu + lam)) * ‖T.tr σ‖ ^ 2 := by
    field_simp
    ring
  rw [e]
  linarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖T.dev σ‖)]

/-- **Coercivity (16)** (p. 14), uniformly in `λ`: there is `α > 0`, depending only on
`μ` and the constant of Lemma 2.2, such that `a(τ, τ) ≥ α ‖τ‖₀²` for every `λ > -μ` and
every divergence-free `τ` with `∫_Ω tr τ = 0`. The order of the quantifiers —
`∃ α` before `∀ λ` — is the uniformity in the incompressible limit. -/
theorem coercive_uniform {div : H →ₗ[ℝ] U} (B : DevDivData div T) (hmu : 0 < mu) :
    ∃ α : ℝ, 0 < α ∧ ∀ lam : ℝ, 0 < mu + lam → ∀ Cinv : H →ₗ[ℝ] H,
      IsIsotropicCinv T lam mu Cinv → ∀ τ : H, div τ = 0 → T.tr τ ∈ B.Q₀ →
        α * ‖τ‖ ^ 2 ≤ ⟪Cinv τ, τ⟫_ℝ := by
  obtain ⟨C, hC, hdd⟩ := dev_div_estimate B
  refine ⟨1 / (2 * mu * C ^ 2), by positivity, fun lam hlm Cinv h τ hdiv htr => ?_⟩
  have h1 := hdd τ htr
  rw [hdiv, norm_zero, add_zero] at h1
  have h2 : ‖τ‖ ^ 2 ≤ C ^ 2 * ‖T.dev τ‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg τ) h1 2
    rwa [mul_pow] at this
  have hC0 := hC.ne'
  have hmu0 := hmu.ne'
  calc 1 / (2 * mu * C ^ 2) * ‖τ‖ ^ 2
      ≤ 1 / (2 * mu * C ^ 2) * (C ^ 2 * ‖T.dev τ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 / (2 * mu) * ‖T.dev τ‖ ^ 2 := by
        field_simp
    _ ≤ ⟪Cinv τ, τ⟫_ℝ := h.dev_le_inner hmu hlm τ

/-- (16) on `ker (B + C) ∩ L²₀(Ω; ℝ²ˣ²)` (p. 14): elements of the kernel of (11) are
divergence free, so `coercive_uniform` applies to them. -/
theorem coercive_uniform_kernel {div : H →ₗ[ℝ] U} (B : DevDivData div T) (hmu : 0 < mu)
    (X S₀ : Submodule ℝ H) :
    ∃ α : ℝ, 0 < α ∧ ∀ lam : ℝ, 0 < mu + lam → ∀ Cinv : H →ₗ[ℝ] H,
      IsIsotropicCinv T lam mu Cinv → ∀ τ : H, IsKernel div X S₀ τ → T.tr τ ∈ B.Q₀ →
        α * ‖τ‖ ^ 2 ≤ ⟪Cinv τ, τ⟫_ℝ := by
  obtain ⟨α, hα, h⟩ := coercive_uniform B hmu
  refine ⟨α, hα, fun lam hlm Cinv hC τ hker htr => h lam hlm Cinv hC τ ?_ htr⟩
  exact inner_self_eq_zero.mp (hker.2.1 (div τ))

end

end MixedElasticEigenvalues
