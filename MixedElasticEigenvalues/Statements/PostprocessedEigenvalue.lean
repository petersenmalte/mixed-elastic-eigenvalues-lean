import MixedElasticEigenvalues.Statements.Postprocessing

/-!
# Theorem 5.7: the postprocessed eigenvalue

Statement of Theorem 5.7 (p. 43) in the abstract framework. `PostprocessedEigenvalueRates`
collects its input: the conclusion of Theorem 5.1, the rates of Theorem 4.8 and the rate
for `‖div(σ - σₕ)‖₀`.

## Erratum

As for Theorem 4.10, the proof of Theorem 5.7 via Lemma 5.6 bounds `|κ - κ*ₕ|` by
products of two eigenfunction errors, hence by `C h^{2k+2} (|u|_{k+2} + |σ|_{k+1} +
|γ|_{k+1})²`; the thesis states the right-hand side without the square. The order
`h^{2k+2}` is unaffected. The squared form is stated below.
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace
open Filter Topology

noncomputable section

variable {H U : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] {ι : Type*}
  {div : H →ₗ[ℝ] U} {X S₀ : Submodule ℝ H} {μ : ℝ}

/-- Input of Theorem 5.7 (p. 43): the conclusion of Theorem 5.1, the rates of Theorem 4.8
for `σ, γ`, and the rate `‖div(σ - σₕ)‖₀ = ‖κu - κₕuₕ‖₀ ≤ C h^k (…)` following from
Theorems 4.8 and 4.10. -/
structure PostprocessedEigenvalueRates {D : DiscreteFamily div X S₀ ι}
    {M : MaterialOperator X μ} {E : EigenpairFamily D M} (PP : Postprocessing D M E)
    (N : SobolevNorms H U) (k : ℕ) where
  two_le_k : 2 ≤ k
  C₃ : ℝ
  C₃_nonneg : 0 ≤ C₃
  rate_ustar : ∀ i, ‖E.p.u - PP.ustar i‖
    ≤ C₃ * D.h i ^ (k + 2) * (N.un (k + 2) E.p.u + N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ)
  rate_σγ : ∀ i, ‖E.p.σ - (E.q i).σₕ‖ + ‖E.p.γ - (E.q i).γₕ‖
    ≤ C₃ * D.h i ^ (k + 1) * (N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ)
  rate_div : ∀ i, ‖div (E.p.σ - (E.q i).σₕ)‖
    ≤ C₃ * D.h i ^ k * (N.un (k + 2) E.p.u + N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ)

/-- **Theorem 5.7** (p. 43). For `k ≥ 2` and sufficiently small `h`, the postprocessed
eigenvalue `κ*ₕ` of Definition 5.5 satisfies
`|κ - κ*ₕ| ≤ C h^{2k+2} (|u|_{k+2} + |σ|_{k+1} + |γ|_{k+1})²` (squared form, see the
erratum above). -/
theorem postprocessed_eigenvalue_rate {D : DiscreteFamily div X S₀ ι}
    {M : MaterialOperator X μ} {E : EigenpairFamily D M} (PP : Postprocessing D M E)
    (N : SobolevNorms H U) (k : ℕ) (R : PostprocessedEigenvalueRates PP N k) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 < C ∧ ∀ i, D.h i ≤ h₀ →
      |E.p.κ - postprocessedEigenvalue div (E.q i).σₕ (PP.ustar i)|
        ≤ C * D.h i ^ (2 * k + 2)
          * (N.un (k + 2) E.p.u + N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ) ^ 2 := by
  -- Not proved here. By Lemma 5.6 (`postprocessed_eigenvalue_identity`, applicable since
  -- `div σₕ ∈ Uₕ` and `u*ₕ ≠ 0` for small `h` by `rate_ustar` and `‖u‖ = 1`) and
  -- Cauchy–Schwarz,
  -- `|κ - κ*ₕ| ≤ C (‖σ - σₕ‖² + ‖γ - γₕ‖² + |κ*ₕ| ‖u - u*ₕ‖² + ‖div(σ - σₕ)‖ ‖u - u*ₕ‖
  --   + 2 |κ - κ*ₕ| ‖u - u*ₕ‖)`;
  -- `|κ*ₕ|` is bounded through the Rayleigh quotient, the last term is absorbed for
  -- `h ≤ h₀` (where `‖u - u*ₕ‖ ≤ 1/4`), and the rates give the order `h^{2k+2}`.
  sorry

/-- The hypotheses of Theorem 5.7 are satisfiable in the trivial model. -/
example (μ : ℝ) (k : ℕ) (hk : 2 ≤ k) (E : EigenpairFamily trivialFamily (trivialMaterial μ))
    (hp : E.p = trivialEigenpair μ) (hq : ∀ n, E.q n = trivialDiscreteEigenpair μ n) :
    PostprocessedEigenvalueRates (trivialPostprocessing μ E hq) trivialSobolev k where
  two_le_k := hk
  C₃ := 1
  C₃_nonneg := zero_le_one
  rate_ustar := fun n => by
    simp only [hp, trivialEigenpair, trivialPostprocessing, sub_self, norm_zero, trivialSobolev]
    have := trivialFamily.h_pos n
    positivity
  rate_σγ := fun n => by
    simp only [hp, hq, trivialEigenpair, trivialDiscreteEigenpair, sub_self, norm_zero,
      add_zero, trivialSobolev]
    have := trivialFamily.h_pos n
    positivity
  rate_div := fun n => by
    simp only [hp, hq, trivialEigenpair, trivialDiscreteEigenpair, sub_self, map_zero,
      norm_zero, trivialSobolev]
    have := trivialFamily.h_pos n
    positivity

end

end MixedElasticEigenvalues
