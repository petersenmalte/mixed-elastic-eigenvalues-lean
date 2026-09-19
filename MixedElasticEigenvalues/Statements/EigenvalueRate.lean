import MixedElasticEigenvalues.Statements.Framework

/-!
# Theorem 4.10: a priori estimate for the Falk finite element eigenvalue approximation

Statement of Theorem 4.10 (p. 30) in the abstract framework. Its input consists of a
normalized eigenpair, normalized discrete eigenpairs on every mesh (`EigenpairFamily`), and
a priori rates of order `k` for the three components of the eigenfunction
(`EigenfunctionRates`, the content of Theorem 4.8 transferred to the eigenvalue problem by
Theorem 4.7). The conclusion follows from Lemma 4.9 (`eigenvalue_identity`).

## Erratum

Theorem 4.10 of the thesis states the bound `C h^{2k} (‖σ‖_k + ‖u‖_k + ‖γ‖_k)`. Lemma 4.9
expresses `κ - κₕ` through *squares* of the eigenfunction errors, so the proof via Theorem
4.8 gives `C h^{2k} (‖σ‖_k + ‖u‖_k + ‖γ‖_k)²`; the convergence order `h^{2k}` is unaffected.
This squared form is what is stated (and proved) below.
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace
open Filter Topology

noncomputable section

variable {H U : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] {ι : Type*}
  {div : H →ₗ[ℝ] U} {X S₀ : Submodule ℝ H} {μ : ℝ}

/-- A normalized eigenpair `(κ, σ, u, γ)` of (36) together with normalized discrete
eigenpairs `(κₕ, σₕ, uₕ, γₕ)` of (37) on every mesh (normalization: p. 29). -/
structure EigenpairFamily (D : DiscreteFamily div X S₀ ι) (M : MaterialOperator X μ) where
  p : MixedEigenpair div X S₀ M
  u_norm : ‖p.u‖ = 1
  q : ∀ i, DiscreteMixedEigenpair div M (D.S i) (D.Uh i) (D.Xh i)
  uₕ_norm : ∀ i, ‖(q i).uₕ‖ = 1

/-- A priori rates of order `k` for the eigenfunction approximation (Theorem 4.8 / (40),
transferred to the eigenvalue problem), plus a uniform bound on the discrete eigenvalues
(they converge to `κ` by Proposition 4.3 and Theorem 4.7). -/
structure EigenfunctionRates {D : DiscreteFamily div X S₀ ι} {M : MaterialOperator X μ}
    (E : EigenpairFamily D M) (N : SobolevNorms H U) (k : ℕ) where
  C₁ : ℝ
  C₁_nonneg : 0 ≤ C₁
  rate_σγ : ∀ i, ‖E.p.σ - (E.q i).σₕ‖ + ‖E.p.γ - (E.q i).γₕ‖
    ≤ C₁ * D.h i ^ k * (N.hn k E.p.σ + N.hn k E.p.γ)
  rate_u : ∀ i, ‖E.p.u - (E.q i).uₕ‖
    ≤ C₁ * D.h i ^ k * (N.un k E.p.u + N.hn k E.p.σ + N.hn k E.p.γ)
  K : ℝ
  κₕ_bound : ∀ i, |(E.q i).κₕ| ≤ K

/-- **Theorem 4.10** (p. 30). Assume `u ∈ Hᵏ`, `σ ∈ Hᵏ`, `γ ∈ Hᵏ ∩ L²_skw`. Then
`|κ - κₕ| ≤ C h^{2k} (‖σ‖_k + ‖u‖_k + ‖γ‖_k)²` (squared form, see the erratum above). -/
theorem eigenvalue_rate {D : DiscreteFamily div X S₀ ι} {M : MaterialOperator X μ}
    (E : EigenpairFamily D M) (N : SobolevNorms H U) (k : ℕ) (R : EigenfunctionRates E N k) :
    ∃ C : ℝ, 0 < C ∧ ∀ i, |E.p.κ - (E.q i).κₕ|
      ≤ C * D.h i ^ (2 * k) * (N.hn k E.p.σ + N.un k E.p.u + N.hn k E.p.γ) ^ 2 := by
  -- Not proved here. By `eigenvalue_identity` (Lemma 4.9),
  -- `|κ - κₕ| ≤ ‖C‖ (‖C⁻¹‖ ‖σ - σₕ‖ + ‖γ - γₕ‖)² + 2|μ| ‖γ - γₕ‖² + K ‖u - uₕ‖²`,
  -- and the rates give the claim with `C = (‖C‖ (‖C⁻¹‖ + 1)² + 2|μ| + K) C₁² + 1`.
  sorry

/-- The hypotheses of Theorem 4.10 are satisfiable: the trivial eigenpairs with all
errors equal to zero. -/
example (μ : ℝ) : EigenpairFamily trivialFamily (trivialMaterial μ) where
  p := trivialEigenpair μ
  u_norm := by simp [trivialEigenpair]
  q := trivialDiscreteEigenpair μ
  uₕ_norm := fun _ => by simp [trivialDiscreteEigenpair]

example (μ : ℝ) (k : ℕ) (E : EigenpairFamily trivialFamily (trivialMaterial μ))
    (hp : E.p = trivialEigenpair μ) (hq : ∀ n, E.q n = trivialDiscreteEigenpair μ n) :
    EigenfunctionRates E trivialSobolev k where
  C₁ := 1
  C₁_nonneg := zero_le_one
  rate_σγ := fun i => by
    simp only [hp, hq, trivialEigenpair, trivialDiscreteEigenpair, sub_self, norm_zero,
      add_zero, trivialSobolev]
    have := trivialFamily.h_pos i
    positivity
  rate_u := fun i => by
    simp only [hp, hq, trivialEigenpair, trivialDiscreteEigenpair, sub_self, norm_zero,
      trivialSobolev]
    have := trivialFamily.h_pos i
    positivity
  K := 1
  κₕ_bound := fun i => by simp [hq, trivialDiscreteEigenpair]

end

end MixedElasticEigenvalues
