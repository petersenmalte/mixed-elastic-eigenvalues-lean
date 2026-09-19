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
  -- By `eigenvalue_identity` (Lemma 4.9),
  -- `|κ - κₕ| ≤ ‖C‖ (‖C⁻¹‖ ‖σ - σₕ‖ + ‖γ - γₕ‖)² + 2|μ| ‖γ - γₕ‖² + K ‖u - uₕ‖²`,
  -- and the rates give the claim with `C = (‖C‖ (‖C⁻¹‖ + 1)² + 2|μ| + |K|) C₁² + 1`.
  refine ⟨(‖M.C‖ * (‖M.Cinv‖ + 1) ^ 2 + 2 * |μ| + |R.K|) * R.C₁ ^ 2 + 1, by positivity,
    fun i => ?_⟩
  have hid := eigenvalue_identity E.p (E.q i) (D.S_le i) (D.Xh_le i) E.u_norm (E.uₕ_norm i)
  have hσγ := R.rate_σγ i
  have hu := R.rate_u i
  have hκ := R.κₕ_bound i
  have hh := D.h_pos i
  have hC₁ := R.C₁_nonneg
  have hT1 := N.hn_nonneg k E.p.σ
  have hT2 := N.un_nonneg k E.p.u
  have hT3 := N.hn_nonneg k E.p.γ
  obtain ⟨T, hT⟩ : ∃ T, T = N.hn k E.p.σ + N.un k E.p.u + N.hn k E.p.γ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = R.C₁ * D.h i ^ k * T := ⟨_, rfl⟩
  rw [← hT]
  set e := E.p.σ - (E.q i).σₕ with he
  set d := E.p.γ - (E.q i).γₕ with hd
  set w := E.p.u - (E.q i).uₕ with hw
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hr : ‖e‖ + ‖d‖ ≤ B := by
    have h2 : 0 ≤ R.C₁ * D.h i ^ k := by positivity
    calc ‖e‖ + ‖d‖ ≤ R.C₁ * D.h i ^ k * (N.hn k E.p.σ + N.hn k E.p.γ) := hσγ
      _ ≤ R.C₁ * D.h i ^ k * T := by
        apply mul_le_mul_of_nonneg_left _ h2
        rw [hT]; linarith
      _ = B := hB.symm
  have hw1 : ‖w‖ ≤ B := by
    calc ‖w‖ ≤ R.C₁ * D.h i ^ k * (N.un k E.p.u + N.hn k E.p.σ + N.hn k E.p.γ) := hu
      _ = B := by rw [hB, hT]; ring
  have hE0 : 0 ≤ energy M.C (M.Cinv e + d) := M.nonneg _
  have hE1 : energy M.C (M.Cinv e + d) ≤ ‖M.C‖ * ‖M.Cinv e + d‖ ^ 2 := by
    unfold energy
    calc ⟪M.C (M.Cinv e + d), M.Cinv e + d⟫_ℝ
        ≤ ‖M.C (M.Cinv e + d)‖ * ‖M.Cinv e + d‖ := real_inner_le_norm _ _
      _ ≤ (‖M.C‖ * ‖M.Cinv e + d‖) * ‖M.Cinv e + d‖ :=
          mul_le_mul_of_nonneg_right (M.C.le_opNorm _) (norm_nonneg _)
      _ = ‖M.C‖ * ‖M.Cinv e + d‖ ^ 2 := by ring
  have hξ : ‖M.Cinv e + d‖ ≤ (‖M.Cinv‖ + 1) * B := by
    calc ‖M.Cinv e + d‖ ≤ ‖M.Cinv e‖ + ‖d‖ := norm_add_le _ _
      _ ≤ ‖M.Cinv‖ * ‖e‖ + ‖d‖ := by have := M.Cinv.le_opNorm e; linarith
      _ ≤ (‖M.Cinv‖ + 1) * (‖e‖ + ‖d‖) := by
          nlinarith [norm_nonneg e, norm_nonneg d, norm_nonneg M.Cinv]
      _ ≤ (‖M.Cinv‖ + 1) * B := by
          apply mul_le_mul_of_nonneg_left hr; positivity
  have hE2 : energy M.C (M.Cinv e + d) ≤ ‖M.C‖ * ((‖M.Cinv‖ + 1) * B) ^ 2 :=
    hE1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hξ 2) (norm_nonneg _))
  have hd2 : ‖d‖ ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg e]) 2
  have hw2 : ‖w‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw1 2
  have hb : |2 * μ * ‖d‖ ^ 2| ≤ 2 * |μ| * B ^ 2 := by
    rw [abs_mul, abs_mul, abs_two, abs_of_nonneg (pow_nonneg (norm_nonneg d) 2)]
    exact mul_le_mul_of_nonneg_left hd2 (by positivity)
  have hc : |(E.q i).κₕ * ‖w‖ ^ 2| ≤ |R.K| * B ^ 2 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg w) 2)]
    exact mul_le_mul (hκ.trans (le_abs_self _)) hw2 (by positivity) (abs_nonneg _)
  have habs : |E.p.κ - (E.q i).κₕ|
      ≤ energy M.C (M.Cinv e + d) + 2 * |μ| * B ^ 2 + |R.K| * B ^ 2 := by
    rw [hid]
    calc |energy M.C (M.Cinv e + d) - 2 * μ * ‖d‖ ^ 2 - (E.q i).κₕ * ‖w‖ ^ 2|
        ≤ |energy M.C (M.Cinv e + d) - 2 * μ * ‖d‖ ^ 2| + |(E.q i).κₕ * ‖w‖ ^ 2| :=
          abs_sub _ _
      _ ≤ |energy M.C (M.Cinv e + d)| + |2 * μ * ‖d‖ ^ 2| + |(E.q i).κₕ * ‖w‖ ^ 2| := by
          linarith [abs_sub (energy M.C (M.Cinv e + d)) (2 * μ * ‖d‖ ^ 2)]
      _ ≤ _ := by rw [abs_of_nonneg hE0]; linarith
  have hB2 : B ^ 2 = R.C₁ ^ 2 * D.h i ^ (2 * k) * T ^ 2 := by rw [hB]; ring
  have hpos : 0 ≤ D.h i ^ (2 * k) * T ^ 2 := by positivity
  calc |E.p.κ - (E.q i).κₕ|
      ≤ energy M.C (M.Cinv e + d) + 2 * |μ| * B ^ 2 + |R.K| * B ^ 2 := habs
    _ ≤ ‖M.C‖ * ((‖M.Cinv‖ + 1) * B) ^ 2 + 2 * |μ| * B ^ 2 + |R.K| * B ^ 2 := by linarith
    _ = (‖M.C‖ * (‖M.Cinv‖ + 1) ^ 2 + 2 * |μ| + |R.K|) * B ^ 2 := by ring
    _ = (‖M.C‖ * (‖M.Cinv‖ + 1) ^ 2 + 2 * |μ| + |R.K|) * R.C₁ ^ 2
          * (D.h i ^ (2 * k) * T ^ 2) := by rw [hB2]; ring
    _ ≤ ((‖M.C‖ * (‖M.Cinv‖ + 1) ^ 2 + 2 * |μ| + |R.K|) * R.C₁ ^ 2 + 1) * D.h i ^ (2 * k)
          * T ^ 2 := by nlinarith [hpos]

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
