import MixedElasticEigenvalues.Statements.PostprocessedEigenvalue

/-!
# From Theorems 4.8, 4.10 and 5.1 to Theorem 5.7 (roadmap step 2)

The input `PostprocessedEigenvalueRates` of Theorem 5.7 consists of three rates. This file
derives all of them from the input of the earlier theorems, as on p. 43 of the thesis:

* the rate for `‖u - u*ₕ‖₀` is the conclusion of Theorem 5.1
  (`postprocessed_eigenfunction_rate`);
* the rate for `‖σ - σₕ‖₀ + ‖γ - γₕ‖₀` is part of the input of Theorem 5.1;
* the rate for `‖div (σ - σₕ)‖₀ = ‖κu - κₕuₕ‖₀` follows from Theorem 4.8 (`rate_u` and the
  bound on `κₕ` in `EigenfunctionRates`) and Theorem 4.10 (`eigenvalue_rate`): this is
  `EigenpairFamily.div_rate`.

The only additional hypothesis is a comparison of the Sobolev norms of the exact eigenpair
of orders `k` and `k + 1`, `k + 2` (`hnorm` below), which holds with `Cn = 1` for the full
Sobolev norms `‖·‖_s`, since these are monotone in `s`.

The main result is `postprocessed_eigenvalue_rate_of_rates`: Theorem 5.7 under the
hypotheses of Theorems 4.10 and 5.1 alone.
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace

noncomputable section

variable {H U : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] {ι : Type*}
  {div : H →ₗ[ℝ] U} {X S₀ : Submodule ℝ H} {μ : ℝ}

/-- The second equation of (36) holds strongly, `div σ = -κ u`, because it is tested with
every `v ∈ U`. -/
theorem MixedEigenpair.div_eq {M : MaterialOperator X μ} (p : MixedEigenpair div X S₀ M) :
    div p.σ = -p.κ • p.u := by
  have h := p.eq₂ (div p.σ + p.κ • p.u)
  have h0 : ⟪div p.σ + p.κ • p.u, div p.σ + p.κ • p.u⟫_ℝ = 0 := by
    rw [inner_add_left, h, real_inner_smul_left]; ring
  rw [inner_self_eq_zero] at h0
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left h0

namespace EigenpairFamily

variable {D : DiscreteFamily div X S₀ ι} {M : MaterialOperator X μ} (E : EigenpairFamily D M)

/-- `div (σ - σₕ) = κₕ uₕ - κ u` (p. 43). -/
theorem div_sub_eq (i : ι) :
    div (E.p.σ - (E.q i).σₕ) = (E.q i).κₕ • (E.q i).uₕ - E.p.κ • E.p.u := by
  rw [map_sub, E.p.div_eq, (E.q i).eq₂, neg_smul, neg_smul, sub_neg_eq_add, neg_add_eq_sub]

/-- `‖div (σ - σₕ)‖₀ ≤ |κₕ| ‖u - uₕ‖₀ + |κ - κₕ|` for normalized eigenfunctions. -/
theorem norm_div_sub_le (i : ι) :
    ‖div (E.p.σ - (E.q i).σₕ)‖
      ≤ |(E.q i).κₕ| * ‖E.p.u - (E.q i).uₕ‖ + |E.p.κ - (E.q i).κₕ| := by
  have e : (E.q i).κₕ • (E.q i).uₕ - E.p.κ • E.p.u
      = ((E.q i).κₕ - E.p.κ) • E.p.u - (E.q i).κₕ • (E.p.u - (E.q i).uₕ) := by
    rw [sub_smul, smul_sub]; abel
  rw [E.div_sub_eq, e]
  calc _ ≤ ‖((E.q i).κₕ - E.p.κ) • E.p.u‖ + ‖(E.q i).κₕ • (E.p.u - (E.q i).uₕ)‖ :=
        norm_sub_le _ _
    _ = |(E.q i).κₕ - E.p.κ| + |(E.q i).κₕ| * ‖E.p.u - (E.q i).uₕ‖ := by
        rw [norm_smul, norm_smul, E.u_norm, Real.norm_eq_abs, Real.norm_eq_abs, mul_one]
    _ = _ := by rw [abs_sub_comm]; ring

/-- The rate `‖div (σ - σₕ)‖₀ ≤ C hᵏ (‖σ‖_k + ‖u‖_k + ‖γ‖_k)` from Theorem 4.8 and
Theorem 4.10 (p. 43). Where `hᵏ T ≤ 1` the eigenvalue error `C h^{2k} T²` of Theorem 4.10 is
at most `C hᵏ T`; elsewhere `|κ - κₕ| ≤ |κ| + K ≤ (|κ| + K) hᵏ T` by the bound on `κₕ`. -/
theorem div_rate (N : SobolevNorms H U) (k : ℕ) (R : EigenfunctionRates E N k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖div (E.p.σ - (E.q i).σₕ)‖
      ≤ C * D.h i ^ k * (N.hn k E.p.σ + N.un k E.p.u + N.hn k E.p.γ) := by
  obtain ⟨Cκ, hCκ, hκ⟩ := eigenvalue_rate E N k R
  have hC₁ := R.C₁_nonneg
  refine ⟨|R.K| * R.C₁ + (Cκ + |E.p.κ| + |R.K|), by positivity, fun i => ?_⟩
  obtain ⟨T, hT⟩ : ∃ T, T = N.hn k E.p.σ + N.un k E.p.u + N.hn k E.p.γ := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by
    rw [hT]
    have := N.hn_nonneg k E.p.σ
    have := N.un_nonneg k E.p.u
    have := N.hn_nonneg k E.p.γ
    linarith
  obtain ⟨a, ha⟩ : ∃ a, a = D.h i ^ k * T := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; exact mul_nonneg (pow_nonneg (D.h_pos i).le k) hT0
  rw [← hT]
  have hu : ‖E.p.u - (E.q i).uₕ‖ ≤ R.C₁ * a := by
    have h := R.rate_u i
    have e : N.un k E.p.u + N.hn k E.p.σ + N.hn k E.p.γ = T := by rw [hT]; ring
    rw [e] at h
    rw [ha, ← mul_assoc]
    exact h
  have hK : |(E.q i).κₕ| ≤ |R.K| := (R.κₕ_bound i).trans (le_abs_self _)
  have h1 : |(E.q i).κₕ| * ‖E.p.u - (E.q i).uₕ‖ ≤ |R.K| * (R.C₁ * a) :=
    mul_le_mul hK hu (norm_nonneg _) (abs_nonneg _)
  have h2 : |E.p.κ - (E.q i).κₕ| ≤ (Cκ + |E.p.κ| + |R.K|) * a := by
    rcases le_total a 1 with ha1 | ha1
    · have h := hκ i
      rw [← hT, pow_mul', show (D.h i ^ k) ^ 2 = D.h i ^ k * D.h i ^ k by ring] at h
      have e : Cκ * (D.h i ^ k * D.h i ^ k) * T ^ 2 = Cκ * a * a := by rw [ha]; ring
      rw [e] at h
      have : Cκ * a * a ≤ Cκ * a := by
        have := mul_nonneg hCκ.le ha0
        nlinarith
      nlinarith [abs_nonneg E.p.κ, abs_nonneg R.K]
    · have h : |E.p.κ - (E.q i).κₕ| ≤ |E.p.κ| + |R.K| := (abs_sub _ _).trans (by linarith)
      have := abs_nonneg E.p.κ
      have := abs_nonneg R.K
      nlinarith
  have e : (|R.K| * R.C₁ + (Cκ + |E.p.κ| + |R.K|)) * D.h i ^ k * T
      = |R.K| * (R.C₁ * a) + (Cκ + |E.p.κ| + |R.K|) * a := by rw [ha]; ring
  rw [e]
  linarith [E.norm_div_sub_le i]

end EigenpairFamily

section Chain

variable {D : DiscreteFamily div X S₀ ι} {M : MaterialOperator X μ} {E : EigenpairFamily D M}
  {PP : Postprocessing D M E} {N : SobolevNorms H U} {k : ℕ}

private theorem le_mul_mul_of_le_const {x c C a b : ℝ} (hx : x ≤ c * a * b) (hc : c ≤ C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : x ≤ C * a * b :=
  hx.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc ha) hb)

/-- The input of Theorem 5.7 from the input of Theorem 5.1 and a rate for
`‖div (σ - σₕ)‖₀`: the rate for `u*ₕ` is Theorem 5.1 itself, the rate for `σ, γ` is shared.
The constant is `C₃ = C(5.1) + C₂ + Cd`. -/
def PostprocessingRates.toPostprocessedEigenvalueRates (R : PostprocessingRates PP N k)
    (Cd : ℝ) (hCd : 0 ≤ Cd)
    (rate_div : ∀ i, ‖div (E.p.σ - (E.q i).σₕ)‖
      ≤ Cd * D.h i ^ k * (N.un (k + 2) E.p.u + N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ)) :
    PostprocessedEigenvalueRates PP N k where
  two_le_k := R.two_le_k
  C₃ := (postprocessed_eigenfunction_rate PP N k R).choose + R.C₂ + Cd
  C₃_nonneg := by
    have := (postprocessed_eigenfunction_rate PP N k R).choose_spec.1
    have := R.C₂_nonneg
    linarith
  rate_ustar i := by
    have h5 := (postprocessed_eigenfunction_rate PP N k R).choose_spec
    have := R.C₂_nonneg
    refine le_mul_mul_of_le_const (h5.2 i) (by linarith) (pow_nonneg (D.h_pos i).le _) ?_
    have := N.un_nonneg (k + 2) E.p.u
    have := N.hn_nonneg (k + 1) E.p.σ
    have := N.hn_nonneg (k + 1) E.p.γ
    linarith
  rate_σγ i := by
    have := (postprocessed_eigenfunction_rate PP N k R).choose_spec.1
    refine le_mul_mul_of_le_const (R.rate_σγ i) (by linarith) (pow_nonneg (D.h_pos i).le _) ?_
    have := N.hn_nonneg (k + 1) E.p.σ
    have := N.hn_nonneg (k + 1) E.p.γ
    linarith
  rate_div i := by
    have := (postprocessed_eigenfunction_rate PP N k R).choose_spec.1
    have := R.C₂_nonneg
    refine le_mul_mul_of_le_const (rate_div i) (by linarith) (pow_nonneg (D.h_pos i).le _) ?_
    have := N.un_nonneg (k + 2) E.p.u
    have := N.hn_nonneg (k + 1) E.p.σ
    have := N.hn_nonneg (k + 1) E.p.γ
    linarith

/-- **Theorem 5.7** (p. 43) from the input of Theorem 5.1 and a rate for
`‖div (σ - σₕ)‖₀`. -/
theorem postprocessed_eigenvalue_rate_of_postprocessingRates (R : PostprocessingRates PP N k)
    (Cd : ℝ) (hCd : 0 ≤ Cd)
    (rate_div : ∀ i, ‖div (E.p.σ - (E.q i).σₕ)‖
      ≤ Cd * D.h i ^ k * (N.un (k + 2) E.p.u + N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ)) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 < C ∧ ∀ i, D.h i ≤ h₀ →
      |E.p.κ - postprocessedEigenvalue div (E.q i).σₕ (PP.ustar i)|
        ≤ C * D.h i ^ (2 * k + 2)
          * (N.un (k + 2) E.p.u + N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ) ^ 2 :=
  postprocessed_eigenvalue_rate PP N k (R.toPostprocessedEigenvalueRates Cd hCd rate_div)

/-- **Theorem 5.7** (p. 43) under the hypotheses of Theorems 4.10 and 5.1 alone:
`|κ - κ*ₕ| ≤ C h^{2k+2} (|u|_{k+2} + |σ|_{k+1} + |γ|_{k+1})²` for `h ≤ h₀`. The rate for
`div (σ - σₕ)` is derived by `EigenpairFamily.div_rate`; `hnorm` compares the Sobolev norms
of orders `k` and `k + 1`, `k + 2` of the exact eigenpair (`Cn = 1` for full norms). -/
theorem postprocessed_eigenvalue_rate_of_rates (R : PostprocessingRates PP N k)
    (R' : EigenfunctionRates E N k) (Cn : ℝ) (hCn : 0 ≤ Cn)
    (hnorm : N.hn k E.p.σ + N.un k E.p.u + N.hn k E.p.γ
      ≤ Cn * (N.un (k + 2) E.p.u + N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ)) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 < C ∧ ∀ i, D.h i ≤ h₀ →
      |E.p.κ - postprocessedEigenvalue div (E.q i).σₕ (PP.ustar i)|
        ≤ C * D.h i ^ (2 * k + 2)
          * (N.un (k + 2) E.p.u + N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ) ^ 2 := by
  obtain ⟨Cd, hCd, hdiv⟩ := E.div_rate N k R'
  refine postprocessed_eigenvalue_rate_of_postprocessingRates R (Cd * Cn)
    (mul_nonneg hCd hCn) fun i => (hdiv i).trans ?_
  have hc : 0 ≤ Cd * D.h i ^ k := mul_nonneg hCd (pow_nonneg (D.h_pos i).le k)
  calc Cd * D.h i ^ k * (N.hn k E.p.σ + N.un k E.p.u + N.hn k E.p.γ)
      ≤ Cd * D.h i ^ k * (Cn * (N.un (k + 2) E.p.u + N.hn (k + 1) E.p.σ
          + N.hn (k + 1) E.p.γ)) := mul_le_mul_of_nonneg_left hnorm hc
    _ = _ := by ring

end Chain

end

end MixedElasticEigenvalues
