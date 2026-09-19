import MixedElasticEigenvalues.Statements.Postprocessing

/-!
# Theorem 5.7: the postprocessed eigenvalue

Theorem 5.7 (p. 43) in the abstract framework, proved from Lemma 5.6
(`postprocessed_eigenvalue_identity`). `PostprocessedEigenvalueRates` collects its input:
the conclusion of Theorem 5.1, the rates of Theorem 4.8 and the rate for `‖div(σ - σₕ)‖₀`.

## Erratum

As for Theorem 4.10, the proof of Theorem 5.7 via Lemma 5.6 bounds `|κ - κ*ₕ|` by
products of two eigenfunction errors, hence by `C h^{2k+2} (|u|_{k+2} + |σ|_{k+1} +
|γ|_{k+1})²`; the thesis states the right-hand side without the square. The order
`h^{2k+2}` is unaffected. The squared form is stated and proved below.
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
  -- By Lemma 5.6 (`postprocessed_eigenvalue_identity`, applicable since `div σₕ ∈ Uₕ` and
  -- `u*ₕ ≠ 0` for `h ≤ h₀`, where `‖u - u*ₕ‖ ≤ 1/4`) and Cauchy–Schwarz,
  -- `|κ - κ*ₕ| ≤ energy + 2|μ| ‖γ - γₕ‖² + |κ*ₕ| ‖u - u*ₕ‖² + 2 ‖div(σ - σₕ)‖ ‖u - u*ₕ‖
  --   + 2 |κ - κ*ₕ| ‖u - u*ₕ‖`;
  -- `|κ*ₕ| ≤ 4/3 (|κ| + C₃ T)` through the Rayleigh quotient and `div σ = -κu`, the last
  -- term is absorbed, and the rates give the order `h^{2k+2}`.
  obtain ⟨T, hT⟩ : ∃ T, T = N.un (k + 2) E.p.u + N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ :=
    ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by
    rw [hT]
    have := N.un_nonneg (k + 2) E.p.u
    have := N.hn_nonneg (k + 1) E.p.σ
    have := N.hn_nonneg (k + 1) E.p.γ
    linarith
  have hC₃ := R.C₃_nonneg
  obtain ⟨Kst, hKst⟩ : ∃ Kst, Kst = 4 / 3 * (|E.p.κ| + R.C₃ * T) := ⟨_, rfl⟩
  have hKst0 : 0 ≤ Kst := by rw [hKst]; positivity
  refine ⟨min 1 (1 / (4 * (R.C₃ * T + 1))),
    2 * (‖M.C‖ * (‖M.Cinv‖ + 1) ^ 2 + 2 * |μ| + Kst + 2) * R.C₃ ^ 2 + 1,
    by positivity, by positivity, fun i hi => ?_⟩
  rw [← hT]
  have hh := D.h_pos i
  have hh1 : D.h i ≤ 1 := le_trans hi (min_le_left _ _)
  have hh2 : D.h i ≤ 1 / (4 * (R.C₃ * T + 1)) := le_trans hi (min_le_right _ _)
  have hr1 := R.rate_ustar i
  have hr2 := R.rate_σγ i
  have hr3 := R.rate_div i
  rw [← hT] at hr1 hr3
  set e := E.p.σ - (E.q i).σₕ with he
  set d := E.p.γ - (E.q i).γₕ with hd
  set uₛ := PP.ustar i with huₛ
  set w := E.p.u - uₛ with hw
  -- the three rate bounds
  obtain ⟨B1, hB1⟩ : ∃ B1, B1 = R.C₃ * D.h i ^ (k + 1) * T := ⟨_, rfl⟩
  obtain ⟨B2, hB2⟩ : ∃ B2, B2 = R.C₃ * D.h i ^ (k + 2) * T := ⟨_, rfl⟩
  obtain ⟨B3, hB3⟩ : ∃ B3, B3 = R.C₃ * D.h i ^ k * T := ⟨_, rfl⟩
  have hB10 : 0 ≤ B1 := by rw [hB1]; positivity
  have hB20 : 0 ≤ B2 := by rw [hB2]; positivity
  have hB30 : 0 ≤ B3 := by rw [hB3]; positivity
  have hed : ‖e‖ + ‖d‖ ≤ B1 := by
    have h2 : 0 ≤ R.C₃ * D.h i ^ (k + 1) := by positivity
    calc ‖e‖ + ‖d‖ ≤ R.C₃ * D.h i ^ (k + 1) * (N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ) := hr2
      _ ≤ R.C₃ * D.h i ^ (k + 1) * T := by
        apply mul_le_mul_of_nonneg_left _ h2
        rw [hT]; linarith [N.un_nonneg (k + 2) E.p.u]
      _ = B1 := hB1.symm
  have hwB : ‖w‖ ≤ B2 := by rw [hB2]; exact hr1
  have hdivB : ‖div e‖ ≤ B3 := by rw [hB3]; exact hr3
  -- `‖w‖ ≤ 1/4`, hence `‖u*ₕ‖ ≥ 3/4` and `u*ₕ ≠ 0`
  have hpow1 : D.h i ^ (k + 2) ≤ D.h i := by
    calc D.h i ^ (k + 2) ≤ D.h i ^ 1 := pow_le_pow_of_le_one hh.le hh1 (by omega)
      _ = D.h i := pow_one _
  have hw14 : ‖w‖ ≤ 1 / 4 := by
    have hpos : 0 < 4 * (R.C₃ * T + 1) := by positivity
    calc ‖w‖ ≤ R.C₃ * D.h i ^ (k + 2) * T := hr1
      _ ≤ R.C₃ * D.h i * T := by gcongr
      _ ≤ R.C₃ * (1 / (4 * (R.C₃ * T + 1))) * T := by gcongr
      _ = (R.C₃ * T) / (4 * (R.C₃ * T + 1)) := by ring
      _ ≤ 1 / 4 := by
        rw [div_le_iff₀ hpos]
        linarith
  have hus : 3 / 4 ≤ ‖uₛ‖ := by
    have := norm_sub_norm_le E.p.u uₛ
    rw [E.u_norm, ← hw] at this
    linarith
  have hus0 : uₛ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hus
    linarith
  -- Lemma 5.6
  have hid := postprocessed_eigenvalue_identity E.p (E.q i) (D.S_le i) (D.Xh_le i) E.u_norm
    hus0 (PP.proj i) (D.div_mem i _ (E.q i).σₕ_mem)
  set κs := postprocessedEigenvalue div (E.q i).σₕ uₛ with hκs
  -- bound on the postprocessed eigenvalue through the Rayleigh quotient
  have hκsb : |κs| ≤ Kst := by
    have h1 := postprocessedEigenvalue_mul_normSq (div := div) (E.q i).σₕ hus0
    have h2 : |κs| * ‖uₛ‖ ^ 2 ≤ ‖div (E.q i).σₕ‖ * ‖uₛ‖ := by
      rw [← abs_of_nonneg (pow_nonneg (norm_nonneg uₛ) 2), ← abs_mul, h1, abs_neg]
      exact abs_real_inner_le_norm _ _
    have hdivσ : div E.p.σ = -E.p.κ • E.p.u := by
      have h0 : ⟪div E.p.σ + E.p.κ • E.p.u, div E.p.σ + E.p.κ • E.p.u⟫_ℝ = 0 := by
        rw [inner_add_left, real_inner_smul_left, E.p.eq₂]
        ring
      rw [inner_self_eq_zero] at h0
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left h0
    have hnσ : ‖div E.p.σ‖ = |E.p.κ| := by
      rw [hdivσ, norm_smul, E.u_norm, mul_one, Real.norm_eq_abs, abs_neg]
    have hdive : div (E.q i).σₕ = div E.p.σ - div e := by rw [he, map_sub]; abel
    have h3 : ‖div (E.q i).σₕ‖ ≤ |E.p.κ| + R.C₃ * T := by
      have hk1 : D.h i ^ k ≤ 1 := pow_le_one₀ hh.le hh1
      calc ‖div (E.q i).σₕ‖ = ‖div E.p.σ - div e‖ := by rw [hdive]
        _ ≤ ‖div E.p.σ‖ + ‖div e‖ := norm_sub_le _ _
        _ ≤ |E.p.κ| + R.C₃ * D.h i ^ k * T := by rw [hnσ]; linarith
        _ ≤ |E.p.κ| + R.C₃ * T := by
          have : R.C₃ * D.h i ^ k * T ≤ R.C₃ * T := by
            rw [show R.C₃ * D.h i ^ k * T = (R.C₃ * T) * D.h i ^ k by ring]
            exact mul_le_of_le_one_right (mul_nonneg hC₃ hT0) hk1
          linarith
    have h4 : |κs| * ‖uₛ‖ ≤ ‖div (E.q i).σₕ‖ := by
      have hpos : 0 < ‖uₛ‖ := by linarith
      have h2' : |κs| * ‖uₛ‖ * ‖uₛ‖ ≤ ‖div (E.q i).σₕ‖ * ‖uₛ‖ := by
        rw [mul_assoc, ← pow_two]; exact h2
      exact le_of_mul_le_mul_right h2' hpos
    have h5 : |κs| * (3 / 4) ≤ |κs| * ‖uₛ‖ := mul_le_mul_of_nonneg_left hus (abs_nonneg _)
    rw [hKst]
    linarith
  -- the five terms of the identity
  have hE0 : 0 ≤ energy M.C (M.Cinv e + d) := M.nonneg _
  have hE1 : energy M.C (M.Cinv e + d) ≤ ‖M.C‖ * ‖M.Cinv e + d‖ ^ 2 := by
    unfold energy
    calc ⟪M.C (M.Cinv e + d), M.Cinv e + d⟫_ℝ
        ≤ ‖M.C (M.Cinv e + d)‖ * ‖M.Cinv e + d‖ := real_inner_le_norm _ _
      _ ≤ (‖M.C‖ * ‖M.Cinv e + d‖) * ‖M.Cinv e + d‖ :=
          mul_le_mul_of_nonneg_right (M.C.le_opNorm _) (norm_nonneg _)
      _ = ‖M.C‖ * ‖M.Cinv e + d‖ ^ 2 := by ring
  have hξ : ‖M.Cinv e + d‖ ≤ (‖M.Cinv‖ + 1) * B1 := by
    calc ‖M.Cinv e + d‖ ≤ ‖M.Cinv e‖ + ‖d‖ := norm_add_le _ _
      _ ≤ ‖M.Cinv‖ * ‖e‖ + ‖d‖ := by have := M.Cinv.le_opNorm e; linarith
      _ ≤ (‖M.Cinv‖ + 1) * (‖e‖ + ‖d‖) := by
          linarith [mul_nonneg (norm_nonneg M.Cinv) (norm_nonneg d), norm_nonneg e]
      _ ≤ (‖M.Cinv‖ + 1) * B1 := by
          apply mul_le_mul_of_nonneg_left hed; positivity
  have hE2 : energy M.C (M.Cinv e + d) ≤ ‖M.C‖ * (‖M.Cinv‖ + 1) ^ 2 * B1 ^ 2 := by
    calc energy M.C (M.Cinv e + d) ≤ ‖M.C‖ * ((‖M.Cinv‖ + 1) * B1) ^ 2 :=
          hE1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hξ 2)
            (norm_nonneg _))
      _ = ‖M.C‖ * (‖M.Cinv‖ + 1) ^ 2 * B1 ^ 2 := by ring
  have hd2 : ‖d‖ ^ 2 ≤ B1 ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg e]) 2
  have hw2 : ‖w‖ ^ 2 ≤ B2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwB 2
  have hX1 : |energy M.C (M.Cinv e + d)| = energy M.C (M.Cinv e + d) := abs_of_nonneg hE0
  have hX2 : |2 * μ * ‖d‖ ^ 2| = 2 * |μ| * ‖d‖ ^ 2 := by
    rw [abs_mul, abs_mul, abs_two, abs_of_nonneg (pow_nonneg (norm_nonneg d) 2)]
  have hX3 : |κs * ‖w‖ ^ 2| = |κs| * ‖w‖ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg w) 2)]
  have hX4 : |2 * ⟪div e, w⟫_ℝ| ≤ 2 * (‖div e‖ * ‖w‖) := by
    rw [abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
  have hX5 : |2 * ⟪(κs - E.p.κ) • E.p.u, w⟫_ℝ| ≤ 2 * |E.p.κ - κs| * ‖w‖ := by
    rw [real_inner_smul_left, abs_mul, abs_mul, abs_two, abs_sub_comm κs E.p.κ]
    have := abs_real_inner_le_norm E.p.u w
    rw [E.u_norm, one_mul] at this
    have := mul_le_mul_of_nonneg_left this (abs_nonneg (E.p.κ - κs))
    linarith
  have hab : ∀ x y : ℝ, |x + y| ≤ |x| + |y| := fun x y => by
    simpa [sub_neg_eq_add] using abs_sub x (-y)
  have tri : ∀ a b c d e : ℝ, |a - b + c + d - e| ≤ |a| + |b| + |c| + |d| + |e| := by
    intro a b c d e
    calc |a - b + c + d - e| ≤ |a - b + c + d| + |e| := abs_sub _ _
      _ ≤ |a - b + c| + |d| + |e| := by linarith [hab (a - b + c) d]
      _ ≤ |a - b| + |c| + |d| + |e| := by linarith [hab (a - b) c]
      _ ≤ |a| + |b| + |c| + |d| + |e| := by linarith [abs_sub a b]
  have hI := (congrArg abs hid).trans_le (tri (energy M.C (M.Cinv e + d)) (2 * μ * ‖d‖ ^ 2)
    (κs * ‖w‖ ^ 2) (2 * ⟪div e, w⟫_ℝ) (2 * ⟪(κs - E.p.κ) • E.p.u, w⟫_ℝ))
  rw [hX1, hX2, hX3] at hI
  -- absorption of the last term using `‖w‖ ≤ 1/4`
  have hI2 : |E.p.κ - κs| ≤ 2 * (energy M.C (M.Cinv e + d) + 2 * |μ| * ‖d‖ ^ 2
      + |κs| * ‖w‖ ^ 2 + 2 * (‖div e‖ * ‖w‖)) := by
    have habs := mul_le_mul_of_nonneg_left hw14 (abs_nonneg (E.p.κ - κs))
    linarith
  -- express everything through `P = h^(2k+2) T²`
  obtain ⟨P, hP⟩ : ∃ P, P = D.h i ^ (2 * k + 2) * T ^ 2 := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hB1sq : B1 ^ 2 = R.C₃ ^ 2 * P := by rw [hB1, hP]; ring
  have hB2sq : B2 ^ 2 ≤ R.C₃ ^ 2 * P := by
    have h1 : (D.h i ^ (k + 2)) ^ 2 ≤ D.h i ^ (2 * k + 2) := by
      rw [← pow_mul]; exact pow_le_pow_of_le_one hh.le hh1 (by omega)
    have h2 : 0 ≤ R.C₃ ^ 2 * T ^ 2 := by positivity
    calc B2 ^ 2 = R.C₃ ^ 2 * T ^ 2 * (D.h i ^ (k + 2)) ^ 2 := by rw [hB2]; ring
      _ ≤ R.C₃ ^ 2 * T ^ 2 * D.h i ^ (2 * k + 2) := mul_le_mul_of_nonneg_left h1 h2
      _ = R.C₃ ^ 2 * P := by rw [hP]; ring
  have hB3B2 : B3 * B2 = R.C₃ ^ 2 * P := by rw [hB3, hB2, hP]; ring
  have hEP : energy M.C (M.Cinv e + d) ≤ ‖M.C‖ * (‖M.Cinv‖ + 1) ^ 2 * (R.C₃ ^ 2 * P) := by
    rw [← hB1sq]; exact hE2
  have hdP : 2 * |μ| * ‖d‖ ^ 2 ≤ 2 * |μ| * (R.C₃ ^ 2 * P) := by
    rw [← hB1sq]; exact mul_le_mul_of_nonneg_left hd2 (by positivity)
  have hwP : |κs| * ‖w‖ ^ 2 ≤ Kst * (R.C₃ ^ 2 * P) :=
    mul_le_mul hκsb (hw2.trans hB2sq) (by positivity) hKst0
  have hdivP : ‖div e‖ * ‖w‖ ≤ R.C₃ ^ 2 * P := by
    rw [← hB3B2]; exact mul_le_mul hdivB hwB (norm_nonneg _) hB30
  calc |E.p.κ - κs|
      ≤ 2 * (energy M.C (M.Cinv e + d) + 2 * |μ| * ‖d‖ ^ 2 + |κs| * ‖w‖ ^ 2
          + 2 * (‖div e‖ * ‖w‖)) := hI2
    _ ≤ 2 * (‖M.C‖ * (‖M.Cinv‖ + 1) ^ 2 + 2 * |μ| + Kst + 2) * R.C₃ ^ 2 * P := by
        linarith
    _ ≤ (2 * (‖M.C‖ * (‖M.Cinv‖ + 1) ^ 2 + 2 * |μ| + Kst + 2) * R.C₃ ^ 2 + 1)
          * D.h i ^ (2 * k + 2) * T ^ 2 := by
        rw [hP] at hP0 ⊢
        linarith

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
