import MixedElasticEigenvalues.Statements.Postprocessing

/-!
# Theorems 6.2 and 6.4: a posteriori error estimation

Theorem 6.2 (reliability of the estimator `η`, p. 48) and Theorem 6.4
(`|κ - κ*ₕ| ≲ η² + h.o.t.`, p. 50) in the abstract framework, both proved.

`APosterioriData` collects the ingredients of Chapter 6:

* the conforming space `V = H¹₀(Ω; ℝ²) ⊆ L²` with the gradient `PP.grad` (which is the
  broken gradient `∇_𝒯` on `U*ₕ`), Gauss' theorem on `V`, and `u ∈ V` with (41) — these
  make `(σ, u, γ)` a solution of the primal mixed eigenvalue problem (62);
* the skew-symmetric part `skw`, the orthogonal projection onto `X`;
* the stability of the primal mixed problem, i.e. the operator `A : W → W'` of p. 46 is
  bounded below. The dual norms of the three residuals are made explicit: by Riesz the
  first is `‖C⁻¹s - ∇v + g‖₀`, the third is `‖skw s‖₀`, and the second, the norm of
  `w ↦ (s, ∇w)` on `V` with the `H¹`-seminorm, is recorded as a function `resG` with its
  two defining properties;
* the Scott–Zhang interpolation onto `V ∩ Uₕ` (p. 47);
* the jump seminorm `Σ_E h_E⁻¹ ‖[·]‖²_E` and the conforming average `ũₕ` with (67).

The element-wise sums `Σ_T h_T² ‖·‖²_T` of the thesis are replaced by `h² ‖·‖²`, which is
equivalent up to constants on the uniform triangulations assumed on p. 8.
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace
open Filter Topology

noncomputable section

variable {H U : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] {ι : Type*}
  {div : H →ₗ[ℝ] U} {X S₀ : Submodule ℝ H} {μ : ℝ}

/-- Ingredients of the a posteriori analysis of Chapter 6, see the module docstring. -/
structure APosterioriData {D : DiscreteFamily div X S₀ ι} {M : MaterialOperator X μ}
    {E : EigenpairFamily D M} (PP : Postprocessing D M E) where
  V : Submodule ℝ U
  u_mem : E.p.u ∈ V
  grad_u : PP.grad E.p.u = M.Cinv E.p.σ + E.p.γ
  green : ∀ σ : H, ∀ v ∈ V, ⟪σ, PP.grad v⟫_ℝ = -⟪div σ, v⟫_ℝ
  skw : H →ₗ[ℝ] H
  skw_mem : ∀ σ, skw σ ∈ X
  skw_inner : ∀ σ, ∀ η ∈ X, ⟪σ, η⟫_ℝ = ⟪skw σ, η⟫_ℝ
  resG : H → ℝ
  resG_bound : ∀ s, ∀ w ∈ V, ⟪s, PP.grad w⟫_ℝ ≤ resG s * ‖PP.grad w‖
  resG_least : ∀ s (b : ℝ), (∀ w ∈ V, ⟪s, PP.grad w⟫_ℝ ≤ b * ‖PP.grad w‖) → resG s ≤ b
  Cst : ℝ
  Cst_nonneg : 0 ≤ Cst
  stab : ∀ s, ∀ v ∈ V, ∀ g ∈ X, ‖M.Cinv s‖ + ‖PP.grad v‖ + ‖g‖
    ≤ Cst * (‖M.Cinv s - PP.grad v + g‖ + resG s + ‖skw s‖)
  sz : ι → U → U
  sz_mem : ∀ i, ∀ v ∈ V, sz i v ∈ V ⊓ D.Uh i
  Csz : ℝ
  Csz_nonneg : 0 ≤ Csz
  sz_approx : ∀ i, ∀ v ∈ V, ‖v - sz i v‖ ≤ Csz * D.h i * ‖PP.grad v‖
  sz_stable : ∀ i, ∀ v ∈ V, ‖sz i v‖ ≤ Csz * ‖PP.grad v‖
  jump : ι → U → ℝ
  jump_nonneg : ∀ i v, 0 ≤ jump i v
  avg : ι → U → U
  avg_mem : ∀ i v, avg i v ∈ V
  Cavg : ℝ
  Cavg_nonneg : 0 ≤ Cavg
  avg_est : ∀ i, ∀ v ∈ PP.Ustar i,
    (D.h i)⁻¹ ^ 2 * ‖v - avg i v‖ ^ 2 + ‖PP.grad v - PP.grad (avg i v)‖ ^ 2 ≤ Cavg * jump i v
  ustar_ne : ∀ i, PP.ustar i ≠ 0
  /-- A uniform bound on the postprocessed eigenvalues. Not spelled out in the thesis,
  where `κ*ₕ → κ` makes it automatic; in this abstract setting it is a hypothesis. -/
  Kstar : ℝ
  Kstar_nonneg : 0 ≤ Kstar
  kstar_bound : ∀ i, |postprocessedEigenvalue div (E.q i).σₕ (PP.ustar i)| ≤ Kstar

/-- The postprocessed eigenvalue `κ*ₕ` on mesh `i` (Definition 5.5). -/
noncomputable def Postprocessing.κstar {D : DiscreteFamily div X S₀ ι} {M : MaterialOperator X μ}
    {E : EigenpairFamily D M} (PP : Postprocessing D M E) (i : ι) : ℝ :=
  postprocessedEigenvalue div (E.q i).σₕ (PP.ustar i)

/-- The higher-order terms of Theorem 6.2:
`h ‖κu - κ*ₕu*ₕ‖₀ + κₕ ‖u - u*ₕ‖₀ + |κ - κₕ|`. -/
noncomputable def Postprocessing.hot {D : DiscreteFamily div X S₀ ι} {M : MaterialOperator X μ}
    {E : EigenpairFamily D M} (PP : Postprocessing D M E) (i : ι) : ℝ :=
  D.h i * ‖E.p.κ • E.p.u - PP.κstar i • PP.ustar i‖ + |(E.q i).κₕ| * ‖E.p.u - PP.ustar i‖
    + |E.p.κ - (E.q i).κₕ|

namespace APosterioriData

variable {D : DiscreteFamily div X S₀ ι} {M : MaterialOperator X μ} {E : EigenpairFamily D M}
  {PP : Postprocessing D M E} (A : APosterioriData PP)

/-- The squared error estimator (p. 48):
`η² = ‖C⁻¹σₕ + γₕ - ∇_𝒯u*ₕ‖₀² + h² ‖κ*ₕu*ₕ + div σₕ‖₀² + Σ_E h_E⁻¹ ‖[u*ₕ]‖²_E + ‖skw σₕ‖₀²`. -/
noncomputable def estimatorSq (i : ι) : ℝ :=
  ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖ ^ 2
    + D.h i ^ 2 * ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖ ^ 2
    + A.jump i (PP.ustar i) + ‖A.skw (E.q i).σₕ‖ ^ 2

/-- The error estimator `η = √(η²)`. -/
noncomputable def estimator (i : ι) : ℝ := Real.sqrt (A.estimatorSq i)

/-- The stress of the primal mixed problem (62) is symmetric, `skw σ = 0`, by its third
equation together with `skw σ ∈ X`. -/
theorem skw_sol_eq_zero : A.skw E.p.σ = 0 := by
  have h1 := E.p.eq₃ (A.skw E.p.σ) (A.skw_mem E.p.σ)
  have h2 := A.skw_inner E.p.σ (A.skw E.p.σ) (A.skw_mem E.p.σ)
  have h3 : ⟪A.skw E.p.σ, A.skw E.p.σ⟫_ℝ = 0 := by rw [← h2]; exact h1
  exact inner_self_eq_zero.mp h3

/-- Hence the third residual of (62) is `‖skw σₕ‖₀`, the last term of the estimator. -/
theorem skw_sub_eq (i : ι) : A.skw (E.p.σ - (E.q i).σₕ) = -A.skw (E.q i).σₕ := by
  rw [map_sub, A.skw_sol_eq_zero, zero_sub]

/-- The central estimate of **Lemma 6.1** (p. 47): the dual norm of the second residual
of (62) is controlled by the volume term of the estimator plus higher-order terms,
`‖Res₂‖ ≲ h ‖κ*ₕu*ₕ + div σₕ‖₀ + h.o.t.`.

The proof follows the thesis: Gauss' theorem turns `(σ - σₕ, ∇w)` into `(κu + div σₕ, w)`;
splitting `w` by its Scott–Zhang interpolant `vₕ` (p. 47), the non-interpolated part is
estimated by `‖w - vₕ‖ ≲ h ‖∇w‖`, while on `vₕ ∈ Uₕ` the strong form of the second
equation of (37) and the postprocessing (52) replace `div σₕ` by `-κₕu*ₕ`. -/
theorem residual_bound (i : ι) :
    A.resG (E.p.σ - (E.q i).σₕ)
      ≤ A.Csz * (D.h i * ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖ + PP.hot i) := by
  refine A.resG_least _ _ (fun w hw => ?_)
  -- Gauss' theorem and the second equation of (36)
  have hgreen : ⟪E.p.σ - (E.q i).σₕ, PP.grad w⟫_ℝ
      = ⟪E.p.κ • E.p.u + div (E.q i).σₕ, w⟫_ℝ := by
    have g1 := A.green E.p.σ w hw
    have g2 := A.green (E.q i).σₕ w hw
    have h2 := E.p.eq₂ w
    rw [inner_sub_left, g1, g2, h2, inner_add_left, real_inner_smul_left]
    ring
  -- split off the Scott–Zhang interpolant
  obtain ⟨hszV, hszU⟩ := A.sz_mem i w hw
  have hd : ⟪div (E.q i).σₕ, A.sz i w⟫_ℝ
      = -((E.q i).κₕ * ⟪PP.ustar i, A.sz i w⟫_ℝ) := by
    rw [(E.q i).eq₂, real_inner_smul_left, ← PP.proj i _ hszU]
    ring
  have hsplit : ⟪E.p.κ • E.p.u + div (E.q i).σₕ, w⟫_ℝ
      = ⟪E.p.κ • E.p.u + div (E.q i).σₕ, w - A.sz i w⟫_ℝ
        + ⟪E.p.κ • E.p.u - (E.q i).κₕ • PP.ustar i, A.sz i w⟫_ℝ := by
    simp only [inner_sub_right, inner_add_left, inner_sub_left, real_inner_smul_left, hd]
    ring
  have hb1 : ⟪E.p.κ • E.p.u + div (E.q i).σₕ, w - A.sz i w⟫_ℝ
      ≤ ‖E.p.κ • E.p.u + div (E.q i).σₕ‖ * (A.Csz * D.h i * ‖PP.grad w‖) :=
    le_trans (real_inner_le_norm _ _)
      (mul_le_mul_of_nonneg_left (A.sz_approx i w hw) (norm_nonneg _))
  have hb2 : ⟪E.p.κ • E.p.u - (E.q i).κₕ • PP.ustar i, A.sz i w⟫_ℝ
      ≤ ‖E.p.κ • E.p.u - (E.q i).κₕ • PP.ustar i‖ * (A.Csz * ‖PP.grad w‖) :=
    le_trans (real_inner_le_norm _ _)
      (mul_le_mul_of_nonneg_left (A.sz_stable i w hw) (norm_nonneg _))
  -- triangle inequalities splitting off the estimator term and the higher-order terms
  have ht1 : ‖E.p.κ • E.p.u + div (E.q i).σₕ‖
      ≤ ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖
        + ‖E.p.κ • E.p.u - PP.κstar i • PP.ustar i‖ := by
    have hrw : E.p.κ • E.p.u + div (E.q i).σₕ
        = (PP.κstar i • PP.ustar i + div (E.q i).σₕ)
          + (E.p.κ • E.p.u - PP.κstar i • PP.ustar i) := by abel
    rw [hrw]; exact norm_add_le _ _
  have ht2 : ‖E.p.κ • E.p.u - (E.q i).κₕ • PP.ustar i‖
      ≤ |E.p.κ - (E.q i).κₕ| + |(E.q i).κₕ| * ‖E.p.u - PP.ustar i‖ := by
    have hrw : E.p.κ • E.p.u - (E.q i).κₕ • PP.ustar i
        = (E.p.κ - (E.q i).κₕ) • E.p.u + (E.q i).κₕ • (E.p.u - PP.ustar i) := by
      rw [sub_smul, smul_sub]; abel
    rw [hrw]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, E.u_norm, mul_one]
  have hc1 : (0:ℝ) ≤ A.Csz * D.h i * ‖PP.grad w‖ := by
    have := (D.h_pos i).le
    have := A.Csz_nonneg
    positivity
  have hc2 : (0:ℝ) ≤ A.Csz * ‖PP.grad w‖ := by
    have := A.Csz_nonneg
    positivity
  have hm1 := mul_le_mul_of_nonneg_right ht1 hc1
  have hm2 := mul_le_mul_of_nonneg_right ht2 hc2
  rw [hgreen, hsplit]
  simp only [Postprocessing.hot]
  nlinarith [hb1, hb2, hm1, hm2]

theorem estimatorSq_nonneg (i : ι) : 0 ≤ A.estimatorSq i := by
  unfold estimatorSq
  have h1 := A.jump_nonneg i (PP.ustar i)
  have h2 : 0 ≤ D.h i ^ 2 * ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖ ^ 2 := by positivity
  linarith [sq_nonneg ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖,
    sq_nonneg ‖A.skw (E.q i).σₕ‖]

/-- `η² = (√η²)²`. -/
theorem sq_estimator (i : ι) : A.estimator i ^ 2 = A.estimatorSq i :=
  Real.sq_sqrt (A.estimatorSq_nonneg i)

theorem estimator_nonneg (i : ι) : 0 ≤ A.estimator i := Real.sqrt_nonneg _

private theorem estimatorSq_eq (i : ι) : A.estimatorSq i
    = ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖ ^ 2
      + D.h i ^ 2 * ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖ ^ 2
      + A.jump i (PP.ustar i) + ‖A.skw (E.q i).σₕ‖ ^ 2 := rfl

/-- The first component of the estimator, `‖C⁻¹σₕ + γₕ - ∇_𝒯u*ₕ‖₀ ≤ η`. -/
theorem res_le_estimator (i : ι) :
    ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖ ≤ A.estimator i := by
  have h1 : ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖ ^ 2 ≤ A.estimatorSq i := by
    rw [A.estimatorSq_eq i]
    have h2 : (0:ℝ) ≤ D.h i ^ 2 * ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖ ^ 2 := by positivity
    linarith [A.jump_nonneg i (PP.ustar i), sq_nonneg ‖A.skw (E.q i).σₕ‖]
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (norm_nonneg _)] at h2

/-- The volume component of the estimator, `h ‖κ*ₕu*ₕ + div σₕ‖₀ ≤ η`. -/
theorem vol_le_estimator (i : ι) :
    D.h i * ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖ ≤ A.estimator i := by
  have hh := (D.h_pos i).le
  have h1 : (D.h i * ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖) ^ 2 ≤ A.estimatorSq i := by
    rw [A.estimatorSq_eq i, mul_pow]
    linarith [A.jump_nonneg i (PP.ustar i), sq_nonneg ‖A.skw (E.q i).σₕ‖,
      sq_nonneg ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖]
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (by positivity)] at h2

/-- The skew component of the estimator, `‖skw σₕ‖₀ ≤ η`. -/
theorem skw_le_estimator (i : ι) : ‖A.skw (E.q i).σₕ‖ ≤ A.estimator i := by
  have h1 : ‖A.skw (E.q i).σₕ‖ ^ 2 ≤ A.estimatorSq i := by
    rw [A.estimatorSq_eq i]
    have h2 : (0:ℝ) ≤ D.h i ^ 2 * ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖ ^ 2 := by positivity
    linarith [A.jump_nonneg i (PP.ustar i),
      sq_nonneg ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖]
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (norm_nonneg _)] at h2

/-- The jump component of the estimator. -/
theorem jump_le_estimatorSq (i : ι) : A.jump i (PP.ustar i) ≤ A.estimatorSq i := by
  rw [A.estimatorSq_eq i]
  have h2 : (0:ℝ) ≤ D.h i ^ 2 * ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖ ^ 2 := by positivity
  linarith [sq_nonneg ‖A.skw (E.q i).σₕ‖,
    sq_nonneg ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖]

/-- Estimate (67) for the gradient of the conforming average `ũₕ` (p. 50). -/
theorem grad_avg_le (i : ι) : ‖PP.grad (PP.ustar i) - PP.grad (A.avg i (PP.ustar i))‖
    ≤ Real.sqrt A.Cavg * A.estimator i := by
  have havg := A.avg_est i (PP.ustar i) (PP.ustar_mem i)
  have h1 : ‖PP.grad (PP.ustar i) - PP.grad (A.avg i (PP.ustar i))‖ ^ 2
      ≤ A.Cavg * A.estimatorSq i := by
    have h2 : (0:ℝ) ≤ (D.h i)⁻¹ ^ 2 * ‖PP.ustar i - A.avg i (PP.ustar i)‖ ^ 2 := by positivity
    linarith [mul_le_mul_of_nonneg_left (A.jump_le_estimatorSq i) A.Cavg_nonneg]
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul A.Cavg_nonneg, ← A.sq_estimator i,
    Real.sqrt_sq (A.estimator_nonneg i)] at h2

/-- Estimate (67) for the conforming average `ũₕ` itself (p. 50). -/
theorem avg_le (i : ι) : ‖PP.ustar i - A.avg i (PP.ustar i)‖
    ≤ D.h i * (Real.sqrt A.Cavg * A.estimator i) := by
  have hh := D.h_pos i
  have hη := A.estimator_nonneg i
  have havg := A.avg_est i (PP.ustar i) (PP.ustar_mem i)
  have h1 : (D.h i)⁻¹ ^ 2 * ‖PP.ustar i - A.avg i (PP.ustar i)‖ ^ 2
      ≤ A.Cavg * A.estimatorSq i := by
    linarith [sq_nonneg ‖PP.grad (PP.ustar i) - PP.grad (A.avg i (PP.ustar i))‖,
      mul_le_mul_of_nonneg_left (A.jump_le_estimatorSq i) A.Cavg_nonneg]
  have h2 : ‖PP.ustar i - A.avg i (PP.ustar i)‖ ^ 2
      ≤ (D.h i * (Real.sqrt A.Cavg * A.estimator i)) ^ 2 := by
    have hexp : (D.h i * (Real.sqrt A.Cavg * A.estimator i)) ^ 2
        = D.h i ^ 2 * (A.Cavg * A.estimatorSq i) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt A.Cavg_nonneg, A.sq_estimator i]
    rw [hexp]
    calc ‖PP.ustar i - A.avg i (PP.ustar i)‖ ^ 2
        = D.h i ^ 2 * ((D.h i)⁻¹ ^ 2 * ‖PP.ustar i - A.avg i (PP.ustar i)‖ ^ 2) := by
          field_simp
      _ ≤ D.h i ^ 2 * (A.Cavg * A.estimatorSq i) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg (D.h i))
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h3

/-- **Theorem 6.2** (p. 48): reliability. Let `κ ∈ ℝ` and `u ∈ H¹₀` solve (62) for some
`(σ, γ)`. The postprocessed eigenfunction `u*ₕ` satisfies
`‖C⁻¹(σ - σₕ)‖₀ + ‖∇u - ∇_𝒯u*ₕ‖₀ + ‖γ - γₕ‖₀ ≲ η + h.o.t.` -/
theorem reliability : ∃ C : ℝ, 0 < C ∧ ∀ i,
    ‖M.Cinv (E.p.σ - (E.q i).σₕ)‖ + ‖PP.grad E.p.u - PP.grad (PP.ustar i)‖
      + ‖E.p.γ - (E.q i).γₕ‖ ≤ C * (A.estimator i + PP.hot i) := by
  -- Proof of the thesis (Lemma 6.1 and pp. 48–49): apply `stab` to the error
  -- `(σ - σₕ, u - ũₕ, γ - γₕ)` with the conforming average `ũₕ = avg i u*ₕ`. By (41) the
  -- first residual is `‖C⁻¹σₕ + γₕ - ∇ũₕ‖`, the second is bounded by `residual_bound`
  -- and the third is `‖skw σₕ‖` by `skw_sub_eq`. The terms with `ũₕ` are replaced by
  -- `u*ₕ` via (67), and each component of `η²` is bounded by `η`.
  have hCst := A.Cst_nonneg
  have hCsz := A.Csz_nonneg
  have hCavg := A.Cavg_nonneg
  have hsqC : (0:ℝ) ≤ Real.sqrt A.Cavg := Real.sqrt_nonneg _
  refine ⟨A.Cst * (2 + Real.sqrt A.Cavg + A.Csz) + Real.sqrt A.Cavg + A.Cst * A.Csz + 1,
    by positivity, fun i => ?_⟩
  have hh := (D.h_pos i).le
  have hjump0 := A.jump_nonneg i (PP.ustar i)
  have hη0 : 0 ≤ A.estimator i := Real.sqrt_nonneg _
  have hhot0 : 0 ≤ PP.hot i := by
    simp only [Postprocessing.hot]
    positivity
  have hc1 := A.res_le_estimator i
  have hc2 := A.vol_le_estimator i
  have hc3 := A.skw_le_estimator i
  have hJ := A.grad_avg_le i
  -- stability of the primal mixed problem, applied to the error
  have hvmem : E.p.u - A.avg i (PP.ustar i) ∈ A.V :=
    A.V.sub_mem A.u_mem (A.avg_mem i (PP.ustar i))
  have hgmem : E.p.γ - (E.q i).γₕ ∈ X :=
    X.sub_mem E.p.γ_mem (D.Xh_le i (E.q i).γₕ_mem)
  have hstab := A.stab (E.p.σ - (E.q i).σₕ) _ hvmem _ hgmem
  have hres1 : M.Cinv (E.p.σ - (E.q i).σₕ) - PP.grad (E.p.u - A.avg i (PP.ustar i))
        + (E.p.γ - (E.q i).γₕ)
      = -(M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (A.avg i (PP.ustar i))) := by
    simp only [map_sub, A.grad_u]
    abel
  have hres1' : ‖M.Cinv (E.p.σ - (E.q i).σₕ) - PP.grad (E.p.u - A.avg i (PP.ustar i))
        + (E.p.γ - (E.q i).γₕ)‖
      ≤ ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖
        + ‖PP.grad (PP.ustar i) - PP.grad (A.avg i (PP.ustar i))‖ := by
    rw [hres1, norm_neg,
      show M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (A.avg i (PP.ustar i))
        = (M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i))
          + (PP.grad (PP.ustar i) - PP.grad (A.avg i (PP.ustar i))) from by abel]
    exact norm_add_le _ _
  have hSk : ‖A.skw (E.p.σ - (E.q i).σₕ)‖ = ‖A.skw (E.q i).σₕ‖ := by
    rw [A.skw_sub_eq i, norm_neg]
  have hRle : A.resG (E.p.σ - (E.q i).σₕ) ≤ A.Csz * (A.estimator i + PP.hot i) :=
    le_trans (A.residual_bound i) (mul_le_mul_of_nonneg_left (by linarith) hCsz)
  -- the gradient of the error against the conforming average
  have hsplit : ‖PP.grad E.p.u - PP.grad (PP.ustar i)‖
      ≤ ‖PP.grad (E.p.u - A.avg i (PP.ustar i))‖
        + ‖PP.grad (PP.ustar i) - PP.grad (A.avg i (PP.ustar i))‖ := by
    rw [map_sub,
      show PP.grad E.p.u - PP.grad (PP.ustar i)
        = (PP.grad E.p.u - PP.grad (A.avg i (PP.ustar i)))
          - (PP.grad (PP.ustar i) - PP.grad (A.avg i (PP.ustar i))) from by abel]
    exact norm_sub_le _ _
  have hstab2 : A.Cst * (‖M.Cinv (E.p.σ - (E.q i).σₕ)
        - PP.grad (E.p.u - A.avg i (PP.ustar i)) + (E.p.γ - (E.q i).γₕ)‖
        + A.resG (E.p.σ - (E.q i).σₕ) + ‖A.skw (E.p.σ - (E.q i).σₕ)‖)
      ≤ A.Cst * ((A.estimator i + Real.sqrt A.Cavg * A.estimator i)
        + A.Csz * (A.estimator i + PP.hot i) + A.estimator i) := by
    refine mul_le_mul_of_nonneg_left ?_ hCst
    rw [hSk]
    linarith [hres1', hJ, hRle, hc1, hc3]
  linarith [hstab, hstab2, hsplit, hJ, hη0, hhot0,
    mul_nonneg hCst hhot0, mul_nonneg (mul_nonneg hCst hsqC) hhot0,
    mul_nonneg (mul_nonneg hCst hCsz) hhot0, mul_nonneg hsqC hhot0,
    mul_nonneg (mul_nonneg hCst hCsz) hη0]

/-- **Theorem 6.4** (p. 50): `|κ - κ*ₕ| ≲ η² + h.o.t.` for sufficiently small `h`, where
the higher-order terms are `(h.o.t.)²` of Theorem 6.2, `‖u - u*ₕ‖₀²` and `(κ - κ*ₕ)²`. -/
theorem eigenvalue_reliability : ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 < C ∧ ∀ i, D.h i ≤ h₀ →
    |E.p.κ - PP.κstar i| ≤ C * (A.estimatorSq i + PP.hot i ^ 2 + ‖E.p.u - PP.ustar i‖ ^ 2
      + (E.p.κ - PP.κstar i) ^ 2) := by
  -- Lemma 5.6 (`postprocessed_eigenvalue_identity`) with `u - u*ₕ = (u - ũₕ) + (ũₕ - u*ₕ)`,
  -- Gauss' theorem for `(div(σ - σₕ), u - ũₕ)`, Theorem 6.2 for the remaining norms,
  -- (67) for the conforming average and Young's inequality for the last term.
  obtain ⟨C₆, hC₆, hrel⟩ := A.reliability
  have hCn := norm_nonneg M.C
  have hsqC : (0:ℝ) ≤ Real.sqrt A.Cavg := Real.sqrt_nonneg _
  have hK := A.Kstar_nonneg
  obtain ⟨K₁, hK₁def⟩ : ∃ K, K = 4 * ‖M.C‖ * C₆ ^ 2 + 2 * |μ| * C₆ ^ 2
      + 2 * ‖M.C‖ * C₆ * (C₆ + Real.sqrt A.Cavg) + 2 * Real.sqrt A.Cavg := ⟨_, rfl⟩
  have hK₁ : (0:ℝ) ≤ K₁ := by rw [hK₁def]; positivity
  refine ⟨1, 2 * K₁ + A.Kstar + 2, one_pos, by positivity, fun i _ => ?_⟩
  have hh := (D.h_pos i).le
  have hη := A.estimator_nonneg i
  have hhot : 0 ≤ PP.hot i := by
    simp only [Postprocessing.hot]
    positivity
  set R := A.estimator i + PP.hot i with hRdef
  have hR0 : 0 ≤ R := by rw [hRdef]; linarith
  -- Lemma 5.6
  have hκdef : PP.κstar i = postprocessedEigenvalue div (E.q i).σₕ (PP.ustar i) := rfl
  have hid := postprocessed_eigenvalue_identity E.p (E.q i) (D.S_le i) (D.Xh_le i) E.u_norm
    (A.ustar_ne i) (PP.proj i) (D.div_mem i _ (E.q i).σₕ_mem)
  rw [← hκdef] at hid
  -- Theorem 6.2
  have hrel' := hrel i
  have hn1 := norm_nonneg (M.Cinv (E.p.σ - (E.q i).σₕ))
  have hn2 := norm_nonneg (PP.grad E.p.u - PP.grad (PP.ustar i))
  have hn3 := norm_nonneg (E.p.γ - (E.q i).γₕ)
  have hb1 : ‖M.Cinv (E.p.σ - (E.q i).σₕ)‖ ≤ C₆ * R := by linarith
  have hb2 : ‖PP.grad E.p.u - PP.grad (PP.ustar i)‖ ≤ C₆ * R := by linarith
  have hb3 : ‖E.p.γ - (E.q i).γₕ‖ ≤ C₆ * R := by linarith
  have hCR0 : (0:ℝ) ≤ C₆ * R := by positivity
  have hCe : ‖E.p.σ - (E.q i).σₕ‖ ≤ ‖M.C‖ * (C₆ * R) := by
    calc ‖E.p.σ - (E.q i).σₕ‖ = ‖M.C (M.Cinv (E.p.σ - (E.q i).σₕ))‖ := by
          rw [M.C_Cinv]
      _ ≤ ‖M.C‖ * ‖M.Cinv (E.p.σ - (E.q i).σₕ)‖ := M.C.le_opNorm _
      _ ≤ ‖M.C‖ * (C₆ * R) := mul_le_mul_of_nonneg_left hb1 hCn
  -- (1) the energy term
  have hE0 : 0 ≤ energy M.C (M.Cinv (E.p.σ - (E.q i).σₕ) + (E.p.γ - (E.q i).γₕ)) := M.nonneg _
  have hE1 : energy M.C (M.Cinv (E.p.σ - (E.q i).σₕ) + (E.p.γ - (E.q i).γₕ))
      ≤ ‖M.C‖ * (2 * (C₆ * R)) ^ 2 := by
    have hx : ‖M.Cinv (E.p.σ - (E.q i).σₕ) + (E.p.γ - (E.q i).γₕ)‖ ≤ 2 * (C₆ * R) :=
      le_trans (norm_add_le _ _) (by linarith)
    calc energy M.C (M.Cinv (E.p.σ - (E.q i).σₕ) + (E.p.γ - (E.q i).γₕ))
        ≤ ‖M.C‖ * ‖M.Cinv (E.p.σ - (E.q i).σₕ) + (E.p.γ - (E.q i).γₕ)‖ ^ 2 := by
          unfold energy
          have hcs := real_inner_le_norm (M.C (M.Cinv (E.p.σ - (E.q i).σₕ) + (E.p.γ - (E.q i).γₕ)))
            (M.Cinv (E.p.σ - (E.q i).σₕ) + (E.p.γ - (E.q i).γₕ))
          have hop := M.C.le_opNorm (M.Cinv (E.p.σ - (E.q i).σₕ) + (E.p.γ - (E.q i).γₕ))
          have h2 := mul_le_mul_of_nonneg_right hop
            (norm_nonneg (M.Cinv (E.p.σ - (E.q i).σₕ) + (E.p.γ - (E.q i).γₕ)))
          linarith [hcs, h2]
      _ ≤ ‖M.C‖ * (2 * (C₆ * R)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2) hCn
  -- (2) the skew term
  have hE2 : |2 * μ * ‖E.p.γ - (E.q i).γₕ‖ ^ 2| ≤ 2 * |μ| * (C₆ * R) ^ 2 := by
    rw [abs_mul, abs_mul, abs_two, abs_of_nonneg (sq_nonneg ‖E.p.γ - (E.q i).γₕ‖)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb3 2) (by positivity)
  -- (3) the postprocessed eigenvalue term
  have hE3 : |PP.κstar i * ‖E.p.u - PP.ustar i‖ ^ 2|
      ≤ A.Kstar * ‖E.p.u - PP.ustar i‖ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖E.p.u - PP.ustar i‖)]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hkb := A.kstar_bound i
    rwa [← hκdef] at hkb
  -- (4) the divergence term, split at the conforming average
  have hdivσ : div E.p.σ = -E.p.κ • E.p.u := by
    have h0 : ⟪div E.p.σ + E.p.κ • E.p.u, div E.p.σ + E.p.κ • E.p.u⟫_ℝ = 0 := by
      rw [inner_add_left, real_inner_smul_left, E.p.eq₂]
      ring
    rw [inner_self_eq_zero] at h0
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left h0
  have hdiven : ‖div (E.p.σ - (E.q i).σₕ)‖ = ‖E.p.κ • E.p.u + div (E.q i).σₕ‖ := by
    rw [show div (E.p.σ - (E.q i).σₕ) = -(E.p.κ • E.p.u + div (E.q i).σₕ) from by
      rw [map_sub, hdivσ, neg_smul]; abel, norm_neg]
  have hvV : E.p.u - A.avg i (PP.ustar i) ∈ A.V :=
    A.V.sub_mem A.u_mem (A.avg_mem i (PP.ustar i))
  have hbA : |⟪div (E.p.σ - (E.q i).σₕ), E.p.u - A.avg i (PP.ustar i)⟫_ℝ|
      ≤ (‖M.C‖ * (C₆ * R)) * (C₆ * R + Real.sqrt A.Cavg * A.estimator i) := by
    have hgauss : ⟪div (E.p.σ - (E.q i).σₕ), E.p.u - A.avg i (PP.ustar i)⟫_ℝ
        = -⟪E.p.σ - (E.q i).σₕ, PP.grad (E.p.u - A.avg i (PP.ustar i))⟫_ℝ := by
      rw [A.green (E.p.σ - (E.q i).σₕ) _ hvV]; ring
    rw [hgauss, abs_neg]
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    have hg : ‖PP.grad (E.p.u - A.avg i (PP.ustar i))‖
        ≤ C₆ * R + Real.sqrt A.Cavg * A.estimator i := by
      rw [map_sub, show PP.grad E.p.u - PP.grad (A.avg i (PP.ustar i))
        = (PP.grad E.p.u - PP.grad (PP.ustar i))
          + (PP.grad (PP.ustar i) - PP.grad (A.avg i (PP.ustar i))) from by abel]
      exact le_trans (norm_add_le _ _) (by linarith [A.grad_avg_le i])
    exact mul_le_mul hCe hg (norm_nonneg _) (by positivity)
  have hbB : |⟪div (E.p.σ - (E.q i).σₕ), A.avg i (PP.ustar i) - PP.ustar i⟫_ℝ|
      ≤ Real.sqrt A.Cavg * A.estimator i * R := by
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    have hn : ‖A.avg i (PP.ustar i) - PP.ustar i‖
        ≤ D.h i * (Real.sqrt A.Cavg * A.estimator i) := by
      rw [norm_sub_rev]; exact A.avg_le i
    have hd : ‖div (E.p.σ - (E.q i).σₕ)‖ ≤ ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖
        + ‖E.p.κ • E.p.u - PP.κstar i • PP.ustar i‖ := by
      rw [hdiven, show E.p.κ • E.p.u + div (E.q i).σₕ
        = (PP.κstar i • PP.ustar i + div (E.q i).σₕ)
          + (E.p.κ • E.p.u - PP.κstar i • PP.ustar i) from by abel]
      exact norm_add_le _ _
    have hvol := A.vol_le_estimator i
    have hhot2 : D.h i * ‖E.p.κ • E.p.u - PP.κstar i • PP.ustar i‖ ≤ PP.hot i := by
      simp only [Postprocessing.hot]
      have hA : (0:ℝ) ≤ |(E.q i).κₕ| * ‖E.p.u - PP.ustar i‖ := by positivity
      linarith [abs_nonneg (E.p.κ - (E.q i).κₕ)]
    calc ‖div (E.p.σ - (E.q i).σₕ)‖ * ‖A.avg i (PP.ustar i) - PP.ustar i‖
        ≤ (‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖
            + ‖E.p.κ • E.p.u - PP.κstar i • PP.ustar i‖)
          * (D.h i * (Real.sqrt A.Cavg * A.estimator i)) :=
          mul_le_mul hd hn (norm_nonneg _) (by positivity)
      _ = Real.sqrt A.Cavg * A.estimator i
            * (D.h i * ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖
              + D.h i * ‖E.p.κ • E.p.u - PP.κstar i • PP.ustar i‖) := by ring
      _ ≤ Real.sqrt A.Cavg * A.estimator i * R := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hRdef]; linarith
  have hE4 : |2 * ⟪div (E.p.σ - (E.q i).σₕ), E.p.u - PP.ustar i⟫_ℝ|
      ≤ 2 * ((‖M.C‖ * (C₆ * R)) * (C₆ * R + Real.sqrt A.Cavg * A.estimator i)
        + Real.sqrt A.Cavg * A.estimator i * R) := by
    rw [show ⟪div (E.p.σ - (E.q i).σₕ), E.p.u - PP.ustar i⟫_ℝ
      = ⟪div (E.p.σ - (E.q i).σₕ), E.p.u - A.avg i (PP.ustar i)⟫_ℝ
        + ⟪div (E.p.σ - (E.q i).σₕ), A.avg i (PP.ustar i) - PP.ustar i⟫_ℝ from by
      rw [← inner_add_right]; congr 1; abel, abs_mul, abs_two]
    have := abs_add_le ⟪div (E.p.σ - (E.q i).σₕ), E.p.u - A.avg i (PP.ustar i)⟫_ℝ
      ⟪div (E.p.σ - (E.q i).σₕ), A.avg i (PP.ustar i) - PP.ustar i⟫_ℝ
    linarith [hbA, hbB]
  -- (5) Young's inequality for the last term
  have hE5 : |2 * ⟪(PP.κstar i - E.p.κ) • E.p.u, E.p.u - PP.ustar i⟫_ℝ|
      ≤ (E.p.κ - PP.κstar i) ^ 2 + ‖E.p.u - PP.ustar i‖ ^ 2 := by
    rw [real_inner_smul_left, abs_mul, abs_mul, abs_two, abs_sub_comm (PP.κstar i) E.p.κ]
    have hcs := abs_real_inner_le_norm E.p.u (E.p.u - PP.ustar i)
    rw [E.u_norm, one_mul] at hcs
    nlinarith [hcs, abs_nonneg (E.p.κ - PP.κstar i), norm_nonneg (E.p.u - PP.ustar i),
      sq_nonneg (|E.p.κ - PP.κstar i| - ‖E.p.u - PP.ustar i‖), sq_abs (E.p.κ - PP.κstar i)]
  -- assembly
  have hab : ∀ x y : ℝ, |x + y| ≤ |x| + |y| := fun x y => by
    simpa [sub_neg_eq_add] using abs_sub x (-y)
  have tri : ∀ a b c d e : ℝ, |a - b + c + d - e| ≤ |a| + |b| + |c| + |d| + |e| := by
    intro a b c d e
    calc |a - b + c + d - e| ≤ |a - b + c + d| + |e| := abs_sub _ _
      _ ≤ |a - b + c| + |d| + |e| := by linarith [hab (a - b + c) d]
      _ ≤ |a - b| + |c| + |d| + |e| := by linarith [hab (a - b) c]
      _ ≤ |a| + |b| + |c| + |d| + |e| := by linarith [abs_sub a b]
  have hI := (congrArg abs hid).trans_le
    (tri (energy M.C (M.Cinv (E.p.σ - (E.q i).σₕ) + (E.p.γ - (E.q i).γₕ)))
      (2 * μ * ‖E.p.γ - (E.q i).γₕ‖ ^ 2) (PP.κstar i * ‖E.p.u - PP.ustar i‖ ^ 2)
      (2 * ⟪div (E.p.σ - (E.q i).σₕ), E.p.u - PP.ustar i⟫_ℝ)
      (2 * ⟪(PP.κstar i - E.p.κ) • E.p.u, E.p.u - PP.ustar i⟫_ℝ))
  rw [abs_of_nonneg hE0] at hI
  have hηR : A.estimator i ≤ R := by rw [hRdef]; linarith
  have hmain : |E.p.κ - PP.κstar i|
      ≤ K₁ * R ^ 2 + (A.Kstar + 1) * ‖E.p.u - PP.ustar i‖ ^ 2
        + (E.p.κ - PP.κstar i) ^ 2 := by
    have hp1 : Real.sqrt A.Cavg * A.estimator i ≤ Real.sqrt A.Cavg * R :=
      mul_le_mul_of_nonneg_left hηR hsqC
    have hp2 : Real.sqrt A.Cavg * A.estimator i * R ≤ Real.sqrt A.Cavg * R * R :=
      mul_le_mul_of_nonneg_right hp1 hR0
    have hp3 : (‖M.C‖ * (C₆ * R)) * (C₆ * R + Real.sqrt A.Cavg * A.estimator i)
        ≤ (‖M.C‖ * (C₆ * R)) * (C₆ * R + Real.sqrt A.Cavg * R) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [hK₁def]
    linarith [hI, hE1, hE2, hE3, hE4, hE5, hp2, hp3]
  have hRsq : R ^ 2 ≤ 2 * (A.estimatorSq i + PP.hot i ^ 2) := by
    have hsq := A.sq_estimator i
    have hexp : R ^ 2 = A.estimator i ^ 2 + 2 * (A.estimator i * PP.hot i) + PP.hot i ^ 2 := by
      rw [hRdef]; ring
    rw [hexp, hsq]
    linarith [sq_nonneg (A.estimator i - PP.hot i), hsq]
  have e1 : (0:ℝ) ≤ A.estimatorSq i := A.estimatorSq_nonneg i
  have e2 : (0:ℝ) ≤ PP.hot i ^ 2 := sq_nonneg _
  have e3 : (0:ℝ) ≤ ‖E.p.u - PP.ustar i‖ ^ 2 := sq_nonneg _
  have e4 : (0:ℝ) ≤ (E.p.κ - PP.κstar i) ^ 2 := sq_nonneg _
  have hstep := mul_le_mul_of_nonneg_left hRsq hK₁
  linarith [hmain, hstep, mul_nonneg hK e1, mul_nonneg hK e2, mul_nonneg hK₁ e3,
    mul_nonneg hK₁ e4, mul_nonneg hK e4, e1, e2, e3, e4]

end APosterioriData

/-- The hypotheses of Theorems 6.2 and 6.4 are satisfiable in the trivial model
(`V = ℝ`, `∇ = -id`, `skw = 0`, `resG = ‖·‖`, `Cst = 2`, Scott–Zhang and the conforming
average equal to the identity, no jumps). -/
example (μ : ℝ) (E : EigenpairFamily trivialFamily (trivialMaterial μ))
    (hp : E.p = trivialEigenpair μ) (hq : ∀ n, E.q n = trivialDiscreteEigenpair μ n) :
    APosterioriData (trivialPostprocessing μ E hq) where
  V := ⊤
  u_mem := Submodule.mem_top
  grad_u := by simp [trivialPostprocessing, hp, trivialEigenpair, trivialMaterial]
  green := fun σ v _ => by simp [trivialPostprocessing]
  skw := 0
  skw_mem := fun _ => Submodule.zero_mem _
  skw_inner := fun σ η hη => by simp [(Submodule.mem_bot ℝ).mp hη]
  resG := fun s => ‖s‖
  resG_bound := fun s w _ => by
    simpa [trivialPostprocessing] using real_inner_le_norm s (-w)
  resG_least := fun s b hb => by
    by_cases hs : s = 0
    · have := hb (-1) Submodule.mem_top
      simp only [trivialPostprocessing, LinearMap.neg_apply, LinearMap.id_coe, id_eq, neg_neg,
        norm_one, mul_one, hs, inner_zero_left] at this
      simpa [hs] using this
    · have := hb (-s) Submodule.mem_top
      simp only [trivialPostprocessing, LinearMap.neg_apply, LinearMap.id_coe, id_eq, neg_neg,
        real_inner_self_eq_norm_sq] at this
      have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hs
      nlinarith
  Cst := 2
  Cst_nonneg := by norm_num
  stab := fun s v _ g hg => by
    simp only [(Submodule.mem_bot ℝ).mp hg, trivialMaterial, ContinuousLinearMap.id_apply,
      trivialPostprocessing, LinearMap.neg_apply, LinearMap.id_coe, id_eq, norm_neg,
      LinearMap.zero_apply, norm_zero, add_zero, sub_neg_eq_add]
    have h1 : ‖v‖ ≤ ‖s + v‖ + ‖s‖ := by
      calc ‖v‖ = ‖(s + v) - s‖ := by congr 1; abel
        _ ≤ ‖s + v‖ + ‖s‖ := norm_sub_le _ _
    linarith [norm_nonneg s, norm_nonneg (s + v)]
  sz := fun _ v => v
  sz_mem := fun _ _ _ => ⟨Submodule.mem_top, Submodule.mem_top⟩
  Csz := 1
  Csz_nonneg := zero_le_one
  sz_approx := fun n v _ => by
    have := trivialFamily.h_pos n
    simp only [sub_self, norm_zero]
    positivity
  sz_stable := fun n v _ => by simp [trivialPostprocessing]
  jump := fun _ _ => 0
  jump_nonneg := fun _ _ => le_rfl
  avg := fun _ v => v
  avg_mem := fun _ _ => Submodule.mem_top
  Cavg := 0
  Cavg_nonneg := le_rfl
  avg_est := fun n v _ => by simp
  ustar_ne := fun _ => by simp [trivialPostprocessing]
  Kstar := 1
  Kstar_nonneg := zero_le_one
  kstar_bound := fun n => by
    have h1 : (E.q n).σₕ = -1 := by rw [hq]; rfl
    simp [postprocessedEigenvalue, trivialPostprocessing, h1]

end

end MixedElasticEigenvalues
