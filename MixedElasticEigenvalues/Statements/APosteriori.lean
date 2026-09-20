import MixedElasticEigenvalues.Statements.Postprocessing

/-!
# Theorems 6.2 and 6.4: a posteriori error estimation

Proofs of Theorem 6.2 (reliability of the estimator `η`, p. 48) and Theorem 6.4
(`|κ - κ*ₕ| ≲ η² + h.o.t.`, p. 50) in the abstract framework.

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
  have hest : A.estimator i = Real.sqrt (A.estimatorSq i) := rfl
  have hsqSq : A.estimatorSq i
      = ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖ ^ 2
        + D.h i ^ 2 * ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖ ^ 2
        + A.jump i (PP.ustar i) + ‖A.skw (E.q i).σₕ‖ ^ 2 := rfl
  have hpos2 : (0:ℝ) ≤ D.h i ^ 2 * ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖ ^ 2 := by
    positivity
  -- every component of `η²` is bounded by `η`
  have hc1 : ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖ ≤ A.estimator i := by
    have h1 : ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖ ^ 2
        ≤ A.estimatorSq i := by
      rw [hsqSq]; linarith [sq_nonneg ‖A.skw (E.q i).σₕ‖]
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (norm_nonneg _), ← hest] at h2
  have hc2 : D.h i * ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖ ≤ A.estimator i := by
    have h1 : (D.h i * ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖) ^ 2 ≤ A.estimatorSq i := by
      rw [hsqSq, mul_pow]
      linarith [sq_nonneg ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖,
        sq_nonneg ‖A.skw (E.q i).σₕ‖]
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity), ← hest] at h2
  have hc3 : ‖A.skw (E.q i).σₕ‖ ≤ A.estimator i := by
    have h1 : ‖A.skw (E.q i).σₕ‖ ^ 2 ≤ A.estimatorSq i := by
      rw [hsqSq]
      linarith [sq_nonneg ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖]
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (norm_nonneg _), ← hest] at h2
  -- the conforming average, estimate (67)
  have hJ : ‖PP.grad (PP.ustar i) - PP.grad (A.avg i (PP.ustar i))‖
      ≤ Real.sqrt A.Cavg * A.estimator i := by
    have havg := A.avg_est i (PP.ustar i) (PP.ustar_mem i)
    have hj : A.jump i (PP.ustar i) ≤ A.estimatorSq i := by
      rw [hsqSq]
      linarith [sq_nonneg ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖,
        sq_nonneg ‖A.skw (E.q i).σₕ‖]
    have h1 : ‖PP.grad (PP.ustar i) - PP.grad (A.avg i (PP.ustar i))‖ ^ 2
        ≤ A.Cavg * A.estimatorSq i := by
      have h2 : (0:ℝ) ≤ (D.h i)⁻¹ ^ 2 * ‖PP.ustar i - A.avg i (PP.ustar i)‖ ^ 2 := by positivity
      linarith [mul_le_mul_of_nonneg_left hj hCavg]
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hCavg, ← hest] at h2
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

/-- The element residual is one of the nonnegative components of the estimator. -/
theorem residual_le_estimator (i : ι) :
    D.h i * ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖ ≤ A.estimator i := by
  have hsq : (D.h i * ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖) ^ 2
      ≤ A.estimatorSq i := by
    simp only [estimatorSq, Postprocessing.κstar, mul_pow]
    linarith [A.jump_nonneg i (PP.ustar i),
      sq_nonneg ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖,
      sq_nonneg ‖A.skw (E.q i).σₕ‖]
  have h := Real.sqrt_le_sqrt hsq
  have hh := (D.h_pos i).le
  simpa only [Real.sqrt_sq (mul_nonneg hh (norm_nonneg
    (PP.κstar i • PP.ustar i + div (E.q i).σₕ))), estimator] using h

/-- The jump contribution is bounded by the squared estimator. -/
theorem jump_le_estimatorSq (i : ι) : A.jump i (PP.ustar i) ≤ A.estimatorSq i := by
  unfold estimatorSq
  have hres : 0 ≤ D.h i ^ 2 *
      ‖PP.κstar i • PP.ustar i + div (E.q i).σₕ‖ ^ 2 := by positivity
  linarith [sq_nonneg ‖M.Cinv (E.q i).σₕ + (E.q i).γₕ - PP.grad (PP.ustar i)‖,
    sq_nonneg ‖A.skw (E.q i).σₕ‖]

/-- The conforming average differs from the postprocessed function by at most the
jump contribution, in both the scaled `L²` norm and the broken gradient norm. -/
theorem average_error_le_estimator (i : ι) :
    ‖PP.ustar i - A.avg i (PP.ustar i)‖ ≤ D.h i * Real.sqrt A.Cavg * A.estimator i ∧
    ‖PP.grad (PP.ustar i) - PP.grad (A.avg i (PP.ustar i))‖
      ≤ Real.sqrt A.Cavg * A.estimator i := by
  have hh := D.h_pos i
  have havg := (A.avg_est i (PP.ustar i) (PP.ustar_mem i)).trans
    (mul_le_mul_of_nonneg_left (A.jump_le_estimatorSq i) A.Cavg_nonneg)
  have hscaled : (D.h i)⁻¹ * ‖PP.ustar i - A.avg i (PP.ustar i)‖
      ≤ Real.sqrt A.Cavg * A.estimator i := by
    have hsq : ((D.h i)⁻¹ * ‖PP.ustar i - A.avg i (PP.ustar i)‖) ^ 2
        ≤ A.Cavg * A.estimatorSq i := by
      rw [mul_pow]
      linarith [sq_nonneg ‖PP.grad (PP.ustar i) - PP.grad (A.avg i (PP.ustar i))‖]
    have h := Real.sqrt_le_sqrt hsq
    simpa only [Real.sqrt_sq (mul_nonneg (inv_nonneg.mpr hh.le)
      (norm_nonneg (PP.ustar i - A.avg i (PP.ustar i)))),
      Real.sqrt_mul A.Cavg_nonneg, estimator] using h
  constructor
  · calc ‖PP.ustar i - A.avg i (PP.ustar i)‖
        = D.h i * ((D.h i)⁻¹ * ‖PP.ustar i - A.avg i (PP.ustar i)‖) := by
            rw [← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
      _ ≤ D.h i * (Real.sqrt A.Cavg * A.estimator i) :=
          mul_le_mul_of_nonneg_left hscaled hh.le
      _ = D.h i * Real.sqrt A.Cavg * A.estimator i := by ring
  · have hsq : ‖PP.grad (PP.ustar i) - PP.grad (A.avg i (PP.ustar i))‖ ^ 2
        ≤ A.Cavg * A.estimatorSq i := by
      have hnonneg : 0 ≤ (D.h i)⁻¹ ^ 2 * ‖PP.ustar i - A.avg i (PP.ustar i)‖ ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith
    have h := Real.sqrt_le_sqrt hsq
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul A.Cavg_nonneg, estimator] using h

/-- **Theorem 6.4** (p. 50): `|κ - κ*ₕ| ≲ η² + h.o.t.`, where the higher-order terms are
`(h.o.t.)²` of Theorem 6.2, `‖u - u*ₕ‖₀²` and `(κ - κ*ₕ)²`. With the last term retained,
the estimate holds on every mesh: errors at least one are bounded by their square, and
smaller errors imply `|κ*ₕ| ≤ |κ| + 1`. No extra eigenvalue bound is needed. -/
theorem eigenvalue_reliability : ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 < C ∧ ∀ i, D.h i ≤ h₀ →
    |E.p.κ - PP.κstar i| ≤ C * (A.estimatorSq i + PP.hot i ^ 2 + ‖E.p.u - PP.ustar i‖ ^ 2
      + (E.p.κ - PP.κstar i) ^ 2) := by
  obtain ⟨Cr, hCr, hr⟩ := A.reliability
  let a := Real.sqrt A.Cavg
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  let K := ‖M.C‖ * Cr * (Cr + a) + a
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let B := (‖M.C‖ + 2 * |μ|) * Cr ^ 2 + 2 * K
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨1, 2 * B + |E.p.κ| + 3, by norm_num, by positivity, fun i _ => ?_⟩
  have hh := D.h_pos i
  let e := E.p.σ - (E.q i).σₕ
  let g := E.p.γ - (E.q i).γₕ
  let w := E.p.u - PP.ustar i
  let v := E.p.u - A.avg i (PP.ustar i)
  let z := PP.ustar i - A.avg i (PP.ustar i)
  let κs := PP.κstar i
  let δ := |E.p.κ - κs|
  let S := A.estimator i + PP.hot i
  let T := A.estimatorSq i + PP.hot i ^ 2
  have hη : 0 ≤ A.estimator i := Real.sqrt_nonneg _
  have hhot : 0 ≤ PP.hot i := by
    have hh := (D.h_pos i).le
    unfold Postprocessing.hot
    positivity
  have hS : 0 ≤ S := add_nonneg hη hhot
  have hT : 0 ≤ T := add_nonneg (A.estimatorSq_nonneg i) (sq_nonneg _)
  have hηS : A.estimator i ≤ S := le_add_of_nonneg_right hhot
  have hSsq : S ^ 2 ≤ 2 * T := by
    have hsq : A.estimator i ^ 2 = A.estimatorSq i :=
      Real.sq_sqrt (A.estimatorSq_nonneg i)
    dsimp [S, T]
    nlinarith only [hsq, sq_nonneg (A.estimator i - PP.hot i)]
  have hrel : ‖M.Cinv e‖ + ‖PP.grad E.p.u - PP.grad (PP.ustar i)‖ + ‖g‖ ≤ Cr * S := hr i
  have he : ‖M.Cinv e‖ ≤ Cr * S := by
    linarith only [hrel, norm_nonneg (PP.grad E.p.u - PP.grad (PP.ustar i)), norm_nonneg g]
  have hg : ‖g‖ ≤ Cr * S := by
    linarith only [hrel, norm_nonneg (M.Cinv e),
      norm_nonneg (PP.grad E.p.u - PP.grad (PP.ustar i))]
  have hwgrad : ‖PP.grad E.p.u - PP.grad (PP.ustar i)‖ ≤ Cr * S := by
    linarith only [hrel, norm_nonneg (M.Cinv e), norm_nonneg g]
  have havg := A.average_error_le_estimator i
  have he_norm : ‖e‖ ≤ ‖M.C‖ * Cr * S := by
    calc ‖e‖ = ‖M.C (M.Cinv e)‖ := by rw [M.C_Cinv]
      _ ≤ ‖M.C‖ * ‖M.Cinv e‖ := M.C.le_opNorm _
      _ ≤ ‖M.C‖ * (Cr * S) := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ = ‖M.C‖ * Cr * S := by ring
  have hvgrad : ‖PP.grad v‖ ≤ (Cr + a) * S := by
    have hsplit : PP.grad v = (PP.grad E.p.u - PP.grad (PP.ustar i))
        + (PP.grad (PP.ustar i) - PP.grad (A.avg i (PP.ustar i))) := by
      dsimp [v]
      rw [map_sub]
      abel
    rw [hsplit]
    exact (norm_add_le _ _).trans ((add_le_add hwgrad havg.2).trans (by
      nlinarith only [mul_le_mul_of_nonneg_left hηS ha]))
  -- Split the divergence pairing at the conforming average.
  have hv : v ∈ A.V := A.V.sub_mem A.u_mem (A.avg_mem i (PP.ustar i))
  have hpairv : |⟪div e, v⟫_ℝ| ≤ (‖M.C‖ * Cr * (Cr + a)) * S ^ 2 := by
    have hgreen : ⟪div e, v⟫_ℝ = -⟪e, PP.grad v⟫_ℝ := by linarith [A.green e v hv]
    rw [hgreen, abs_neg]
    calc |⟪e, PP.grad v⟫_ℝ| ≤ ‖e‖ * ‖PP.grad v‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖M.C‖ * Cr * S) * ((Cr + a) * S) :=
          mul_le_mul he_norm hvgrad (norm_nonneg _) (by positivity)
      _ = (‖M.C‖ * Cr * (Cr + a)) * S ^ 2 := by ring
  have hdivσ : div E.p.σ = -E.p.κ • E.p.u := by
    have h0 : ⟪div E.p.σ + E.p.κ • E.p.u, div E.p.σ + E.p.κ • E.p.u⟫_ℝ = 0 := by
      rw [inner_add_left, real_inner_smul_left, E.p.eq₂]
      ring
    rw [inner_self_eq_zero] at h0
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left h0
  have hdivnorm : ‖div e‖ ≤ ‖κs • PP.ustar i + div (E.q i).σₕ‖
      + ‖E.p.κ • E.p.u - κs • PP.ustar i‖ := by
    have hsplit : div e = -(κs • PP.ustar i + div (E.q i).σₕ)
        - (E.p.κ • E.p.u - κs • PP.ustar i) := by
      dsimp [e]
      rw [map_sub, hdivσ, neg_smul]
      abel
    rw [hsplit]
    simpa only [norm_neg] using norm_sub_le (-(κs • PP.ustar i + div (E.q i).σₕ))
      (E.p.κ • E.p.u - κs • PP.ustar i)
  have hhot_res : D.h i * ‖E.p.κ • E.p.u - κs • PP.ustar i‖ ≤ PP.hot i := by
    change D.h i * ‖E.p.κ • E.p.u - κs • PP.ustar i‖ ≤
      D.h i * ‖E.p.κ • E.p.u - κs • PP.ustar i‖
        + |(E.q i).κₕ| * ‖w‖ + |E.p.κ - (E.q i).κₕ|
    linarith [mul_nonneg (abs_nonneg (E.q i).κₕ) (norm_nonneg w),
      abs_nonneg (E.p.κ - (E.q i).κₕ)]
  have hres : D.h i * ‖κs • PP.ustar i + div (E.q i).σₕ‖
      + D.h i * ‖E.p.κ • E.p.u - κs • PP.ustar i‖ ≤ S :=
    add_le_add (A.residual_le_estimator i) hhot_res
  have hpairz : |⟪div e, z⟫_ℝ| ≤ a * S ^ 2 := by
    calc |⟪div e, z⟫_ℝ| ≤ ‖div e‖ * ‖z‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖κs • PP.ustar i + div (E.q i).σₕ‖ + ‖E.p.κ • E.p.u - κs • PP.ustar i‖)
          * (D.h i * a * A.estimator i) :=
          mul_le_mul hdivnorm havg.1 (norm_nonneg _) (by positivity)
      _ = (a * A.estimator i) * (D.h i * ‖κs • PP.ustar i + div (E.q i).σₕ‖
          + D.h i * ‖E.p.κ • E.p.u - κs • PP.ustar i‖) := by ring
      _ ≤ (a * S) * S := mul_le_mul (mul_le_mul_of_nonneg_left hηS ha) hres
          (by positivity) (mul_nonneg ha hS)
      _ = a * S ^ 2 := by ring
  have hpair : |⟪div e, w⟫_ℝ| ≤ K * S ^ 2 := by
    have hw : w = v - z := by dsimp [w, v, z]; abel
    rw [hw, inner_sub_right]
    exact (abs_sub _ _).trans ((add_le_add hpairv hpairz).trans_eq (by dsimp [K]; ring))
  -- Bound the other terms in the eigenvalue identity by reliability.
  have hξ : ‖M.Cinv e + g‖ ≤ Cr * S := by
    apply (norm_add_le _ _).trans
    linarith only [hrel, norm_nonneg (PP.grad E.p.u - PP.grad (PP.ustar i))]
  have henergy : |energy M.C (M.Cinv e + g)| ≤ ‖M.C‖ * Cr ^ 2 * S ^ 2 := by
    rw [abs_of_nonneg (show 0 ≤ energy M.C (M.Cinv e + g) from M.nonneg _)]
    calc energy M.C (M.Cinv e + g)
        ≤ ‖M.C (M.Cinv e + g)‖ * ‖M.Cinv e + g‖ := real_inner_le_norm _ _
      _ ≤ (‖M.C‖ * ‖M.Cinv e + g‖) * ‖M.Cinv e + g‖ :=
          mul_le_mul_of_nonneg_right (M.C.le_opNorm _) (norm_nonneg _)
      _ = ‖M.C‖ * ‖M.Cinv e + g‖ ^ 2 := by ring
      _ ≤ ‖M.C‖ * (Cr * S) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hξ 2) (norm_nonneg _)
      _ = ‖M.C‖ * Cr ^ 2 * S ^ 2 := by ring
  have hrotation : |2 * μ * ‖g‖ ^ 2| ≤ 2 * |μ| * Cr ^ 2 * S ^ 2 := by
    rw [abs_mul, abs_mul, abs_two, abs_of_nonneg (sq_nonneg ‖g‖)]
    calc 2 * |μ| * ‖g‖ ^ 2 ≤ 2 * |μ| * (Cr * S) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hg 2) (by positivity)
      _ = 2 * |μ| * Cr ^ 2 * S ^ 2 := by ring
  have hlast : |2 * ⟪(κs - E.p.κ) • E.p.u, w⟫_ℝ| ≤ 2 * δ * ‖w‖ := by
    rw [real_inner_smul_left, abs_mul, abs_mul, abs_two, abs_sub_comm κs E.p.κ]
    have h := abs_real_inner_le_norm E.p.u w
    rw [E.u_norm, one_mul] at h
    have hmul := mul_le_mul_of_nonneg_left h (abs_nonneg (E.p.κ - κs))
    dsimp [δ]
    linarith only [hmul]
  have hid := postprocessed_eigenvalue_identity E.p (E.q i) (D.S_le i) (D.Xh_le i)
    E.u_norm (A.ustar_ne i) (PP.proj i) (D.div_mem i _ (E.q i).σₕ_mem)
  have hidentity : δ ≤ B * S ^ 2 + |κs| * ‖w‖ ^ 2 + 2 * δ * ‖w‖ := by
    change E.p.κ - κs = energy M.C (M.Cinv e + g) - 2 * μ * ‖g‖ ^ 2
      + κs * ‖w‖ ^ 2 + 2 * ⟪div e, w⟫_ℝ - 2 * ⟪(κs - E.p.κ) • E.p.u, w⟫_ℝ at hid
    have htri : ∀ b c d f g : ℝ, |b - c + d + f - g| ≤ |b| + |c| + |d| + |f| + |g| := by
      intro b c d f g
      have hab : ∀ x y : ℝ, |x + y| ≤ |x| + |y| := fun x y => by
        simpa [sub_neg_eq_add] using abs_sub x (-y)
      linarith [abs_sub (b - c + d + f) g, hab (b - c + d) f, hab (b - c) d, abs_sub b c]
    have h := (congrArg abs hid).trans_le (htri _ _ _ _ _)
    rw [abs_mul κs, abs_of_nonneg (sq_nonneg ‖w‖), abs_mul 2, abs_two] at h
    have hpair2 := mul_le_mul_of_nonneg_left hpair (show (0 : ℝ) ≤ 2 by norm_num)
    dsimp [δ, B] at *
    nlinarith only [h, henergy, hrotation, hlast, hpair2]
  have hδ : 0 ≤ δ := abs_nonneg _
  have hfinal : δ ≤ (2 * B + |E.p.κ| + 3) * (T + ‖w‖ ^ 2 + δ ^ 2) := by
    by_cases hsmall : δ < 1
    · have hκ : |κs| ≤ |E.p.κ| + 1 := by
        have ht := abs_sub E.p.κ (E.p.κ - κs)
        rw [sub_sub_cancel] at ht
        linarith only [ht, hsmall]
      have hκw := mul_le_mul_of_nonneg_right hκ (sq_nonneg ‖w‖)
      have hBS := mul_le_mul_of_nonneg_left hSsq hB
      have hyoung : 2 * δ * ‖w‖ ≤ δ ^ 2 + ‖w‖ ^ 2 := by
        nlinarith only [sq_nonneg (δ - ‖w‖)]
      have hbound : δ ≤ 2 * B * T + (|E.p.κ| + 2) * ‖w‖ ^ 2 + δ ^ 2 := by
        nlinarith only [hidentity, hκw, hBS, hyoung]
      have h1 : 2 * B * T ≤ (2 * B + |E.p.κ| + 3) * T :=
        mul_le_mul_of_nonneg_right (by linarith [abs_nonneg E.p.κ]) hT
      have h2 : (|E.p.κ| + 2) * ‖w‖ ^ 2 ≤ (2 * B + |E.p.κ| + 3) * ‖w‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      have h3 : δ ^ 2 ≤ (2 * B + |E.p.κ| + 3) * δ ^ 2 :=
        le_mul_of_one_le_left (sq_nonneg _) (by linarith [abs_nonneg E.p.κ])
      nlinarith only [hbound, h1, h2, h3]
    · have hlarge : 1 ≤ δ := le_of_not_gt hsmall
      have hsquare : δ ≤ δ ^ 2 := by nlinarith only [hlarge]
      have h1 : δ ^ 2 ≤ T + ‖w‖ ^ 2 + δ ^ 2 := by linarith [sq_nonneg ‖w‖]
      exact hsquare.trans (h1.trans (le_mul_of_one_le_left (by positivity)
        (by linarith [abs_nonneg E.p.κ])))
  simpa only [δ, κs, T, w, sq_abs] using hfinal

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

end

end MixedElasticEigenvalues
