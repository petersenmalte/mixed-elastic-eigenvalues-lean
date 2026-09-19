import MixedElasticEigenvalues.Statements.Postprocessing

/-!
# Theorems 6.2 and 6.4: a posteriori error estimation

Statements of Theorem 6.2 (reliability of the estimator `η`, p. 48) and Theorem 6.4
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
  stab : ∀ s, ∀ v ∈ V, ∀ g ∈ X, ‖M.Cinv s‖ + ‖PP.grad v‖ + ‖g‖
    ≤ Cst * (‖M.Cinv s - PP.grad v + g‖ + resG s + ‖skw s‖)
  sz : ι → U → U
  sz_mem : ∀ i, ∀ v ∈ V, sz i v ∈ V ⊓ D.Uh i
  Csz : ℝ
  sz_approx : ∀ i, ∀ v ∈ V, ‖v - sz i v‖ ≤ Csz * D.h i * ‖PP.grad v‖
  sz_stable : ∀ i, ∀ v ∈ V, ‖sz i v‖ ≤ Csz * ‖PP.grad v‖
  jump : ι → U → ℝ
  jump_nonneg : ∀ i v, 0 ≤ jump i v
  avg : ι → U → U
  avg_mem : ∀ i v, avg i v ∈ V
  Cavg : ℝ
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
  -- Not proved here. Proof of the thesis (Lemma 6.1 and pp. 48–49): apply `stab` to the
  -- error `(σ - σₕ, u - ũₕ, γ - γₕ)` with the conforming average `ũₕ = avg i u*ₕ`. By
  -- (41), Gauss' theorem and (36) the three residual norms are `‖C⁻¹σₕ + γₕ - ∇ũₕ‖`,
  -- `resG (σ - σₕ)` and `‖skw σₕ‖`; `resG (σ - σₕ)` is bounded through `resG_least` by
  -- `h ‖κu + div σₕ‖ + h.o.t.` using Scott–Zhang, (37) and (52). The terms with `ũₕ` are
  -- replaced by `u*ₕ` via (67), and Jensen's inequality gives `η`.
  sorry

/-- **Theorem 6.4** (p. 50): `|κ - κ*ₕ| ≲ η² + h.o.t.` for sufficiently small `h`, where
the higher-order terms are `(h.o.t.)²` of Theorem 6.2, `‖u - u*ₕ‖₀²` and `(κ - κ*ₕ)²`. -/
theorem eigenvalue_reliability : ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 < C ∧ ∀ i, D.h i ≤ h₀ →
    |E.p.κ - PP.κstar i| ≤ C * (A.estimatorSq i + PP.hot i ^ 2 + ‖E.p.u - PP.ustar i‖ ^ 2
      + (E.p.κ - PP.κstar i) ^ 2) := by
  -- Not proved here. Proof of the thesis: Lemma 5.6 (`postprocessed_eigenvalue_identity`)
  -- with `u - u*ₕ = (u - ũₕ) + (ũₕ - u*ₕ)`, Gauss' theorem for the term
  -- `(div(σ - σₕ), u - ũₕ)`, Young's inequality, Theorem 6.2 and (67); the restriction
  -- `h ≤ h₀` (with `h₀ ≤ 1`) absorbs `h² Σ_E h_E⁻¹‖[u*ₕ]‖²` into `η²`.
  sorry

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
  avg_est := fun n v _ => by simp
  ustar_ne := fun _ => by simp [trivialPostprocessing]

end

end MixedElasticEigenvalues
