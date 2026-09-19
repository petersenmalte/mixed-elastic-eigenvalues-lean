import MixedElasticEigenvalues.Statements.EigenvalueRate

/-!
# Theorem 5.1: the postprocessed eigenfunction

Statement of Theorem 5.1 (p. 38) in the abstract framework (Theorem 5.7 is in
`PostprocessedEigenvalue.lean`).

* `Postprocessing` records the enriched space `U*ₕ ⊇ Uₕ`, its orthogonal complement `Ũₕ`
  (50), the broken gradient `∇_𝒯` and a postprocessed eigenfunction `u*ₕ` satisfying (52).
* `PostprocessingRates` collects the finite element facts used in the proof of Theorem
  5.1: the projection estimate (55), Bramble–Hilbert (57), the nodal interpolation
  estimates (58), the local Poincaré inequality and inverse estimate (pp. 38–39), the
  stress/skew rates of Theorem 4.8, and the identity (41) `∇u = C⁻¹σ + γ`.

Existence and uniqueness of the postprocessing (52), discussed on pp. 37–38 via the
LBB condition, is not formalized: `u*ₕ` is part of the data.
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace
open Filter Topology

noncomputable section

variable {H U : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] {ι : Type*}
  {div : H →ₗ[ℝ] U} {X S₀ : Submodule ℝ H} {μ : ℝ}

/-- The local postprocessing (52)/(53) of Section 5.1 on every mesh `i`: the enriched space
`U*ₕ ⊇ Uₕ`, the `L²`-orthogonal complement `Ũₕ` of `Uₕ` in `U*ₕ` (50)–(51), the broken
gradient `∇_𝒯 : U*ₕ → H` (a linear map on `U`, only used on `U*ₕ` and on the smooth `u`),
and the postprocessed eigenfunction `u*ₕ ∈ U*ₕ` with `Pₕu*ₕ = uₕ` and
`(∇u*ₕ, ∇vₕ) = (C⁻¹σₕ + γₕ, ∇vₕ)` for all `vₕ ∈ Ũₕ`. -/
structure Postprocessing (D : DiscreteFamily div X S₀ ι) (M : MaterialOperator X μ)
    (E : EigenpairFamily D M) where
  Ustar : ι → Submodule ℝ U
  Uh_le : ∀ i, D.Uh i ≤ Ustar i
  Utilde : ι → Submodule ℝ U
  Utilde_le : ∀ i, Utilde i ≤ Ustar i
  Utilde_orth : ∀ i, ∀ v ∈ Utilde i, ∀ w ∈ D.Uh i, ⟪v, w⟫_ℝ = 0
  Ustar_sum : ∀ i, ∀ v ∈ Ustar i, ∃ w ∈ D.Uh i, ∃ vt ∈ Utilde i, v = w + vt
  grad : U →ₗ[ℝ] H
  ustar : ι → U
  ustar_mem : ∀ i, ustar i ∈ Ustar i
  proj : ∀ i, ∀ w ∈ D.Uh i, ⟪ustar i, w⟫_ℝ = ⟪(E.q i).uₕ, w⟫_ℝ
  grad_eq : ∀ i, ∀ v ∈ Utilde i,
    ⟪grad (ustar i), grad v⟫_ℝ = ⟪M.Cinv (E.q i).σₕ + (E.q i).γₕ, grad v⟫_ℝ

/-- Finite element input of Theorem 5.1 (pp. 38–40), with a common constant `C₂`:
the `L²`-projections `Pₕ, P*ₕ, P̃ₕ` (defined by their orthogonality relations, p. 36),
the estimate (55) for `‖Pₕu - uₕ‖₀`, Bramble–Hilbert (57), the nodal interpolant with
(58) for `j = 0, 1`, Poincaré's inequality on `Ũₕ`, the inverse estimate on `U*ₕ`, the
rates of Theorem 4.8 for `σ, γ`, and the identity (41) for the smooth solution. -/
structure PostprocessingRates {D : DiscreteFamily div X S₀ ι} {M : MaterialOperator X μ}
    {E : EigenpairFamily D M} (PP : Postprocessing D M E) (N : SobolevNorms H U) (k : ℕ) where
  two_le_k : 2 ≤ k
  grad_u : PP.grad E.p.u = M.Cinv E.p.σ + E.p.γ
  Ph : ι → U → U
  Ph_mem : ∀ i v, Ph i v ∈ D.Uh i
  Ph_orth : ∀ i v, ∀ w ∈ D.Uh i, ⟪v - Ph i v, w⟫_ℝ = 0
  Pstar : ι → U → U
  Pstar_mem : ∀ i v, Pstar i v ∈ PP.Ustar i
  Pstar_orth : ∀ i v, ∀ w ∈ PP.Ustar i, ⟪v - Pstar i v, w⟫_ℝ = 0
  Ptilde : ι → U → U
  Ptilde_mem : ∀ i v, Ptilde i v ∈ PP.Utilde i
  Ptilde_orth : ∀ i v, ∀ w ∈ PP.Utilde i, ⟪v - Ptilde i v, w⟫_ℝ = 0
  C₂ : ℝ
  C₂_nonneg : 0 ≤ C₂
  proj_rate : ∀ i, ‖Ph i E.p.u - (E.q i).uₕ‖
    ≤ C₂ * D.h i ^ (k + 2) * (N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ)
  bh : ∀ i, ‖E.p.u - Pstar i E.p.u‖ ≤ C₂ * D.h i ^ (k + 2) * N.un (k + 2) E.p.u
  nodal : ι → U → U
  nodal_mem : ∀ i v, nodal i v ∈ PP.Ustar i
  nodal_rate₀ : ∀ i, ‖E.p.u - nodal i E.p.u‖ ≤ C₂ * D.h i ^ (k + 2) * N.un (k + 2) E.p.u
  nodal_rate₁ : ∀ i, ‖PP.grad (E.p.u - nodal i E.p.u)‖
    ≤ C₂ * D.h i ^ (k + 1) * N.un (k + 2) E.p.u
  poincare : ∀ i, ∀ v ∈ PP.Utilde i, ‖v‖ ≤ C₂ * D.h i * ‖PP.grad v‖
  inverse : ∀ i, ∀ v ∈ PP.Ustar i, D.h i * ‖PP.grad v‖ ≤ C₂ * ‖v‖
  rate_σγ : ∀ i, ‖E.p.σ - (E.q i).σₕ‖ + ‖E.p.γ - (E.q i).γₕ‖
    ≤ C₂ * D.h i ^ (k + 1) * (N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ)

/-- **Theorem 5.1** (p. 38). For `k ≥ 2`, the solution `u*ₕ` of (52) satisfies
`‖u - u*ₕ‖₀ ≤ C h^{k+2} (|u|_{k+2} + |σ|_{k+1} + |γ|_{k+1})`, provided
`σ ∈ H^{k+1}`, `u ∈ H^{k+2}`, `γ ∈ L²_skw ∩ H^{k+1}`. -/
theorem postprocessed_eigenfunction_rate {D : DiscreteFamily div X S₀ ι}
    {M : MaterialOperator X μ} {E : EigenpairFamily D M} (PP : Postprocessing D M E)
    (N : SobolevNorms H U) (k : ℕ) (R : PostprocessingRates PP N k) :
    ∃ C : ℝ, 0 < C ∧ ∀ i, ‖E.p.u - PP.ustar i‖
      ≤ C * D.h i ^ (k + 2) * (N.un (k + 2) E.p.u + N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ) := by
  -- Not proved here. Proof of the thesis (pp. 38–40): `‖u - u*ₕ‖ ≤ ‖u - P*ₕu‖ +
  -- ‖Pₕ(u - u*ₕ)‖ + ‖P̃ₕ(u - u*ₕ)‖` using `P*ₕ = Pₕ + P̃ₕ` (51) (provable from the
  -- orthogonality relations and `Ustar_sum`); the first term is (57), the second equals
  -- `‖Pₕu - uₕ‖` by `proj` and is (55), the third is bounded via Poincaré, the identity
  -- `(∇(u - u*ₕ), ∇ṽ) = (C⁻¹(σ - σₕ) + γ - γₕ, ∇ṽ)` from (41) and (52), the inverse
  -- estimate on `U*ₕ`, (58) and the rates for `σ, γ`.
  sorry

/-- The hypotheses of Theorem 5.1 are satisfiable: in the trivial model the
postprocessing is `U*ₕ = Uₕ = ℝ`, `Ũₕ = ⊥`, `∇ = -id`, `u*ₕ = uₕ = 1`, and every error
vanishes. -/
def trivialPostprocessing (μ : ℝ) (E : EigenpairFamily trivialFamily (trivialMaterial μ))
    (hq : ∀ n, E.q n = trivialDiscreteEigenpair μ n) :
    Postprocessing trivialFamily (trivialMaterial μ) E where
  Ustar := fun _ => ⊤
  Uh_le := fun _ => le_rfl
  Utilde := fun _ => ⊥
  Utilde_le := fun _ => bot_le
  Utilde_orth := fun _ v hv _ _ => by simp [(Submodule.mem_bot ℝ).mp hv]
  Ustar_sum := fun _ v _ => ⟨v, Submodule.mem_top, 0, Submodule.zero_mem _, by simp⟩
  grad := -LinearMap.id
  ustar := fun _ => 1
  ustar_mem := fun _ => Submodule.mem_top
  proj := fun n w _ => by simp [hq, trivialDiscreteEigenpair]
  grad_eq := fun n v hv => by simp [(Submodule.mem_bot ℝ).mp hv]

example (μ : ℝ) (k : ℕ) (hk : 2 ≤ k) (E : EigenpairFamily trivialFamily (trivialMaterial μ))
    (hp : E.p = trivialEigenpair μ) (hq : ∀ n, E.q n = trivialDiscreteEigenpair μ n) :
    PostprocessingRates (trivialPostprocessing μ E hq) trivialSobolev k where
  two_le_k := hk
  grad_u := by simp [trivialPostprocessing, hp, trivialEigenpair, trivialMaterial]
  Ph := fun _ v => v
  Ph_mem := fun _ _ => Submodule.mem_top
  Ph_orth := fun _ _ _ _ => by simp
  Pstar := fun _ v => v
  Pstar_mem := fun _ _ => Submodule.mem_top
  Pstar_orth := fun _ _ _ _ => by simp
  Ptilde := fun _ _ => 0
  Ptilde_mem := fun _ _ => Submodule.zero_mem _
  Ptilde_orth := fun _ _ _ hw => by simp [(Submodule.mem_bot ℝ).mp hw]
  C₂ := 1
  C₂_nonneg := zero_le_one
  proj_rate := fun n => by
    simp only [hp, hq, trivialEigenpair, trivialDiscreteEigenpair, sub_self, norm_zero,
      trivialSobolev]
    have := trivialFamily.h_pos n
    positivity
  bh := fun n => by have := trivialFamily.h_pos n; simp [trivialSobolev]; positivity
  nodal := fun _ v => v
  nodal_mem := fun _ _ => Submodule.mem_top
  nodal_rate₀ := fun n => by have := trivialFamily.h_pos n; simp [trivialSobolev]; positivity
  nodal_rate₁ := fun n => by have := trivialFamily.h_pos n; simp [trivialSobolev]; positivity
  poincare := fun n v hv => by simp [(Submodule.mem_bot ℝ).mp hv]
  inverse := fun n v _ => by
    simp only [trivialPostprocessing, LinearMap.neg_apply, LinearMap.id_coe, id_eq, norm_neg,
      one_mul]
    have h1 : trivialFamily.h n ≤ 1 := by
      simp only [trivialFamily]
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact mul_le_of_le_one_left (norm_nonneg v) h1
  rate_σγ := fun n => by
    simp only [hp, hq, trivialEigenpair, trivialDiscreteEigenpair, sub_self, norm_zero,
      add_zero, trivialSobolev]
    have := trivialFamily.h_pos n
    positivity

end

end MixedElasticEigenvalues
