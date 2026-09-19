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

/-! ### `L²`-projections

An `L²`-projection onto a subspace `S` is characterized by membership in `S` and
orthogonality of the residual to `S` (p. 36). That characterization determines it
uniquely, fixes the elements of `S` and makes it additive on differences — the only
properties of `Pₕ`, `P*ₕ`, `P̃ₕ` used below. -/

section Projections

variable {S : Submodule ℝ U}

/-- Two elements of `S` whose residuals are both orthogonal to `S` coincide. -/
theorem proj_unique {v z₁ z₂ : U} (h₁ : z₁ ∈ S) (h₂ : z₂ ∈ S)
    (ho₁ : ∀ w ∈ S, ⟪v - z₁, w⟫_ℝ = 0) (ho₂ : ∀ w ∈ S, ⟪v - z₂, w⟫_ℝ = 0) : z₁ = z₂ := by
  have hmem : z₁ - z₂ ∈ S := S.sub_mem h₁ h₂
  have key : ⟪z₁ - z₂, z₁ - z₂⟫_ℝ = 0 := by
    have hrw : ⟪z₁ - z₂, z₁ - z₂⟫_ℝ = ⟪v - z₂, z₁ - z₂⟫_ℝ - ⟪v - z₁, z₁ - z₂⟫_ℝ := by
      rw [← inner_sub_left]
      congr 1
      abel
    rw [hrw, ho₂ _ hmem, ho₁ _ hmem, sub_zero]
  exact eq_of_sub_eq_zero (inner_self_eq_zero.mp key)

/-- A projection fixes the elements of `S`. -/
theorem proj_eq_self {P : U → U} (hm : ∀ v, P v ∈ S)
    (ho : ∀ v, ∀ w ∈ S, ⟪v - P v, w⟫_ℝ = 0) {z : U} (hz : z ∈ S) : P z = z :=
  proj_unique (hm z) hz (ho z) (fun w _ => by simp)

/-- A projection is additive on differences. -/
theorem proj_sub {P : U → U} (hm : ∀ v, P v ∈ S)
    (ho : ∀ v, ∀ w ∈ S, ⟪v - P v, w⟫_ℝ = 0) (v₁ v₂ : U) : P (v₁ - v₂) = P v₁ - P v₂ := by
  refine proj_unique (hm _) (S.sub_mem (hm v₁) (hm v₂)) (ho _) (fun w hw => ?_)
  have hrw : v₁ - v₂ - (P v₁ - P v₂) = (v₁ - P v₁) - (v₂ - P v₂) := by abel
  rw [hrw, inner_sub_left, ho v₁ w hw, ho v₂ w hw, sub_zero]

end Projections

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

namespace PostprocessingRates

variable {D : DiscreteFamily div X S₀ ι} {M : MaterialOperator X μ} {E : EigenpairFamily D M}
  {PP : Postprocessing D M E} {N : SobolevNorms H U} {k : ℕ} (R : PostprocessingRates PP N k)

/-- **Equation (51)** (p. 36): `P*ₕ = Pₕ + P̃ₕ`, from the orthogonality relations together
with `U*ₕ = Uₕ + Ũₕ` and `Uₕ ⊥ Ũₕ`. -/
theorem pstar_eq (i : ι) (v : U) : R.Pstar i v = R.Ph i v + R.Ptilde i v := by
  refine proj_unique (R.Pstar_mem i v)
    ((PP.Ustar i).add_mem (PP.Uh_le i (R.Ph_mem i v)) (PP.Utilde_le i (R.Ptilde_mem i v)))
    (R.Pstar_orth i v) (fun w hw => ?_)
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := PP.Ustar_sum i w hw
  have d1 : ⟪v - (R.Ph i v + R.Ptilde i v), w₁⟫_ℝ = 0 := by
    have hrw : v - (R.Ph i v + R.Ptilde i v) = (v - R.Ph i v) - R.Ptilde i v := by abel
    rw [hrw, inner_sub_left, R.Ph_orth i v w₁ hw₁,
      PP.Utilde_orth i _ (R.Ptilde_mem i v) w₁ hw₁, sub_zero]
  have d2 : ⟪v - (R.Ph i v + R.Ptilde i v), w₂⟫_ℝ = 0 := by
    have hrw : v - (R.Ph i v + R.Ptilde i v) = (v - R.Ptilde i v) - R.Ph i v := by abel
    have hc : ⟪R.Ph i v, w₂⟫_ℝ = 0 := by
      rw [real_inner_comm]
      exact PP.Utilde_orth i w₂ hw₂ _ (R.Ph_mem i v)
    rw [hrw, inner_sub_left, R.Ptilde_orth i v w₂ hw₂, hc, sub_zero]
  rw [inner_add_right, d1, d2, add_zero]

/-- `Pₕu*ₕ = uₕ`, the first equation of the postprocessing (52). -/
theorem ph_ustar (i : ι) : R.Ph i (PP.ustar i) = (E.q i).uₕ := by
  refine proj_unique (R.Ph_mem i _) (E.q i).uₕ_mem (R.Ph_orth i _) (fun w hw => ?_)
  rw [inner_sub_left, PP.proj i w hw, sub_self]

end PostprocessingRates

/-- **Theorem 5.1** (p. 38). For `k ≥ 2`, the solution `u*ₕ` of (52) satisfies
`‖u - u*ₕ‖₀ ≤ C h^{k+2} (|u|_{k+2} + |σ|_{k+1} + |γ|_{k+1})`, provided
`σ ∈ H^{k+1}`, `u ∈ H^{k+2}`, `γ ∈ L²_skw ∩ H^{k+1}`. -/
theorem postprocessed_eigenfunction_rate {D : DiscreteFamily div X S₀ ι}
    {M : MaterialOperator X μ} {E : EigenpairFamily D M} (PP : Postprocessing D M E)
    (N : SobolevNorms H U) (k : ℕ) (R : PostprocessingRates PP N k) :
    ∃ C : ℝ, 0 < C ∧ ∀ i, ‖E.p.u - PP.ustar i‖
      ≤ C * D.h i ^ (k + 2) * (N.un (k + 2) E.p.u + N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ) := by
  -- Proof of the thesis (pp. 38–40): `u - u*ₕ = (u - P*ₕu) + (Pₕu - uₕ) + P̃ₕ(u - u*ₕ)`
  -- by (51); the first term is (57), the second is (55), and the third is bounded via
  -- Poincaré together with the identity `(∇(u - u*ₕ), ∇ṽ) = (C⁻¹(σ - σₕ) + γ - γₕ, ∇ṽ)`
  -- from (41) and (52), the inverse estimate on `U*ₕ`, (58) and the rates for `σ, γ`.
  have hC₂ := R.C₂_nonneg
  have hCinv : (0:ℝ) ≤ ‖M.Cinv‖ := norm_nonneg _
  refine ⟨(2 + R.C₂ * (3 * R.C₂ + 2 + ‖M.Cinv‖)) * R.C₂ + 1, by positivity, fun i => ?_⟩
  have hh := D.h_pos i
  have hTs := N.hn_nonneg (k + 1) E.p.σ
  have hTg := N.hn_nonneg (k + 1) E.p.γ
  have hTu := N.un_nonneg (k + 2) E.p.u
  obtain ⟨T, hT⟩ : ∃ T, T = N.un (k + 2) E.p.u + N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ :=
    ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = R.C₂ * D.h i ^ (k + 2) * T := ⟨_, rfl⟩
  rw [← hT]
  have hP0 : 0 ≤ P := by rw [hPdef, hT]; positivity
  have hpow : D.h i ^ (k + 2) = D.h i ^ (k + 1) * D.h i := by ring
  -- every rate of order `k+2` is bounded by `P`
  have key_u : ∀ x : ℝ, x ≤ R.C₂ * D.h i ^ (k + 2) * N.un (k + 2) E.p.u → x ≤ P := fun x hx =>
    hx.trans (by
      rw [hPdef, hT]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have key_sg : ∀ x : ℝ,
      x ≤ R.C₂ * D.h i ^ (k + 2) * (N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ) → x ≤ P :=
    fun x hx => hx.trans (by
      rw [hPdef, hT]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hA : ‖E.p.u - R.Pstar i E.p.u‖ ≤ P := key_u _ (R.bh i)
  have hI : ‖E.p.u - R.nodal i E.p.u‖ ≤ P := key_u _ (R.nodal_rate₀ i)
  have hB : ‖R.Ph i E.p.u - (E.q i).uₕ‖ ≤ P := key_sg _ (R.proj_rate i)
  have hgradI : D.h i * ‖PP.grad (E.p.u - R.nodal i E.p.u)‖ ≤ P := by
    refine key_u _ ?_
    calc D.h i * ‖PP.grad (E.p.u - R.nodal i E.p.u)‖
        ≤ D.h i * (R.C₂ * D.h i ^ (k + 1) * N.un (k + 2) E.p.u) :=
          mul_le_mul_of_nonneg_left (R.nodal_rate₁ i) hh.le
      _ = R.C₂ * D.h i ^ (k + 2) * N.un (k + 2) E.p.u := by rw [hpow]; ring
  have hRsg : D.h i * (‖E.p.σ - (E.q i).σₕ‖ + ‖E.p.γ - (E.q i).γₕ‖) ≤ P := by
    refine key_sg _ ?_
    calc D.h i * (‖E.p.σ - (E.q i).σₕ‖ + ‖E.p.γ - (E.q i).γₕ‖)
        ≤ D.h i * (R.C₂ * D.h i ^ (k + 1) * (N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ)) :=
          mul_le_mul_of_nonneg_left (R.rate_σγ i) hh.le
      _ = R.C₂ * D.h i ^ (k + 2) * (N.hn (k + 1) E.p.σ + N.hn (k + 1) E.p.γ) := by
          rw [hpow]; ring
  -- inverse estimates for the two discrete differences
  have hinvB : D.h i * ‖PP.grad (R.Ph i E.p.u - (E.q i).uₕ)‖ ≤ R.C₂ * P := by
    calc D.h i * ‖PP.grad (R.Ph i E.p.u - (E.q i).uₕ)‖
        ≤ R.C₂ * ‖R.Ph i E.p.u - (E.q i).uₕ‖ :=
          R.inverse i _ ((PP.Ustar i).sub_mem (PP.Uh_le i (R.Ph_mem i _))
            (PP.Uh_le i (E.q i).uₕ_mem))
      _ ≤ R.C₂ * P := mul_le_mul_of_nonneg_left hB hC₂
  have hPstarI : ‖R.Pstar i E.p.u - R.nodal i E.p.u‖ ≤ 2 * P := by
    have hrw : R.Pstar i E.p.u - R.nodal i E.p.u
        = (R.Pstar i E.p.u - E.p.u) + (E.p.u - R.nodal i E.p.u) := by abel
    have h1 : ‖R.Pstar i E.p.u - E.p.u‖ = ‖E.p.u - R.Pstar i E.p.u‖ := norm_sub_rev _ _
    calc ‖R.Pstar i E.p.u - R.nodal i E.p.u‖
        ≤ ‖R.Pstar i E.p.u - E.p.u‖ + ‖E.p.u - R.nodal i E.p.u‖ := by
          rw [hrw]; exact norm_add_le _ _
      _ ≤ 2 * P := by rw [h1]; linarith
  have hgradPstar : D.h i * ‖PP.grad (R.Pstar i E.p.u - E.p.u)‖ ≤ 2 * R.C₂ * P + P := by
    have h1 : D.h i * ‖PP.grad (R.Pstar i E.p.u - R.nodal i E.p.u)‖ ≤ 2 * R.C₂ * P := by
      calc D.h i * ‖PP.grad (R.Pstar i E.p.u - R.nodal i E.p.u)‖
          ≤ R.C₂ * ‖R.Pstar i E.p.u - R.nodal i E.p.u‖ :=
            R.inverse i _ ((PP.Ustar i).sub_mem (R.Pstar_mem i _) (R.nodal_mem i _))
        _ ≤ R.C₂ * (2 * P) := mul_le_mul_of_nonneg_left hPstarI hC₂
        _ = 2 * R.C₂ * P := by ring
    have h2 : D.h i * ‖PP.grad (R.nodal i E.p.u - E.p.u)‖ ≤ P := by
      rw [show R.nodal i E.p.u - E.p.u = -(E.p.u - R.nodal i E.p.u) by abel, map_neg, norm_neg]
      exact hgradI
    have h3 : ‖PP.grad (R.Pstar i E.p.u - E.p.u)‖
        ≤ ‖PP.grad (R.Pstar i E.p.u - R.nodal i E.p.u)‖
          + ‖PP.grad (R.nodal i E.p.u - E.p.u)‖ := by
      rw [show R.Pstar i E.p.u - E.p.u
          = (R.Pstar i E.p.u - R.nodal i E.p.u) + (R.nodal i E.p.u - E.p.u) by abel, map_add]
      exact norm_add_le _ _
    have h4 := mul_le_mul_of_nonneg_left h3 hh.le
    rw [mul_add] at h4
    linarith
  -- the three projections of the error
  have hPs : R.Pstar i (E.p.u - PP.ustar i) = R.Pstar i E.p.u - PP.ustar i := by
    rw [proj_sub (R.Pstar_mem i) (R.Pstar_orth i),
      proj_eq_self (R.Pstar_mem i) (R.Pstar_orth i) (PP.ustar_mem i)]
  have hPh : R.Ph i (E.p.u - PP.ustar i) = R.Ph i E.p.u - (E.q i).uₕ := by
    rw [proj_sub (R.Ph_mem i) (R.Ph_orth i), R.ph_ustar i]
  have h51 := R.pstar_eq i (E.p.u - PP.ustar i)
  rw [hPs, hPh] at h51
  have hdecomp : E.p.u - PP.ustar i
      = (E.p.u - R.Pstar i E.p.u) + ((R.Ph i E.p.u - (E.q i).uₕ)
        + R.Ptilde i (E.p.u - PP.ustar i)) := by
    rw [← h51]; abel
  -- the gradient of the `Ũₕ`-component
  have hvtmem : R.Ptilde i (E.p.u - PP.ustar i) ∈ PP.Utilde i := R.Ptilde_mem i _
  have hgrad_id : ⟪PP.grad (E.p.u - PP.ustar i),
        PP.grad (R.Ptilde i (E.p.u - PP.ustar i))⟫_ℝ
      = ⟪M.Cinv (E.p.σ - (E.q i).σₕ) + (E.p.γ - (E.q i).γₕ),
          PP.grad (R.Ptilde i (E.p.u - PP.ustar i))⟫_ℝ := by
    rw [map_sub, inner_sub_left, R.grad_u, PP.grad_eq i _ hvtmem, map_sub, ← inner_sub_left]
    congr 1
    abel
  have hgvec : R.Ptilde i (E.p.u - PP.ustar i)
      = (R.Pstar i E.p.u - E.p.u) + (E.p.u - PP.ustar i)
        - (R.Ph i E.p.u - (E.q i).uₕ) := by
    rw [show R.Ptilde i (E.p.u - PP.ustar i)
        = (R.Pstar i E.p.u - PP.ustar i) - (R.Ph i E.p.u - (E.q i).uₕ) by rw [h51]; abel]
    abel
  have hinner : ∀ y : H, ⟪PP.grad (R.Ptilde i (E.p.u - PP.ustar i)), y⟫_ℝ
      = ⟪PP.grad (R.Pstar i E.p.u - E.p.u), y⟫_ℝ + ⟪PP.grad (E.p.u - PP.ustar i), y⟫_ℝ
        - ⟪PP.grad (R.Ph i E.p.u - (E.q i).uₕ), y⟫_ℝ := by
    intro y
    rw [hgvec, map_sub, map_add, inner_sub_left, inner_add_left]
  obtain ⟨Bnd, hBnd⟩ : ∃ B, B = ‖PP.grad (R.Pstar i E.p.u - E.p.u)‖
      + (‖M.Cinv‖ + 1) * (‖E.p.σ - (E.q i).σₕ‖ + ‖E.p.γ - (E.q i).γₕ‖)
      + ‖PP.grad (R.Ph i E.p.u - (E.q i).uₕ)‖ := ⟨_, rfl⟩
  have hBnd0 : 0 ≤ Bnd := by
    rw [hBnd]
    have h1 : (0:ℝ) ≤ (‖M.Cinv‖ + 1) * (‖E.p.σ - (E.q i).σₕ‖ + ‖E.p.γ - (E.q i).γₕ‖) := by
      positivity
    linarith [norm_nonneg (PP.grad (R.Pstar i E.p.u - E.p.u)),
      norm_nonneg (PP.grad (R.Ph i E.p.u - (E.q i).uₕ))]
  have hnormC : ‖M.Cinv (E.p.σ - (E.q i).σₕ) + (E.p.γ - (E.q i).γₕ)‖
      ≤ (‖M.Cinv‖ + 1) * (‖E.p.σ - (E.q i).σₕ‖ + ‖E.p.γ - (E.q i).γₕ‖) := by
    have h1 := M.Cinv.le_opNorm (E.p.σ - (E.q i).σₕ)
    have h2 := norm_add_le (M.Cinv (E.p.σ - (E.q i).σₕ)) (E.p.γ - (E.q i).γₕ)
    nlinarith [norm_nonneg (E.p.σ - (E.q i).σₕ), norm_nonneg (E.p.γ - (E.q i).γₕ),
      norm_nonneg M.Cinv]
  have hgradvt : ‖PP.grad (R.Ptilde i (E.p.u - PP.ustar i))‖ ≤ Bnd := by
    have hsq : ‖PP.grad (R.Ptilde i (E.p.u - PP.ustar i))‖ ^ 2
        ≤ Bnd * ‖PP.grad (R.Ptilde i (E.p.u - PP.ustar i))‖ := by
      rw [← real_inner_self_eq_norm_sq, hinner, hgrad_id, hBnd]
      have c1 := abs_real_inner_le_norm (PP.grad (R.Pstar i E.p.u - E.p.u))
        (PP.grad (R.Ptilde i (E.p.u - PP.ustar i)))
      have c2 := abs_real_inner_le_norm (M.Cinv (E.p.σ - (E.q i).σₕ) + (E.p.γ - (E.q i).γₕ))
        (PP.grad (R.Ptilde i (E.p.u - PP.ustar i)))
      have c3 := abs_real_inner_le_norm (PP.grad (R.Ph i E.p.u - (E.q i).uₕ))
        (PP.grad (R.Ptilde i (E.p.u - PP.ustar i)))
      have c2' := mul_le_mul_of_nonneg_right hnormC
        (norm_nonneg (PP.grad (R.Ptilde i (E.p.u - PP.ustar i))))
      have l1 := le_abs_self ⟪PP.grad (R.Pstar i E.p.u - E.p.u),
        PP.grad (R.Ptilde i (E.p.u - PP.ustar i))⟫_ℝ
      have l2 := le_abs_self ⟪M.Cinv (E.p.σ - (E.q i).σₕ) + (E.p.γ - (E.q i).γₕ),
        PP.grad (R.Ptilde i (E.p.u - PP.ustar i))⟫_ℝ
      have l3 := neg_le_abs ⟪PP.grad (R.Ph i E.p.u - (E.q i).uₕ),
        PP.grad (R.Ptilde i (E.p.u - PP.ustar i))⟫_ℝ
      nlinarith [c1, c2, c3, c2', l1, l2, l3]
    rcases eq_or_lt_of_le (norm_nonneg (PP.grad (R.Ptilde i (E.p.u - PP.ustar i)))) with h0 | h0
    · rw [← h0]; exact hBnd0
    · have h2 : ‖PP.grad (R.Ptilde i (E.p.u - PP.ustar i))‖
          * ‖PP.grad (R.Ptilde i (E.p.u - PP.ustar i))‖
          ≤ Bnd * ‖PP.grad (R.Ptilde i (E.p.u - PP.ustar i))‖ := by
        rw [← pow_two]; exact hsq
      exact le_of_mul_le_mul_right h2 h0
  -- Poincaré on `Ũₕ`
  have hvtbound : ‖R.Ptilde i (E.p.u - PP.ustar i)‖
      ≤ R.C₂ * (3 * R.C₂ + 2 + ‖M.Cinv‖) * P := by
    have hp := R.poincare i _ hvtmem
    have hBd : D.h i * Bnd ≤ (3 * R.C₂ + 2 + ‖M.Cinv‖) * P := by
      rw [hBnd, mul_add, mul_add, ← mul_assoc (D.h i), mul_comm (D.h i) (‖M.Cinv‖ + 1),
        mul_assoc]
      have := hRsg
      nlinarith [hgradPstar, hinvB, hRsg, norm_nonneg M.Cinv, hP0]
    calc ‖R.Ptilde i (E.p.u - PP.ustar i)‖
        ≤ R.C₂ * D.h i * ‖PP.grad (R.Ptilde i (E.p.u - PP.ustar i))‖ := hp
      _ ≤ R.C₂ * (D.h i * Bnd) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hgradvt hh.le) hC₂
      _ ≤ R.C₂ * ((3 * R.C₂ + 2 + ‖M.Cinv‖) * P) := mul_le_mul_of_nonneg_left hBd hC₂
      _ = R.C₂ * (3 * R.C₂ + 2 + ‖M.Cinv‖) * P := by ring
  -- assembly
  have hfinal : ‖E.p.u - PP.ustar i‖
      ≤ P + (P + R.C₂ * (3 * R.C₂ + 2 + ‖M.Cinv‖) * P) := by
    calc ‖E.p.u - PP.ustar i‖
        = ‖(E.p.u - R.Pstar i E.p.u) + ((R.Ph i E.p.u - (E.q i).uₕ)
            + R.Ptilde i (E.p.u - PP.ustar i))‖ := by rw [← hdecomp]
      _ ≤ ‖E.p.u - R.Pstar i E.p.u‖ + ‖(R.Ph i E.p.u - (E.q i).uₕ)
            + R.Ptilde i (E.p.u - PP.ustar i)‖ := norm_add_le _ _
      _ ≤ ‖E.p.u - R.Pstar i E.p.u‖ + (‖R.Ph i E.p.u - (E.q i).uₕ‖
            + ‖R.Ptilde i (E.p.u - PP.ustar i)‖) := by
          have := norm_add_le (R.Ph i E.p.u - (E.q i).uₕ) (R.Ptilde i (E.p.u - PP.ustar i))
          linarith
      _ ≤ P + (P + R.C₂ * (3 * R.C₂ + 2 + ‖M.Cinv‖) * P) := by
          exact add_le_add hA (add_le_add hB hvtbound)
  have hKP : P + (P + R.C₂ * (3 * R.C₂ + 2 + ‖M.Cinv‖) * P)
      ≤ ((2 + R.C₂ * (3 * R.C₂ + 2 + ‖M.Cinv‖)) * R.C₂ + 1) * D.h i ^ (k + 2) * T := by
    have hpos : (0:ℝ) ≤ D.h i ^ (k + 2) * T := by rw [hT]; positivity
    rw [hPdef]
    nlinarith [hpos]
  linarith

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
