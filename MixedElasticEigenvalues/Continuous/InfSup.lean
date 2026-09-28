import MixedElasticEigenvalues.Statements.Framework

/-!
# Proposition 2.1 and the continuous inf-sup condition (13) (p. 13, [5, Proposition 2])

For every `v ∈ U` and `η ∈ X` there is `τ ∈ Σ₀` with
`b(τ, v) + c(η, τ) = (div τ, v)₀ + (τ, η)₀ = ‖v‖₀² + ‖η‖₀²` and
`‖τ‖_{H(div)} ≤ C (‖v‖₀ + ‖η‖₀)`.

As for the rest of the project, the spaces are abstract and the analytic input is a
typed hypothesis (`InfSupData`), with a complete proof from it. The input consists of
the two liftings that also drive the discrete construction of Section 3 (pp. 17–18):

* `divLift` — `div : Σ₀ → U` has a bounded right inverse. This is the inf-sup
  condition of the stress–displacement formulation, which the thesis takes for granted
  (p. 17, with reference to [4]);
* `skewLift` — every skew part can be realized by a divergence-free stress: for each
  `g` there is `τ ∈ Σ₀` with `div τ = 0`, `(τ, η)₀ = (g, η)₀` for all `η ∈ X`, and
  `‖τ‖₀ ≲ ‖g‖₀`. In the thesis this is the `Curl` of the solution of an auxiliary Stokes
  problem, using (28) `(Curl ψ, S₂(q))₀ = (q, div ψ)₀` and (30) `div Curl ψ = 0`.

Given these, `τ = τ₁ + τ₂` with `div τ₁ = v` and `τ₂` the skew correction of `η - τ₁`
has divergence `v` and skew part `η`, which is Proposition 2.1 in a slightly stronger
form (`infsup_lift`). The continuous inf-sup condition (13) follows.

## Erratum

Proposition 2.1 asserts `τ ∈ Σ_g`. For `g ≠ 0` this cannot hold together with the bound
`‖τ‖_{H(div)} ≤ C (‖v‖₀ + ‖η‖₀)`: for `v = η = 0` it forces `τ = 0 ∉ Σ_g`. The correct
space, as in [5, Proposition 2] and in the inf-sup condition, is the test space `Σ₀`;
this is what is formalized. Likewise (13) as printed has `τ` outside the supremum; it is
the condition `inf_{v, η} sup_{τ} (b(τ, v) + c(η, τ)) / (‖τ‖_{H(div)} (‖v‖₀ + ‖η‖₀)) ≥ β`,
the continuous analogue of (20), which is `continuous_infsup`.
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace

noncomputable section

variable {H U : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The analytic input of Proposition 2.1, see the module docstring. -/
structure InfSupData (div : H →ₗ[ℝ] U) (X S₀ : Submodule ℝ H) where
  C₁ : ℝ
  C₁_nonneg : 0 ≤ C₁
  /-- `div : Σ₀ → U` has a bounded right inverse. -/
  divLift : ∀ v : U, ∃ τ ∈ S₀, div τ = v ∧ ‖τ‖ ≤ C₁ * ‖v‖
  C₂ : ℝ
  C₂_nonneg : 0 ≤ C₂
  /-- Divergence-free stresses realize every skew part. -/
  skewLift : ∀ g : H, ∃ τ ∈ S₀, div τ = 0 ∧ (∀ η ∈ X, ⟪τ, η⟫_ℝ = ⟪g, η⟫_ℝ) ∧ ‖τ‖ ≤ C₂ * ‖g‖

variable {div : H →ₗ[ℝ] U} {X S₀ : Submodule ℝ H}

/-- Proposition 2.1 in its strong form: for `v ∈ U`, `η ∈ X` there is `τ ∈ Σ₀` with
`div τ = v`, skew part `η` (i.e. `(τ, η')₀ = (η, η')₀` for all `η' ∈ X`) and
`‖τ‖_{H(div)} ≤ C (‖v‖₀ + ‖η‖₀)`. -/
theorem infsup_lift (hyp : InfSupData div X S₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : U, ∀ η ∈ X, ∃ τ ∈ S₀, div τ = v ∧
      (∀ η' ∈ X, ⟪τ, η'⟫_ℝ = ⟪η, η'⟫_ℝ) ∧ hdivNorm div τ ≤ C * (‖v‖ + ‖η‖) := by
  have h1 := hyp.C₁_nonneg
  have h2 := hyp.C₂_nonneg
  refine ⟨1 + hyp.C₁ + hyp.C₂ * hyp.C₁ + hyp.C₂, by positivity, fun v η _ => ?_⟩
  obtain ⟨τ₁, hτ₁, hdiv₁, hb₁⟩ := hyp.divLift v
  obtain ⟨τ₂, hτ₂, hdiv₂, hskew₂, hb₂⟩ := hyp.skewLift (η - τ₁)
  have hdiv : div (τ₁ + τ₂) = v := by rw [map_add, hdiv₁, hdiv₂, add_zero]
  refine ⟨τ₁ + τ₂, S₀.add_mem hτ₁ hτ₂, hdiv, fun η' hη' => ?_, ?_⟩
  · rw [inner_add_left, hskew₂ η' hη', inner_sub_left]
    ring
  · have hb₂' : ‖τ₂‖ ≤ hyp.C₂ * (‖η‖ + hyp.C₁ * ‖v‖) :=
      le_trans hb₂ (mul_le_mul_of_nonneg_left
        (le_trans (norm_sub_le _ _) (by linarith)) h2)
    have hsum := norm_add_le τ₁ τ₂
    unfold hdivNorm
    rw [hdiv]
    have hv := norm_nonneg v
    have hη := norm_nonneg η
    linarith [mul_nonneg h2 hv, mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + hyp.C₁ + hyp.C₂ * hyp.C₁) hη]

/-- **Proposition 2.1** (p. 13, [5, Proposition 2]): for all `v ∈ U` and `η ∈ X` there is
`τ ∈ Σ₀` with `b(τ, v) + c(η, τ) = ‖v‖₀² + ‖η‖₀²` and `‖τ‖_{H(div)} ≤ C (‖v‖₀ + ‖η‖₀)`
(with `Σ₀` in place of `Σ_g`, see the erratum). -/
theorem prop_2_1 (hyp : InfSupData div X S₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : U, ∀ η ∈ X, ∃ τ ∈ S₀,
      ⟪div τ, v⟫_ℝ + ⟪τ, η⟫_ℝ = ‖v‖ ^ 2 + ‖η‖ ^ 2 ∧ hdivNorm div τ ≤ C * (‖v‖ + ‖η‖) := by
  obtain ⟨C, hC, h⟩ := infsup_lift hyp
  refine ⟨C, hC, fun v η hη => ?_⟩
  obtain ⟨τ, hτ, hdiv, hskew, hb⟩ := h v η hη
  exact ⟨τ, hτ, by rw [hdiv, hskew η hη, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq], hb⟩

/-- The continuous inf-sup condition (13) (p. 13), in the form of the discrete condition
(20): there is `β > 0` such that for all `v ∈ U`, `η ∈ X` some `τ ∈ Σ₀` satisfies
`β ‖τ‖_{H(div)} (‖v‖₀ + ‖η‖₀) ≤ b(τ, v) + c(η, τ)`. -/
theorem continuous_infsup (hyp : InfSupData div X S₀) :
    ∃ β : ℝ, 0 < β ∧ ∀ v : U, ∀ η ∈ X, ∃ τ ∈ S₀,
      β * hdivNorm div τ * (‖v‖ + ‖η‖) ≤ ⟪div τ, v⟫_ℝ + ⟪τ, η⟫_ℝ := by
  obtain ⟨C, hC, h⟩ := prop_2_1 hyp
  refine ⟨1 / (2 * (C + 1)), by positivity, fun v η hη => ?_⟩
  obtain ⟨τ, hτ, heq, hb⟩ := h v η hη
  refine ⟨τ, hτ, ?_⟩
  rw [heq]
  have hs : (0 : ℝ) ≤ ‖v‖ + ‖η‖ := by positivity
  have h1 : hdivNorm div τ * (‖v‖ + ‖η‖) ≤ C * (‖v‖ + ‖η‖) * (‖v‖ + ‖η‖) :=
    mul_le_mul_of_nonneg_right hb hs
  have h2 : (‖v‖ + ‖η‖) ^ 2 ≤ 2 * (‖v‖ ^ 2 + ‖η‖ ^ 2) := by
    linarith [sq_nonneg (‖v‖ - ‖η‖)]
  have h3 : hdivNorm div τ * (‖v‖ + ‖η‖) ≤ 2 * (C + 1) * (‖v‖ ^ 2 + ‖η‖ ^ 2) := by
    have h4 := mul_le_mul_of_nonneg_left h2 hC
    nlinarith [h1, h4, sq_nonneg ‖v‖, sq_nonneg ‖η‖]
  have hpos : (0 : ℝ) < 2 * (C + 1) := by positivity
  calc 1 / (2 * (C + 1)) * hdivNorm div τ * (‖v‖ + ‖η‖)
      = (hdivNorm div τ * (‖v‖ + ‖η‖)) / (2 * (C + 1)) := by ring
    _ ≤ (2 * (C + 1) * (‖v‖ ^ 2 + ‖η‖ ^ 2)) / (2 * (C + 1)) := by gcongr
    _ = ‖v‖ ^ 2 + ‖η‖ ^ 2 := mul_div_cancel_left₀ _ hpos.ne'

/-- The hypotheses of Proposition 2.1 are satisfiable: `H = U = ℝ`, `div = id`, `Σ₀ = ℝ`,
`X = 0`. -/
example : InfSupData (LinearMap.id : ℝ →ₗ[ℝ] ℝ) ⊥ ⊤ where
  C₁ := 1
  C₁_nonneg := zero_le_one
  divLift := fun v => ⟨v, Submodule.mem_top, rfl, by simp⟩
  C₂ := 0
  C₂_nonneg := le_rfl
  skewLift := fun g => ⟨0, Submodule.zero_mem _, map_zero _, fun η hη => by
    simp [(Submodule.mem_bot ℝ).mp hη], by simp⟩

end

end MixedElasticEigenvalues
