import Mathlib

/-!
# Abstract eigenvalue identities (thesis Lemma 4.9, Definition 5.5, Lemma 5.6)

Both lemmas are purely algebraic consequences of the variational equations (36), (37)
and (53) in an inner product space; no PDE, mesh or finite element enters. We formalize
them in this abstract setting:

* `H` is a real inner product space (the tensors, `L²(Ω; ℝ²ˣ²)` in the thesis);
* `U` is a real inner product space (the displacements, `L²(Ω; ℝ²)`);
* `div : H →ₗ[ℝ] U` is a linear map (the divergence; only its linearity is used, so we
  take it to be defined on all of `H` instead of on `Σ = H(div)`);
* `X : Submodule ℝ H` is the space of skew-symmetric tensors, equation (9);
* `S₀ : Submodule ℝ H` is the test space of the first equation of (36);
* `M : MaterialOperator X μ` bundles `C : H →L[ℝ] H` and `C⁻¹` with the properties
  used in Chapters 4 and 5: symmetry, invertibility and `C η = 2μ η` on `X`.

Instead of the operator square roots `C^{±1/2}` of the thesis we work with the quadratic
forms `energy C ξ = ⟪C ξ, ξ⟫ = ‖ξ‖²_{C^{1/2}}` and `⟪C⁻¹ τ, τ⟫ = ‖τ‖²_{C^{-1/2}}`
directly (definition (5), p. 10), which avoids the functional calculus entirely.

## Erratum

In the proof of Lemma 5.6 (p. 41) the first display ends with `+ (γ, σₕ)`; the correct
term is `+ 2(γ, σₕ)` (as in the proof of Lemma 4.9, p. 30). The typo does not propagate:
the following line of the thesis and the identity (60) itself are correct, and (60) is
what `postprocessed_eigenvalue_identity` below proves.
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace

variable {H U : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The material operator `C` together with its inverse `C⁻¹`, with the properties used in
Chapters 4 and 5 of the thesis: symmetry with respect to the inner product, `C ∘ C⁻¹ = id`,
`C⁻¹ ∘ C = id`, positivity, and `C η = 2μ η` for skew-symmetric `η ∈ X` (p. 30). -/
structure MaterialOperator (X : Submodule ℝ H) (μ : ℝ) where
  /-- The material tensor `C`. -/
  C : H →L[ℝ] H
  /-- The inverse material tensor `C⁻¹`. -/
  Cinv : H →L[ℝ] H
  symm : ∀ x y : H, ⟪C x, y⟫_ℝ = ⟪x, C y⟫_ℝ
  C_Cinv : ∀ x : H, C (Cinv x) = x
  Cinv_C : ∀ x : H, Cinv (C x) = x
  nonneg : ∀ x : H, 0 ≤ ⟪C x, x⟫_ℝ
  skew : ∀ η ∈ X, C η = (2 * μ) • η

namespace MaterialOperator

variable {X : Submodule ℝ H} {μ : ℝ} (M : MaterialOperator X μ)

/-- `C⁻¹` is symmetric as well, equation (6). -/
theorem Cinv_symm (x y : H) : ⟪M.Cinv x, y⟫_ℝ = ⟪x, M.Cinv y⟫_ℝ := by
  have h := M.symm (M.Cinv x) (M.Cinv y)
  rw [M.C_Cinv, M.C_Cinv] at h
  exact h.symm

/-- `2μ C⁻¹ η = η` for skew-symmetric `η`. -/
theorem smul_Cinv_of_mem {η : H} (hη : η ∈ X) : (2 * μ) • M.Cinv η = η := by
  have h := M.Cinv_C η
  rwa [M.skew η hη, map_smul] at h

end MaterialOperator

/-- The quadratic form `energy T ξ = ⟪T ξ, ξ⟫`. For `T = C` this is `‖ξ‖²_{C^{1/2}}` and for
`T = C⁻¹` it is `‖ξ‖²_{C^{-1/2}}` in the notation (5) of the thesis. -/
def energy (T : H →L[ℝ] H) (ξ : H) : ℝ := ⟪T ξ, ξ⟫_ℝ

/-- Expansion of `‖C⁻¹ e + d‖²_{C^{1/2}}` for skew-symmetric `d`, the computation on p. 30:
`‖C⁻¹ e + d‖²_{C^{1/2}} = ‖e‖²_{C^{-1/2}} + 2 (e, d) + 2μ ‖d‖²`. -/
theorem energy_Cinv_add {X : Submodule ℝ H} {μ : ℝ} (M : MaterialOperator X μ) (e : H)
    {d : H} (hd : d ∈ X) :
    energy M.C (M.Cinv e + d) = ⟪M.Cinv e, e⟫_ℝ + 2 * ⟪e, d⟫_ℝ + 2 * μ * ‖d‖ ^ 2 := by
  have hCd : M.C d = (2 * μ) • d := M.skew d hd
  have h1 : ⟪M.C d, M.Cinv e⟫_ℝ = ⟪d, e⟫_ℝ := by rw [M.symm, M.C_Cinv]
  have h2 : ⟪M.C d, d⟫_ℝ = 2 * μ * ‖d‖ ^ 2 := by
    rw [hCd, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have h3 : ⟪e, M.Cinv e⟫_ℝ = ⟪M.Cinv e, e⟫_ℝ := real_inner_comm _ _
  have h4 : ⟪d, e⟫_ℝ = ⟪e, d⟫_ℝ := real_inner_comm _ _
  unfold energy
  rw [map_add, M.C_Cinv, inner_add_left, inner_add_right, inner_add_right, h1, h2, h3, h4]
  ring

/-- A solution `(κ, σ, u, γ)` of the continuous eigenvalue problem (36) (p. 26), where the
first equation is tested with `τ ∈ S₀` and the third with `η ∈ X`. -/
structure MixedEigenpair (div : H →ₗ[ℝ] U) (X S₀ : Submodule ℝ H) {μ : ℝ}
    (M : MaterialOperator X μ) where
  κ : ℝ
  σ : H
  u : U
  γ : H
  σ_mem : σ ∈ S₀
  γ_mem : γ ∈ X
  /-- `(C⁻¹σ, τ) + (div τ, u) + (γ, τ) = 0` for all `τ ∈ S₀`. -/
  eq₁ : ∀ τ ∈ S₀, ⟪M.Cinv σ, τ⟫_ℝ + ⟪div τ, u⟫_ℝ + ⟪γ, τ⟫_ℝ = 0
  /-- `(div σ, v) = -κ (u, v)` for all `v ∈ U`. -/
  eq₂ : ∀ v : U, ⟪div σ, v⟫_ℝ = -κ * ⟪u, v⟫_ℝ
  /-- `(σ, η) = 0` for all `η ∈ X`. -/
  eq₃ : ∀ η ∈ X, ⟪σ, η⟫_ℝ = 0

/-- A solution `(κₕ, σₕ, uₕ, γₕ)` of the discrete eigenvalue problem (37) (p. 26) on the
discrete spaces `Sₕ`, `Uₕ`, `Xₕ`. The second equation is recorded in its strong form
`div σₕ = -κₕ uₕ`, which is how it is used on p. 30 (`div Sₕ ⊆ Uₕ`). -/
structure DiscreteMixedEigenpair (div : H →ₗ[ℝ] U) {X : Submodule ℝ H} {μ : ℝ}
    (M : MaterialOperator X μ) (Sₕ : Submodule ℝ H) (Uₕ : Submodule ℝ U)
    (Xₕ : Submodule ℝ H) where
  κₕ : ℝ
  σₕ : H
  uₕ : U
  γₕ : H
  σₕ_mem : σₕ ∈ Sₕ
  uₕ_mem : uₕ ∈ Uₕ
  γₕ_mem : γₕ ∈ Xₕ
  /-- `(C⁻¹σₕ, τₕ) + (div τₕ, uₕ) + (γₕ, τₕ) = 0` for all `τₕ ∈ Sₕ`. -/
  eq₁ : ∀ τₕ ∈ Sₕ, ⟪M.Cinv σₕ, τₕ⟫_ℝ + ⟪div τₕ, uₕ⟫_ℝ + ⟪γₕ, τₕ⟫_ℝ = 0
  /-- `div σₕ + κₕ uₕ = 0` holds strongly. -/
  eq₂ : div σₕ = -κₕ • uₕ
  /-- `(σₕ, ηₕ) = 0` for all `ηₕ ∈ Xₕ`. -/
  eq₃ : ∀ ηₕ ∈ Xₕ, ⟪σₕ, ηₕ⟫_ℝ = 0

section Identities

variable {div : H →ₗ[ℝ] U} {X S₀ Sₕ Xₕ : Submodule ℝ H} {Uₕ : Submodule ℝ U} {μ : ℝ}
  {M : MaterialOperator X μ}

/-- The three evaluations of the first equations used in both proofs, and the vanishing of
the mixed term `(γ, σ)`, `(γₕ, σₕ)`, `(σ, γₕ)`. -/
theorem MixedEigenpair.inner_Cinv_self (p : MixedEigenpair div X S₀ M) (hu : ‖p.u‖ = 1) :
    ⟪M.Cinv p.σ, p.σ⟫_ℝ = p.κ := by
  have h1 := p.eq₁ p.σ p.σ_mem
  have h2 := p.eq₂ p.u
  have h3 : ⟪p.γ, p.σ⟫_ℝ = 0 := by rw [real_inner_comm]; exact p.eq₃ p.γ p.γ_mem
  rw [real_inner_self_eq_norm_sq, hu] at h2
  linarith

/-- `(C⁻¹ σₕ, σₕ) = -(div σₕ, uₕ)` from (37). -/
theorem DiscreteMixedEigenpair.inner_Cinv_self (q : DiscreteMixedEigenpair div M Sₕ Uₕ Xₕ) :
    ⟪M.Cinv q.σₕ, q.σₕ⟫_ℝ = -⟪div q.σₕ, q.uₕ⟫_ℝ := by
  have h1 := q.eq₁ q.σₕ q.σₕ_mem
  have h3 : ⟪q.γₕ, q.σₕ⟫_ℝ = 0 := by rw [real_inner_comm]; exact q.eq₃ q.γₕ q.γₕ_mem
  linarith

/-- `(C⁻¹ σ, σₕ) = -(div σₕ, u) - (γ, σₕ)`: the first equation of (36) tested with `σₕ`. -/
theorem MixedEigenpair.inner_Cinv_discrete (p : MixedEigenpair div X S₀ M)
    (q : DiscreteMixedEigenpair div M Sₕ Uₕ Xₕ) (hS : Sₕ ≤ S₀) :
    ⟪M.Cinv p.σ, q.σₕ⟫_ℝ = -⟪div q.σₕ, p.u⟫_ℝ - ⟪p.γ, q.σₕ⟫_ℝ := by
  have h1 := p.eq₁ q.σₕ (hS q.σₕ_mem)
  linarith

/-- `(σ - σₕ, γ - γₕ) = -(γ, σₕ)`, using the third equations of (36) and (37). -/
theorem MixedEigenpair.inner_sub_sub (p : MixedEigenpair div X S₀ M)
    (q : DiscreteMixedEigenpair div M Sₕ Uₕ Xₕ) (hX : Xₕ ≤ X) :
    ⟪p.σ - q.σₕ, p.γ - q.γₕ⟫_ℝ = -⟪p.γ, q.σₕ⟫_ℝ := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, p.eq₃ p.γ p.γ_mem,
    p.eq₃ q.γₕ (hX q.γₕ_mem), q.eq₃ q.γₕ q.γₕ_mem, real_inner_comm p.γ q.σₕ]
  ring

/-- Polarization of `(C⁻¹(σ - σₕ), σ - σₕ)`, first line of the proof of Lemma 4.9. -/
theorem inner_Cinv_sub_sub (σ σₕ : H) :
    ⟪M.Cinv (σ - σₕ), σ - σₕ⟫_ℝ
      = ⟪M.Cinv σ, σ⟫_ℝ + ⟪M.Cinv σₕ, σₕ⟫_ℝ - 2 * ⟪M.Cinv σ, σₕ⟫_ℝ := by
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, M.Cinv_symm σₕ σ,
    real_inner_comm (M.Cinv σ) σₕ]
  ring

/-- The square-root-free form of Lemma 4.9:
`κ - κₕ = (C⁻¹(σ - σₕ), σ - σₕ) + 2 (σ - σₕ, γ - γₕ) - κₕ ‖u - uₕ‖²`
for normalized eigenfunctions `‖u‖ = ‖uₕ‖ = 1`. -/
theorem eigenvalue_identity_raw (p : MixedEigenpair div X S₀ M)
    (q : DiscreteMixedEigenpair div M Sₕ Uₕ Xₕ) (hS : Sₕ ≤ S₀) (hX : Xₕ ≤ X)
    (hu : ‖p.u‖ = 1) (huₕ : ‖q.uₕ‖ = 1) :
    p.κ - q.κₕ = ⟪M.Cinv (p.σ - q.σₕ), p.σ - q.σₕ⟫_ℝ + 2 * ⟪p.σ - q.σₕ, p.γ - q.γₕ⟫_ℝ
      - q.κₕ * ‖p.u - q.uₕ‖ ^ 2 := by
  have F5 := inner_Cinv_sub_sub (M := M) p.σ q.σₕ
  have F1 := p.inner_Cinv_self hu
  have F2 : ⟪M.Cinv q.σₕ, q.σₕ⟫_ℝ = q.κₕ := by
    rw [q.inner_Cinv_self, q.eq₂, real_inner_smul_left, real_inner_self_eq_norm_sq, huₕ]
    ring
  have F3 : ⟪M.Cinv p.σ, q.σₕ⟫_ℝ = q.κₕ * ⟪q.uₕ, p.u⟫_ℝ - ⟪p.γ, q.σₕ⟫_ℝ := by
    rw [p.inner_Cinv_discrete q hS, q.eq₂, real_inner_smul_left]
    ring
  have F4 := p.inner_sub_sub q hX
  have F9 : ‖p.u - q.uₕ‖ ^ 2 = 2 - 2 * ⟪p.u, q.uₕ⟫_ℝ := by
    rw [norm_sub_sq_real, hu, huₕ]; ring
  have F0 : ⟪q.uₕ, p.u⟫_ℝ = ⟪p.u, q.uₕ⟫_ℝ := real_inner_comm _ _
  rw [F5, F1, F2, F3, F4, F9, F0]
  ring

/-- **Lemma 4.9** (p. 30). For normalized eigenfunctions `‖u‖ = ‖uₕ‖ = 1`,
`κ - κₕ = ‖C⁻¹(σ - σₕ) + (γ - γₕ)‖²_{C^{1/2}} - 2μ ‖γ - γₕ‖² - κₕ ‖u - uₕ‖²`. -/
theorem eigenvalue_identity (p : MixedEigenpair div X S₀ M)
    (q : DiscreteMixedEigenpair div M Sₕ Uₕ Xₕ) (hS : Sₕ ≤ S₀) (hX : Xₕ ≤ X)
    (hu : ‖p.u‖ = 1) (huₕ : ‖q.uₕ‖ = 1) :
    p.κ - q.κₕ = energy M.C (M.Cinv (p.σ - q.σₕ) + (p.γ - q.γₕ))
      - 2 * μ * ‖p.γ - q.γₕ‖ ^ 2 - q.κₕ * ‖p.u - q.uₕ‖ ^ 2 := by
  have hd : p.γ - q.γₕ ∈ X := X.sub_mem p.γ_mem (hX q.γₕ_mem)
  rw [energy_Cinv_add M (p.σ - q.σₕ) hd, eigenvalue_identity_raw p q hS hX hu huₕ]
  ring

/-- **Definition 5.5** (p. 41): the postprocessed eigenvalue as the Rayleigh quotient
`κ*ₕ = -(div σₕ, u*ₕ) / (u*ₕ, u*ₕ)`, equation (59). -/
noncomputable def postprocessedEigenvalue (div : H →ₗ[ℝ] U) (σₕ : H) (uₛ : U) : ℝ :=
  -⟪div σₕ, uₛ⟫_ℝ / ‖uₛ‖ ^ 2

theorem postprocessedEigenvalue_mul_normSq (σₕ : H) {uₛ : U} (huₛ : uₛ ≠ 0) :
    postprocessedEigenvalue div σₕ uₛ * ‖uₛ‖ ^ 2 = -⟪div σₕ, uₛ⟫_ℝ := by
  unfold postprocessedEigenvalue
  have h : ‖uₛ‖ ^ 2 ≠ 0 := by positivity
  field_simp

/-- The square-root-free form of Lemma 5.6. Hypotheses: `‖u‖ = 1`; the postprocessed
eigenfunction `u*ₕ ≠ 0` satisfies the second equation of (53), `(u*ₕ, wₕ) = (uₕ, wₕ)` for
all `wₕ ∈ Uₕ`; and `div σₕ ∈ Uₕ` (p. 41). -/
theorem postprocessed_eigenvalue_identity_raw (p : MixedEigenpair div X S₀ M)
    (q : DiscreteMixedEigenpair div M Sₕ Uₕ Xₕ) (hS : Sₕ ≤ S₀) (hX : Xₕ ≤ X)
    (hu : ‖p.u‖ = 1) {uₛ : U} (huₛ : uₛ ≠ 0)
    (hpost : ∀ wₕ ∈ Uₕ, ⟪uₛ, wₕ⟫_ℝ = ⟪q.uₕ, wₕ⟫_ℝ) (hdiv : div q.σₕ ∈ Uₕ) :
    p.κ - postprocessedEigenvalue div q.σₕ uₛ
      = ⟪M.Cinv (p.σ - q.σₕ), p.σ - q.σₕ⟫_ℝ + 2 * ⟪p.σ - q.σₕ, p.γ - q.γₕ⟫_ℝ
        + postprocessedEigenvalue div q.σₕ uₛ * ‖p.u - uₛ‖ ^ 2
        + 2 * ⟪div (p.σ - q.σₕ), p.u - uₛ⟫_ℝ
        - 2 * ⟪(postprocessedEigenvalue div q.σₕ uₛ - p.κ) • p.u, p.u - uₛ⟫_ℝ := by
  set κₛ := postprocessedEigenvalue div q.σₕ uₛ with hκₛ
  have F5 := inner_Cinv_sub_sub (M := M) p.σ q.σₕ
  have F1 := p.inner_Cinv_self hu
  have F2 := q.inner_Cinv_self
  have F3 := p.inner_Cinv_discrete q hS
  have F4 := p.inner_sub_sub q hX
  have F7 : ⟪div q.σₕ, q.uₕ⟫_ℝ = ⟪div q.σₕ, uₛ⟫_ℝ := by
    rw [real_inner_comm q.uₕ (div q.σₕ), ← hpost (div q.σₕ) hdiv]
    exact real_inner_comm _ _
  have F8 : ⟪div q.σₕ, uₛ⟫_ℝ = -(κₛ * ‖uₛ‖ ^ 2) := by
    rw [hκₛ, postprocessedEigenvalue_mul_normSq q.σₕ huₛ, neg_neg]
  have F9 : ‖p.u - uₛ‖ ^ 2 = 1 - 2 * ⟪p.u, uₛ⟫_ℝ + ‖uₛ‖ ^ 2 := by
    rw [norm_sub_sq_real, hu]; ring
  have F10 : ⟪div (p.σ - q.σₕ), p.u - uₛ⟫_ℝ = ⟪div p.σ, p.u - uₛ⟫_ℝ - ⟪div q.σₕ, p.u - uₛ⟫_ℝ := by
    rw [map_sub, inner_sub_left]
  have F11 : ⟪div p.σ, p.u - uₛ⟫_ℝ = -p.κ * ⟪p.u, p.u - uₛ⟫_ℝ := p.eq₂ _
  have F12 : ⟪div q.σₕ, p.u - uₛ⟫_ℝ = ⟪div q.σₕ, p.u⟫_ℝ - ⟪div q.σₕ, uₛ⟫_ℝ := by
    rw [inner_sub_right]
  have F13 : ⟪p.u, p.u - uₛ⟫_ℝ = 1 - ⟪p.u, uₛ⟫_ℝ := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hu]; ring
  rw [real_inner_smul_left, F5, F1, F2, F3, F4, F7, F9, F10, F11, F12, F13, F8]
  ring

/-- **Lemma 5.6** (p. 41), identity (60):
`κ - κ*ₕ = ‖C⁻¹(σ - σₕ) + (γ - γₕ)‖²_{C^{1/2}} - 2μ ‖γ - γₕ‖² + κ*ₕ ‖u - u*ₕ‖²
  + 2 (div(σ - σₕ), u - u*ₕ) - 2 ((κ*ₕ - κ) u, u - u*ₕ)`.
The thesis assumes `‖u‖ = 1` in the proof; the hypotheses on `u*ₕ` are those of the
postprocessing (53). -/
theorem postprocessed_eigenvalue_identity (p : MixedEigenpair div X S₀ M)
    (q : DiscreteMixedEigenpair div M Sₕ Uₕ Xₕ) (hS : Sₕ ≤ S₀) (hX : Xₕ ≤ X)
    (hu : ‖p.u‖ = 1) {uₛ : U} (huₛ : uₛ ≠ 0)
    (hpost : ∀ wₕ ∈ Uₕ, ⟪uₛ, wₕ⟫_ℝ = ⟪q.uₕ, wₕ⟫_ℝ) (hdiv : div q.σₕ ∈ Uₕ) :
    p.κ - postprocessedEigenvalue div q.σₕ uₛ
      = energy M.C (M.Cinv (p.σ - q.σₕ) + (p.γ - q.γₕ)) - 2 * μ * ‖p.γ - q.γₕ‖ ^ 2
        + postprocessedEigenvalue div q.σₕ uₛ * ‖p.u - uₛ‖ ^ 2
        + 2 * ⟪div (p.σ - q.σₕ), p.u - uₛ⟫_ℝ
        - 2 * ⟪(postprocessedEigenvalue div q.σₕ uₛ - p.κ) • p.u, p.u - uₛ⟫_ℝ := by
  have hd : p.γ - q.γₕ ∈ X := X.sub_mem p.γ_mem (hX q.γₕ_mem)
  rw [energy_Cinv_add M (p.σ - q.σₕ) hd,
    postprocessed_eigenvalue_identity_raw p q hS hX hu huₛ hpost hdiv]
  ring

end Identities

/-! ### Consistency of the hypotheses

The structures above are satisfiable: `H = U = ℝ`, `div = 0`, `X = ⊥`, `S₀ = ⊤`,
`C = C⁻¹ = id`, eigenpair `(κ, σ, u, γ) = (0, 0, 1, 0)`. -/

/-- `C = C⁻¹ = id` on `ℝ` with `X = ⊥` is a material operator for any `μ`. -/
example (μ : ℝ) : MaterialOperator (⊥ : Submodule ℝ ℝ) μ where
  C := ContinuousLinearMap.id ℝ ℝ
  Cinv := ContinuousLinearMap.id ℝ ℝ
  symm := fun x y => by simp
  C_Cinv := fun x => rfl
  Cinv_C := fun x => rfl
  nonneg := fun x => real_inner_self_nonneg
  skew := by simp

/-- The trivial eigenpair `(0, 0, 1, 0)` solves (36) for `div = 0`. -/
example (μ : ℝ) (M : MaterialOperator (⊥ : Submodule ℝ ℝ) μ) :
    MixedEigenpair (0 : ℝ →ₗ[ℝ] ℝ) ⊥ ⊤ M where
  κ := 0
  σ := 0
  u := 1
  γ := 0
  σ_mem := Submodule.mem_top
  γ_mem := Submodule.zero_mem _
  eq₁ := fun τ _ => by simp
  eq₂ := fun v => by simp
  eq₃ := fun η _ => by simp

/-- The trivial discrete eigenpair `(0, 0, 1, 0)` solves (37) for `div = 0`. -/
example (μ : ℝ) (M : MaterialOperator (⊥ : Submodule ℝ ℝ) μ) :
    DiscreteMixedEigenpair (0 : ℝ →ₗ[ℝ] ℝ) M ⊤ ⊤ ⊥ where
  κₕ := 0
  σₕ := 0
  uₕ := 1
  γₕ := 0
  σₕ_mem := Submodule.mem_top
  uₕ_mem := Submodule.mem_top
  γₕ_mem := Submodule.zero_mem _
  eq₁ := fun τ _ => by simp
  eq₂ := by simp
  eq₃ := fun η _ => by simp

end MixedElasticEigenvalues
