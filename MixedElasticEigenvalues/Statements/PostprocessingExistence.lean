import MixedElasticEigenvalues.Statements.Postprocessing

/-!
# Existence and uniqueness of the postprocessing (52) (roadmap step 3)

In `Postprocessing.lean` the postprocessed eigenfunction `u*ₕ` enters as data. Here it is
constructed: given the spaces `Uₕ ⊆ U*ₕ = Uₕ ⊕ Ũₕ` of (50)–(51) and the broken gradient,
the problem (52)

  `u*ₕ ∈ U*ₕ`, `Pₕ u*ₕ = uₕ`, `(∇u*ₕ, ∇ṽ) = (C⁻¹σₕ + γₕ, ∇ṽ)` for all `ṽ ∈ Ũₕ`

has exactly one solution as soon as `Ũₕ` is finite-dimensional and `∇` is injective on
`Ũₕ`; the latter follows from Poincaré's inequality on `Ũₕ` (`grad_inj_of_poincare`),
which is part of the input of Theorem 5.1.

* `exists_grad_galerkin` — finite-dimensional Lax–Milgram for `(∇·, ∇·)` on `Ũₕ`;
* `postprocessed_unique` — uniqueness for (52);
* `PostprocessingSpaces.exists_isPostprocessed` — existence for (52);
* `PostprocessingSpaces.toPostprocessing` — a `Postprocessing` constructed from the spaces;
* `Postprocessing.ustar_unique` — every `Postprocessing` has the unique solution as `u*ₕ`.
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace

noncomputable section

variable {H U : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] {ι : Type*}
  {div : H →ₗ[ℝ] U} {X S₀ : Submodule ℝ H} {μ : ℝ}

/-- Poincaré's inequality `‖v‖ ≤ c ‖∇v‖` on a subspace makes `∇` injective there. -/
theorem grad_inj_of_poincare {grad : U →ₗ[ℝ] H} {V : Submodule ℝ U} {c : ℝ}
    (h : ∀ v ∈ V, ‖v‖ ≤ c * ‖grad v‖) : ∀ v ∈ V, grad v = 0 → v = 0 := by
  intro v hv h0
  have := h v hv
  rw [h0, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.mp this

/-- Finite-dimensional Lax–Milgram for the form `(∇x, ∇v)`: if `∇` is injective on the
finite-dimensional subspace `V`, then for every `g` there is `x ∈ V` with
`(∇x, ∇v) = (g, ∇v)` for all `v ∈ V`. The map `x ↦ (∇x, ∇·)` from `V` to its dual is
injective, hence surjective. -/
theorem exists_grad_galerkin (grad : U →ₗ[ℝ] H) (V : Submodule ℝ U) [FiniteDimensional ℝ V]
    (hinj : ∀ v ∈ V, grad v = 0 → v = 0) (g : H) :
    ∃ x ∈ V, ∀ v ∈ V, ⟪grad x, grad v⟫_ℝ = ⟪g, grad v⟫_ℝ := by
  let F : V →ₗ[ℝ] Module.Dual ℝ V :=
    { toFun := fun x =>
        { toFun := fun y => ⟪grad x, grad y⟫_ℝ
          map_add' := by intro y z; simp [inner_add_right]
          map_smul' := by intro r y; simp [inner_smul_right] }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        simp [inner_add_left]
      map_smul' := by
        intro r x
        apply LinearMap.ext
        intro z
        simp [real_inner_smul_left] }
  have hF : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have h : ⟪grad x, grad x⟫_ℝ = 0 := by
      have := congrArg (fun l : Module.Dual ℝ V => l x) hx
      simpa [F] using this
    rw [inner_self_eq_zero] at h
    exact Subtype.ext (hinj x x.property h)
  have hsurj : Function.Surjective F :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm).mp hF
  let b : Module.Dual ℝ V :=
    { toFun := fun y => ⟪g, grad y⟫_ℝ
      map_add' := by intro y z; simp [inner_add_right]
      map_smul' := by intro r y; simp [inner_smul_right] }
  obtain ⟨x, hx⟩ := hsurj b
  refine ⟨x, x.property, fun v hv => ?_⟩
  have := congrArg (fun l : Module.Dual ℝ V => l ⟨v, hv⟩) hx
  simpa [F, b] using this

/-- The conditions (52) on `u*ₕ` for given `uₕ` and right-hand side `g = C⁻¹σₕ + γₕ`:
`u ∈ U*ₕ`, `Pₕ u = uₕ` (in weak form) and `(∇u, ∇ṽ) = (g, ∇ṽ)` for all `ṽ ∈ Ũₕ`. -/
def IsPostprocessed (Uh Ustar Utilde : Submodule ℝ U) (grad : U →ₗ[ℝ] H) (uₕ : U) (g : H)
    (u : U) : Prop :=
  u ∈ Ustar ∧ (∀ w ∈ Uh, ⟪u, w⟫_ℝ = ⟪uₕ, w⟫_ℝ) ∧
    ∀ v ∈ Utilde, ⟪grad u, grad v⟫_ℝ = ⟪g, grad v⟫_ℝ

/-- Uniqueness for (52): if `U*ₕ = Uₕ + Ũₕ` with `Uₕ ⊥ Ũₕ` and `∇` is injective on `Ũₕ`,
then (52) has at most one solution. -/
theorem postprocessed_unique {Uh Ustar Utilde : Submodule ℝ U} {grad : U →ₗ[ℝ] H}
    (orth : ∀ v ∈ Utilde, ∀ w ∈ Uh, ⟪v, w⟫_ℝ = 0)
    (sum : ∀ v ∈ Ustar, ∃ w ∈ Uh, ∃ vt ∈ Utilde, v = w + vt)
    (inj : ∀ v ∈ Utilde, grad v = 0 → v = 0) {uₕ : U} {g : H} {u₁ u₂ : U}
    (h₁ : IsPostprocessed Uh Ustar Utilde grad uₕ g u₁)
    (h₂ : IsPostprocessed Uh Ustar Utilde grad uₕ g u₂) : u₁ = u₂ := by
  obtain ⟨w, hw, vt, hvt, hd⟩ := sum (u₁ - u₂) (Ustar.sub_mem h₁.1 h₂.1)
  have hw0 : w = 0 := by
    have e : ⟪u₁ - u₂, w⟫_ℝ = 0 := by
      rw [inner_sub_left, h₁.2.1 w hw, h₂.2.1 w hw, sub_self]
    rw [hd, inner_add_left, orth vt hvt w hw, add_zero, inner_self_eq_zero] at e
    exact e
  rw [hw0, zero_add] at hd
  have hg : ⟪grad vt, grad vt⟫_ℝ = 0 := by
    nth_rewrite 1 [← hd]
    rw [map_sub, inner_sub_left, h₁.2.2 vt hvt, h₂.2.2 vt hvt, sub_self]
  rw [inner_self_eq_zero] at hg
  rw [← sub_eq_zero, hd]
  exact inj vt hvt hg

/-- Existence for (52): with `Ũₕ` finite-dimensional and `∇` injective on `Ũₕ`, the
function `u*ₕ = uₕ + ũ`, where `ũ ∈ Ũₕ` solves `(∇ũ, ∇ṽ) = (g - ∇uₕ, ∇ṽ)`, solves (52). -/
theorem exists_postprocessed {Uh Ustar Utilde : Submodule ℝ U} {grad : U →ₗ[ℝ] H}
    (Uh_le : Uh ≤ Ustar) (Utilde_le : Utilde ≤ Ustar)
    (orth : ∀ v ∈ Utilde, ∀ w ∈ Uh, ⟪v, w⟫_ℝ = 0) [FiniteDimensional ℝ Utilde]
    (inj : ∀ v ∈ Utilde, grad v = 0 → v = 0) {uₕ : U} (huₕ : uₕ ∈ Uh) (g : H) :
    ∃ u, IsPostprocessed Uh Ustar Utilde grad uₕ g u := by
  obtain ⟨x, hx, hxeq⟩ := exists_grad_galerkin grad Utilde inj (g - grad uₕ)
  refine ⟨uₕ + x, Ustar.add_mem (Uh_le huₕ) (Utilde_le hx), fun w hw => ?_, fun v hv => ?_⟩
  · rw [inner_add_left, orth x hx w hw, add_zero]
  · rw [map_add, inner_add_left, hxeq v hv, inner_sub_left]
    ring

/-- The data of the postprocessing (50)–(52) except for `u*ₕ` itself: the enriched space
`U*ₕ = Uₕ ⊕ Ũₕ`, the broken gradient, finite dimensionality of `Ũₕ` and injectivity of the
broken gradient on `Ũₕ` (e.g. by `grad_inj_of_poincare`). -/
structure PostprocessingSpaces (D : DiscreteFamily div X S₀ ι) where
  Ustar : ι → Submodule ℝ U
  Uh_le : ∀ i, D.Uh i ≤ Ustar i
  Utilde : ι → Submodule ℝ U
  Utilde_le : ∀ i, Utilde i ≤ Ustar i
  Utilde_orth : ∀ i, ∀ v ∈ Utilde i, ∀ w ∈ D.Uh i, ⟪v, w⟫_ℝ = 0
  Ustar_sum : ∀ i, ∀ v ∈ Ustar i, ∃ w ∈ D.Uh i, ∃ vt ∈ Utilde i, v = w + vt
  grad : U →ₗ[ℝ] H
  finite_Utilde : ∀ i, FiniteDimensional ℝ (Utilde i)
  grad_inj : ∀ i, ∀ v ∈ Utilde i, grad v = 0 → v = 0

namespace PostprocessingSpaces

variable {D : DiscreteFamily div X S₀ ι} (PS : PostprocessingSpaces D)

theorem exists_isPostprocessed (i : ι) {uₕ : U} (huₕ : uₕ ∈ D.Uh i) (g : H) :
    ∃ u, IsPostprocessed (D.Uh i) (PS.Ustar i) (PS.Utilde i) PS.grad uₕ g u :=
  haveI := PS.finite_Utilde i
  exists_postprocessed (PS.Uh_le i) (PS.Utilde_le i) (PS.Utilde_orth i) (PS.grad_inj i) huₕ g

theorem isPostprocessed_unique (i : ι) {uₕ : U} {g : H} {u₁ u₂ : U}
    (h₁ : IsPostprocessed (D.Uh i) (PS.Ustar i) (PS.Utilde i) PS.grad uₕ g u₁)
    (h₂ : IsPostprocessed (D.Uh i) (PS.Ustar i) (PS.Utilde i) PS.grad uₕ g u₂) : u₁ = u₂ :=
  postprocessed_unique (PS.Utilde_orth i) (PS.Ustar_sum i) (PS.grad_inj i) h₁ h₂

/-- The postprocessing (52) of a family of discrete eigenpairs, constructed from the spaces:
`u*ₕ` is the unique solution of (52) with `g = C⁻¹σₕ + γₕ`. -/
def toPostprocessing {M : MaterialOperator X μ} (E : EigenpairFamily D M) :
    Postprocessing D M E where
  Ustar := PS.Ustar
  Uh_le := PS.Uh_le
  Utilde := PS.Utilde
  Utilde_le := PS.Utilde_le
  Utilde_orth := PS.Utilde_orth
  Ustar_sum := PS.Ustar_sum
  grad := PS.grad
  ustar i := (PS.exists_isPostprocessed i (E.q i).uₕ_mem (M.Cinv (E.q i).σₕ + (E.q i).γₕ)).choose
  ustar_mem i :=
    (PS.exists_isPostprocessed i (E.q i).uₕ_mem (M.Cinv (E.q i).σₕ + (E.q i).γₕ)).choose_spec.1
  proj i :=
    (PS.exists_isPostprocessed i (E.q i).uₕ_mem (M.Cinv (E.q i).σₕ + (E.q i).γₕ)).choose_spec.2.1
  grad_eq i :=
    (PS.exists_isPostprocessed i (E.q i).uₕ_mem (M.Cinv (E.q i).σₕ + (E.q i).γₕ)).choose_spec.2.2

end PostprocessingSpaces

/-- The postprocessed eigenfunction of any `Postprocessing` is the unique solution of (52),
provided the broken gradient is injective on `Ũₕ` (e.g. by Poincaré's inequality). -/
theorem Postprocessing.ustar_unique {D : DiscreteFamily div X S₀ ι} {M : MaterialOperator X μ}
    {E : EigenpairFamily D M} (PP : Postprocessing D M E)
    (hinj : ∀ i, ∀ v ∈ PP.Utilde i, PP.grad v = 0 → v = 0) (i : ι) {u : U}
    (hu : IsPostprocessed (D.Uh i) (PP.Ustar i) (PP.Utilde i) PP.grad (E.q i).uₕ
      (M.Cinv (E.q i).σₕ + (E.q i).γₕ) u) : u = PP.ustar i :=
  postprocessed_unique (PP.Utilde_orth i) (PP.Ustar_sum i) (hinj i) hu
    ⟨PP.ustar_mem i, PP.proj i, PP.grad_eq i⟩

/-- Under the input of Theorem 5.1, the postprocessing is unique: Poincaré's inequality on
`Ũₕ` (`PostprocessingRates.poincare`) makes the broken gradient injective there. -/
theorem PostprocessingRates.ustar_unique {D : DiscreteFamily div X S₀ ι}
    {M : MaterialOperator X μ} {E : EigenpairFamily D M} {PP : Postprocessing D M E}
    {N : SobolevNorms H U} {k : ℕ} (R : PostprocessingRates PP N k) (i : ι) {u : U}
    (hu : IsPostprocessed (D.Uh i) (PP.Ustar i) (PP.Utilde i) PP.grad (E.q i).uₕ
      (M.Cinv (E.q i).σₕ + (E.q i).γₕ) u) : u = PP.ustar i :=
  PP.ustar_unique (fun j => grad_inj_of_poincare (R.poincare j)) i hu

end

end MixedElasticEigenvalues
