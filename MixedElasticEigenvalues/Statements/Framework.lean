import MixedElasticEigenvalues.EigenvalueIdentities

/-!
# Framework for the theorem statements (Stage 3)

Abstract data shared by the statements in `MixedElasticEigenvalues/Statements/`:

* `hdivNorm div τ = ‖τ‖₀ + ‖div τ‖₀`, the `H(div)`-norm (p. 6);
* `DiscreteFamily`: a family of conforming finite-dimensional discrete spaces
  `Sₕ ⊆ S₀`, `Uₕ ⊆ U`, `Xₕ ⊆ X` indexed by meshes `i : ι` with mesh size `h i`, together
  with the refinement filter `l` along which `h → 0` (Chapter 3; for Falk's element
  `div Sₕ ⊆ Uₕ`, p. 23);
* `MixedSource` / `DiscreteMixedSource`: solutions of the source problems (11) and (17);
* `IsKernel` / `IsDiscreteKernel`: membership in `ker (B + C)` (p. 14) and
  `ker (Bₕ + Cₕ)`, equation (18);
* `SobolevNorms`: abstract Sobolev (semi)norms `‖·‖_s`, `|·|_s`, used only to formulate
  regularity assumptions and convergence rates;
* `trivialFamily`, `trivialMaterial`: the model `H = U = ℝ`, `div = id`, `C = id`, all
  discrete spaces equal to the whole space, used to check that the hypotheses of every
  statement are satisfiable.

Nothing about meshes, polynomials or Sobolev spaces is modelled concretely: every finite
element property enters the theorems of Stage 3 as an explicit, typed hypothesis.
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace
open Filter Topology

variable {H U : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The `H(div)`-norm `‖τ‖_{Hdiv} := ‖τ‖₀ + ‖div τ‖₀` (p. 6). -/
def hdivNorm (div : H →ₗ[ℝ] U) (τ : H) : ℝ := ‖τ‖ + ‖div τ‖

theorem norm_le_hdivNorm (div : H →ₗ[ℝ] U) (τ : H) : ‖τ‖ ≤ hdivNorm div τ := by
  unfold hdivNorm; linarith [norm_nonneg (div τ)]

theorem norm_div_le_hdivNorm (div : H →ₗ[ℝ] U) (τ : H) : ‖div τ‖ ≤ hdivNorm div τ := by
  unfold hdivNorm; linarith [norm_nonneg τ]

theorem hdivNorm_nonneg (div : H →ₗ[ℝ] U) (τ : H) : 0 ≤ hdivNorm div τ :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

/-- A family of conforming discrete spaces `Sₕ = Σ_{g,h} ⊆ S₀`, `Uₕ ⊆ U`, `Xₕ ⊆ X`
indexed by meshes `i : ι` with mesh size `h i > 0` (Chapter 3). The refinement filter `l`
expresses "`h → 0`"; `div Sₕ ⊆ Uₕ` holds for Falk's element (p. 23, Remark 3.6). -/
structure DiscreteFamily (div : H →ₗ[ℝ] U) (X S₀ : Submodule ℝ H) (ι : Type*) where
  S : ι → Submodule ℝ H
  Uh : ι → Submodule ℝ U
  Xh : ι → Submodule ℝ H
  h : ι → ℝ
  h_pos : ∀ i, 0 < h i
  S_le : ∀ i, S i ≤ S₀
  Xh_le : ∀ i, Xh i ≤ X
  div_mem : ∀ i, ∀ τ ∈ S i, div τ ∈ Uh i
  finite_S : ∀ i, FiniteDimensional ℝ (S i)
  finite_Uh : ∀ i, FiniteDimensional ℝ (Uh i)
  finite_Xh : ∀ i, FiniteDimensional ℝ (Xh i)
  l : Filter ι
  h_tendsto : Tendsto h l (𝓝 0)

/-- `τ ∈ ker (B + C)` (p. 14): `τ ∈ S₀` with `(div τ, v) = 0` for all `v` and `(τ, η) = 0`
for all skew-symmetric `η`. -/
def IsKernel (div : H →ₗ[ℝ] U) (X S₀ : Submodule ℝ H) (τ : H) : Prop :=
  τ ∈ S₀ ∧ (∀ v : U, ⟪div τ, v⟫_ℝ = 0) ∧ (∀ η ∈ X, ⟪τ, η⟫_ℝ = 0)

/-- `τₕ ∈ ker (Bₕ + Cₕ)`, equation (18). -/
def IsDiscreteKernel (div : H →ₗ[ℝ] U) (Sₕ : Submodule ℝ H) (Uₕ : Submodule ℝ U)
    (Xₕ : Submodule ℝ H) (τ : H) : Prop :=
  τ ∈ Sₕ ∧ (∀ v ∈ Uₕ, ⟪div τ, v⟫_ℝ = 0) ∧ (∀ η ∈ Xₕ, ⟪τ, η⟫_ℝ = 0)

/-- A solution `(σ, u, γ)` of the source problem (11) with right-hand side `f`. -/
structure MixedSource (div : H →ₗ[ℝ] U) (X S₀ : Submodule ℝ H) {μ : ℝ}
    (M : MaterialOperator X μ) (f : U) where
  σ : H
  u : U
  γ : H
  σ_mem : σ ∈ S₀
  γ_mem : γ ∈ X
  eq₁ : ∀ τ ∈ S₀, ⟪M.Cinv σ, τ⟫_ℝ + ⟪div τ, u⟫_ℝ + ⟪γ, τ⟫_ℝ = 0
  eq₂ : ∀ v : U, ⟪div σ, v⟫_ℝ = -⟪f, v⟫_ℝ
  eq₃ : ∀ η ∈ X, ⟪σ, η⟫_ℝ = 0

/-- A solution `(σₕ, uₕ, γₕ)` of the discrete source problem (17) with right-hand side `f`. -/
structure DiscreteMixedSource (div : H →ₗ[ℝ] U) {X : Submodule ℝ H} {μ : ℝ}
    (M : MaterialOperator X μ) (Sₕ : Submodule ℝ H) (Uₕ : Submodule ℝ U)
    (Xₕ : Submodule ℝ H) (f : U) where
  σₕ : H
  uₕ : U
  γₕ : H
  σₕ_mem : σₕ ∈ Sₕ
  uₕ_mem : uₕ ∈ Uₕ
  γₕ_mem : γₕ ∈ Xₕ
  eq₁ : ∀ τₕ ∈ Sₕ, ⟪M.Cinv σₕ, τₕ⟫_ℝ + ⟪div τₕ, uₕ⟫_ℝ + ⟪γₕ, τₕ⟫_ℝ = 0
  eq₂ : ∀ vₕ ∈ Uₕ, ⟪div σₕ, vₕ⟫_ℝ = -⟪f, vₕ⟫_ℝ
  eq₃ : ∀ ηₕ ∈ Xₕ, ⟪σₕ, ηₕ⟫_ℝ = 0

/-- Abstract Sobolev (semi)norms `‖·‖_s` (or `|·|_s`) on tensor fields (`hn`) and on vector
fields (`un`), `s ∈ ℕ` (p. 6). They only serve to state regularity assumptions and
convergence rates; no property beyond nonnegativity is used. -/
structure SobolevNorms (H U : Type*) [NormedAddCommGroup H] [NormedAddCommGroup U] where
  hn : ℕ → H → ℝ
  un : ℕ → U → ℝ
  hn_nonneg : ∀ s τ, 0 ≤ hn s τ
  un_nonneg : ∀ s v, 0 ≤ un s v

/-! ### The trivial model -/

noncomputable section

/-- `C = C⁻¹ = id` on `ℝ` with `X = ⊥` is a material operator for every `μ`. -/
def trivialMaterial (μ : ℝ) : MaterialOperator (⊥ : Submodule ℝ ℝ) μ where
  C := ContinuousLinearMap.id ℝ ℝ
  Cinv := ContinuousLinearMap.id ℝ ℝ
  symm := fun x y => by simp
  C_Cinv := fun x => rfl
  Cinv_C := fun x => rfl
  nonneg := fun x => real_inner_self_nonneg
  skew := by simp

/-- The family with `div = id : ℝ → ℝ`, `Sₕ = Uₕ = ℝ`, `Xₕ = ⊥`, `h n = 1/(n+1)`. -/
def trivialFamily : DiscreteFamily (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (⊥ : Submodule ℝ ℝ) ⊤ ℕ where
  S := fun _ => ⊤
  Uh := fun _ => ⊤
  Xh := fun _ => ⊥
  h := fun n => 1 / ((n : ℝ) + 1)
  h_pos := fun n => by positivity
  S_le := fun _ => le_rfl
  Xh_le := fun _ => le_rfl
  div_mem := fun _ _ _ => Submodule.mem_top
  finite_S := fun _ => inferInstance
  finite_Uh := fun _ => inferInstance
  finite_Xh := fun _ => inferInstance
  l := atTop
  h_tendsto := tendsto_one_div_add_atTop_nhds_zero_nat

/-- In the trivial model, `(σ, u, γ) = (-f, f, 0)` solves the source problem (11). -/
def trivialSource (μ : ℝ) (f : ℝ) :
    MixedSource (LinearMap.id : ℝ →ₗ[ℝ] ℝ) ⊥ ⊤ (trivialMaterial μ) f where
  σ := -f
  u := f
  γ := 0
  σ_mem := Submodule.mem_top
  γ_mem := Submodule.zero_mem _
  eq₁ := fun τ _ => by simp [trivialMaterial] <;> ring
  eq₂ := fun v => by simp
  eq₃ := fun η hη => by simp [(Submodule.mem_bot ℝ).mp hη]

/-- In the trivial model, `(σₕ, uₕ, γₕ) = (-f, f, 0)` solves the discrete source problem. -/
def trivialDiscreteSource (μ : ℝ) (f : ℝ) (n : ℕ) :
    DiscreteMixedSource (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (trivialMaterial μ) (trivialFamily.S n)
      (trivialFamily.Uh n) (trivialFamily.Xh n) f where
  σₕ := -f
  uₕ := f
  γₕ := 0
  σₕ_mem := Submodule.mem_top
  uₕ_mem := Submodule.mem_top
  γₕ_mem := Submodule.zero_mem _
  eq₁ := fun τ _ => by simp [trivialMaterial] <;> ring
  eq₂ := fun v _ => by simp
  eq₃ := fun η hη => by
    simp only [trivialFamily, Submodule.mem_bot] at hη
    simp [hη]

/-- In the trivial model, `(κ, σ, u, γ) = (1, -1, 1, 0)` is a normalized eigenpair of (36). -/
def trivialEigenpair (μ : ℝ) :
    MixedEigenpair (LinearMap.id : ℝ →ₗ[ℝ] ℝ) ⊥ ⊤ (trivialMaterial μ) where
  κ := 1
  σ := -1
  u := 1
  γ := 0
  σ_mem := Submodule.mem_top
  γ_mem := Submodule.zero_mem _
  eq₁ := fun τ _ => by simp [trivialMaterial] <;> ring
  eq₂ := fun v => by simp
  eq₃ := fun η hη => by simp [(Submodule.mem_bot ℝ).mp hη]

/-- In the trivial model, `(κₕ, σₕ, uₕ, γₕ) = (1, -1, 1, 0)` is a normalized discrete
eigenpair of (37) on every mesh. -/
def trivialDiscreteEigenpair (μ : ℝ) (n : ℕ) :
    DiscreteMixedEigenpair (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (trivialMaterial μ) (trivialFamily.S n)
      (trivialFamily.Uh n) (trivialFamily.Xh n) where
  κₕ := 1
  σₕ := -1
  uₕ := 1
  γₕ := 0
  σₕ_mem := Submodule.mem_top
  uₕ_mem := Submodule.mem_top
  γₕ_mem := Submodule.zero_mem _
  eq₁ := fun τ _ => by simp [trivialMaterial] <;> ring
  eq₂ := by simp
  eq₃ := fun η hη => by
    simp only [trivialFamily, Submodule.mem_bot] at hη
    simp [hη]

/-- The norms `‖·‖_s := ‖·‖` for every `s` are admissible Sobolev norms. -/
def trivialSobolev : SobolevNorms ℝ ℝ where
  hn := fun _ x => ‖x‖
  un := fun _ x => ‖x‖
  hn_nonneg := fun _ _ => norm_nonneg _
  un_nonneg := fun _ _ => norm_nonneg _

end

end MixedElasticEigenvalues
