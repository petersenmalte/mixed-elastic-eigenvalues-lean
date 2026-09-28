import MixedElasticEigenvalues.Material
import MixedElasticEigenvalues.EigenvalueIdentities

/-!
# The isotropic material operator on `2×2` tensors (roadmap step 1)

Connects the pointwise material algebra of `Material.lean` with the abstract layer of
`EigenvalueIdentities.lean`:

* `Tens2` is `Mat2` equipped with the Frobenius inner product `⟪σ, τ⟫ = σ : τ` (p. 7);
  it is a real, finite-dimensional inner product space;
* `skewSubspace` is the space of skew-symmetric tensors, the pointwise version of the
  space `X` of equation (9);
* `isotropicMaterial lam mu hmu hlm` is the `MaterialOperator` built from `matC` and
  `matCinv`, equations (3) and (4), for Lamé parameters with `μ > 0` and `λ + μ > 0`.

`Tens2` is a type synonym of `Mat2`, so that the Frobenius inner product does not become a
global instance on `Matrix (Fin 2) (Fin 2) ℝ` (Mathlib keeps matrix norms local on purpose).
The conversions `Tens2.toMat` and `Tens2.ofMat` are the identity.
-/

namespace MixedElasticEigenvalues

open Matrix
open scoped InnerProductSpace

noncomputable section

/-! ### Linearity of `C` and `C⁻¹` -/

theorem matC_add (lam mu : ℝ) (ε₁ ε₂ : Mat2) :
    matC lam mu (ε₁ + ε₂) = matC lam mu ε₁ + matC lam mu ε₂ := by
  ext i j; fin_cases i <;> fin_cases j <;> mat2_simp <;> ring

theorem matC_smul (lam mu c : ℝ) (ε : Mat2) : matC lam mu (c • ε) = c • matC lam mu ε := by
  ext i j; fin_cases i <;> fin_cases j <;> mat2_simp <;> ring

theorem matCinv_add (lam mu : ℝ) (σ₁ σ₂ : Mat2) :
    matCinv lam mu (σ₁ + σ₂) = matCinv lam mu σ₁ + matCinv lam mu σ₂ := by
  ext i j; fin_cases i <;> fin_cases j <;> mat2_simp <;> ring

theorem matCinv_smul (lam mu c : ℝ) (σ : Mat2) :
    matCinv lam mu (c • σ) = c • matCinv lam mu σ := by
  ext i j; fin_cases i <;> fin_cases j <;> mat2_simp <;> ring

/-! ### The Frobenius inner product space `Tens2` -/

/-- `2×2` real matrices with the Frobenius inner product `⟪σ, τ⟫ := σ : τ` (p. 7): the
pointwise values of the tensor fields in `L²(Ω; ℝ²ˣ²)`. -/
def Tens2 : Type := Mat2

namespace Tens2

instance : AddCommGroup Tens2 := inferInstanceAs (AddCommGroup Mat2)

instance : Module ℝ Tens2 := inferInstanceAs (Module ℝ Mat2)

instance : FiniteDimensional ℝ Tens2 := inferInstanceAs (FiniteDimensional ℝ Mat2)

/-- A tensor viewed as a matrix. -/
def toMat (σ : Tens2) : Mat2 := σ

/-- A matrix viewed as a tensor. -/
def ofMat (A : Mat2) : Tens2 := A

@[simp] theorem toMat_ofMat (A : Mat2) : toMat (ofMat A) = A := rfl
@[simp] theorem ofMat_toMat (σ : Tens2) : ofMat (toMat σ) = σ := rfl
@[simp] theorem toMat_zero : toMat 0 = 0 := rfl
@[simp] theorem toMat_add (σ τ : Tens2) : toMat (σ + τ) = toMat σ + toMat τ := rfl
@[simp] theorem toMat_neg (σ : Tens2) : toMat (-σ) = -toMat σ := rfl
@[simp] theorem toMat_sub (σ τ : Tens2) : toMat (σ - τ) = toMat σ - toMat τ := rfl
@[simp] theorem toMat_smul (c : ℝ) (σ : Tens2) : toMat (c • σ) = c • toMat σ := rfl

theorem toMat_injective : Function.Injective toMat := fun _ _ h => h

@[ext] theorem ext {σ τ : Tens2} (h : ∀ i j, toMat σ i j = toMat τ i j) : σ = τ :=
  Matrix.ext h

/-- The Frobenius product as an inner product core. -/
@[instance_reducible]
def frobCore : InnerProductSpace.Core ℝ Tens2 where
  inner σ τ := frob (toMat σ) (toMat τ)
  conj_inner_symm σ τ := by
    simp only [conj_trivial]
    exact frob_comm _ _
  re_inner_nonneg σ := by
    simp only [RCLike.re_to_real]
    exact frobSq_nonneg _
  add_left σ τ ρ := frob_add_left _ _ _
  smul_left σ τ r := by
    simp only [conj_trivial]
    exact frob_smul_left _ _ _
  definite σ h := toMat_injective ((frobSq_eq_zero_iff (toMat σ)).mp h)

instance : NormedAddCommGroup Tens2 :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ Tens2 _ _ _ frobCore

instance : InnerProductSpace ℝ Tens2 := InnerProductSpace.ofCore _

/-- The inner product of `Tens2` is the Frobenius product. -/
theorem inner_def (σ τ : Tens2) : ⟪σ, τ⟫_ℝ = frob (toMat σ) (toMat τ) := rfl

/-- The norm of `Tens2` is the Frobenius norm: `‖τ‖² = |τ|²`. -/
theorem norm_sq_eq (τ : Tens2) : ‖τ‖ ^ 2 = frobSq (toMat τ) := by
  rw [← real_inner_self_eq_norm_sq]; rfl

theorem norm_eq_sqrt (τ : Tens2) : ‖τ‖ = Real.sqrt (frobSq (toMat τ)) := by
  rw [← norm_sq_eq, Real.sqrt_sq (norm_nonneg τ)]

end Tens2

open Tens2

/-! ### Skew-symmetric tensors -/

/-- The skew-symmetric tensors `{η : ηᵀ = -η}`, the pointwise version of the space `X` of
equation (9). -/
def skewSubspace : Submodule ℝ Tens2 where
  carrier := {η | (toMat η)ᵀ = -toMat η}
  add_mem' {a b} ha hb := by
    change (toMat a + toMat b)ᵀ = -(toMat a + toMat b)
    rw [transpose_add, ha, hb, neg_add]
  zero_mem' := by
    change (0 : Mat2)ᵀ = -0
    simp
  smul_mem' c a ha := by
    change (c • toMat a)ᵀ = -(c • toMat a)
    rw [transpose_smul, ha, smul_neg]

theorem mem_skewSubspace (η : Tens2) : η ∈ skewSubspace ↔ (toMat η)ᵀ = -toMat η := Iff.rfl

/-- The skew-symmetric part lies in `X`. -/
theorem ofMat_skw_mem (τ : Mat2) : ofMat (skw τ) ∈ skewSubspace := skw_transpose τ

/-- Skew-symmetric tensors are orthogonal to symmetric ones (p. 7). -/
theorem inner_sym_skew (σ : Mat2) {η : Tens2} (hη : η ∈ skewSubspace) :
    ⟪ofMat (sym σ), η⟫_ℝ = 0 := by
  have h : skw (toMat η) = toMat η := (skw_eq_self_iff _).mpr hη
  rw [inner_def, toMat_ofMat, ← h]
  exact frob_sym_skw σ (toMat η)

/-! ### The material operators `C` and `C⁻¹` -/

/-- `C` as a linear map on `Tens2`, equation (3). -/
def matCLinear (lam mu : ℝ) : Tens2 →ₗ[ℝ] Tens2 where
  toFun ε := ofMat (matC lam mu (toMat ε))
  map_add' a b := matC_add lam mu (toMat a) (toMat b)
  map_smul' c a := matC_smul lam mu c (toMat a)

/-- `C⁻¹` as a linear map on `Tens2`, equation (4). -/
def matCinvLinear (lam mu : ℝ) : Tens2 →ₗ[ℝ] Tens2 where
  toFun σ := ofMat (matCinv lam mu (toMat σ))
  map_add' a b := matCinv_add lam mu (toMat a) (toMat b)
  map_smul' c a := matCinv_smul lam mu c (toMat a)

/-- `C` as a continuous linear map (every linear map on `Tens2` is continuous). -/
def matCCLM (lam mu : ℝ) : Tens2 →L[ℝ] Tens2 :=
  LinearMap.toContinuousLinearMap (matCLinear lam mu)

/-- `C⁻¹` as a continuous linear map. -/
def matCinvCLM (lam mu : ℝ) : Tens2 →L[ℝ] Tens2 :=
  LinearMap.toContinuousLinearMap (matCinvLinear lam mu)

@[simp] theorem toMat_matCCLM (lam mu : ℝ) (ε : Tens2) :
    toMat (matCCLM lam mu ε) = matC lam mu (toMat ε) := rfl

@[simp] theorem toMat_matCinvCLM (lam mu : ℝ) (σ : Tens2) :
    toMat (matCinvCLM lam mu σ) = matCinv lam mu (toMat σ) := rfl

/-- The isotropic material law of plane elasticity, equations (3) and (4), as a
`MaterialOperator` on the Frobenius inner product space `Tens2` with `X` the skew-symmetric
tensors. The Lamé parameters only need `μ > 0` and `λ + μ > 0` (the thesis assumes
`λ, μ > 0`). -/
def isotropicMaterial (lam mu : ℝ) (hmu : 0 < mu) (hlm : 0 < lam + mu) :
    MaterialOperator skewSubspace mu where
  C := matCCLM lam mu
  Cinv := matCinvCLM lam mu
  symm x y := by
    rw [inner_def, inner_def, toMat_matCCLM, toMat_matCCLM]
    exact frob_matC_symm lam mu _ _
  C_Cinv x := toMat_injective (matC_matCinv lam mu hmu.ne' (by linarith) (toMat x))
  Cinv_C x := toMat_injective (matCinv_matC lam mu hmu.ne' (by linarith) (toMat x))
  nonneg x := by
    rw [inner_def, toMat_matCCLM]
    exact frob_matC_self_nonneg hmu hlm _
  skew η hη := toMat_injective (matC_of_skew lam mu hη)

section isotropic

variable {lam mu : ℝ} (hmu : 0 < mu) (hlm : 0 < lam + mu)

@[simp] theorem isotropicMaterial_C : (isotropicMaterial lam mu hmu hlm).C = matCCLM lam mu :=
  rfl

@[simp] theorem isotropicMaterial_Cinv :
    (isotropicMaterial lam mu hmu hlm).Cinv = matCinvCLM lam mu := rfl

/-- `C` is positive definite: `⟪C ε, ε⟫ > 0` for `ε ≠ 0`. -/
theorem isotropicMaterial_pos {ε : Tens2} (hε : ε ≠ 0) :
    0 < ⟪(isotropicMaterial lam mu hmu hlm).C ε, ε⟫_ℝ := by
  rw [isotropicMaterial_C, inner_def, toMat_matCCLM]
  exact frob_matC_self_pos hmu hlm hε

/-- Reformulation of `a(σ, τ) = ⟪C⁻¹ σ, τ⟫` through deviator and trace (p. 13). -/
theorem isotropicMaterial_inner_Cinv (σ τ : Tens2) :
    ⟪(isotropicMaterial lam mu hmu hlm).Cinv σ, τ⟫_ℝ
      = 1 / (2 * mu) * ⟪ofMat (dev (toMat σ)), ofMat (dev (toMat τ))⟫_ℝ
        + 1 / (4 * (lam + mu)) * ((toMat σ).trace * (toMat τ).trace) := by
  rw [isotropicMaterial_Cinv, inner_def, inner_def, toMat_matCinvCLM]
  exact frob_matCinv_dev_trace lam mu hmu.ne' hlm.ne' _ _

/-- Coercivity of `a` on all of `L²` with a `λ`-dependent constant (p. 13):
`⟪C⁻¹ τ, τ⟫ ≥ ‖τ‖² / (2(λ + μ))` for `λ ≥ 0`. -/
theorem isotropicMaterial_Cinv_coercive (hlam : 0 ≤ lam) (τ : Tens2) :
    1 / (2 * (lam + mu)) * ‖τ‖ ^ 2 ≤ ⟪(isotropicMaterial lam mu hmu hlm).Cinv τ, τ⟫_ℝ := by
  rw [isotropicMaterial_Cinv, inner_def, toMat_matCinvCLM, norm_sq_eq]
  exact frob_matCinv_self_ge hmu hlam _

end isotropic

end

end MixedElasticEigenvalues
