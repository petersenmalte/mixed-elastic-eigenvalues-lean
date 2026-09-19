import Mathlib

/-!
# Material algebra for 2×2 tensors (thesis Chapter 2, pp. 9–14)

Pointwise linear algebra on `Matrix (Fin 2) (Fin 2) ℝ` underlying the isotropic material
law `σ = C ε(u)` of plane linear elasticity: equations (3)–(6) and (12) of the thesis.

* `frob σ τ` is the Frobenius product `σ : τ = ∑ᵢⱼ σᵢⱼ τᵢⱼ` (p. 7).
* `skw`, `sym`, `dev` are the skew-symmetric part, the symmetric part and the deviator.
* `matC lam mu ε = λ tr ε · I + 2μ ε` is the material tensor `C`, equation (3);
  `matCinv lam mu` is its inverse `C⁻¹`, equation (4).

All statements are pointwise (finite-dimensional) identities and inequalities. The integral
identities of the thesis (e.g. the reformulation of `a(σ,τ)` on p. 13) follow from these by
integrating over the domain, which is not formalized here.
-/

namespace MixedElasticEigenvalues

open Matrix

noncomputable section

/-- `2×2` real matrices: the pointwise values of stress and strain tensors. -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

/-- Frobenius product `σ : τ := ∑ᵢⱼ σᵢⱼ τᵢⱼ` (thesis p. 7). -/
def frob (σ τ : Mat2) : ℝ := ∑ i, ∑ j, σ i j * τ i j

/-- Squared Frobenius norm `|τ|² := τ : τ`. -/
def frobSq (τ : Mat2) : ℝ := frob τ τ

/-- Skew-symmetric part `skw τ := ½ (τ - τᵀ)` (p. 7). -/
def skw (τ : Mat2) : Mat2 := (1 / 2 : ℝ) • (τ - τᵀ)

/-- Symmetric part `sym τ := ½ (τ + τᵀ)` (p. 7). -/
def sym (τ : Mat2) : Mat2 := (1 / 2 : ℝ) • (τ + τᵀ)

/-- Deviator `dev τ := τ - ½ tr τ · I` (p. 10). -/
def dev (τ : Mat2) : Mat2 := τ - (τ.trace / 2) • (1 : Mat2)

/-- Isotropic material tensor `C ε := λ tr ε · I + 2μ ε`, equation (3) (p. 9). -/
def matC (lam mu : ℝ) (ε : Mat2) : Mat2 := (lam * ε.trace) • (1 : Mat2) + (2 * mu) • ε

/-- Inverse material tensor `C⁻¹ σ := 1/(2μ) (σ - λ/(2(μ+λ)) tr σ · I)`, equation (4) (p. 9). -/
def matCinv (lam mu : ℝ) (σ : Mat2) : Mat2 :=
  (1 / (2 * mu)) • (σ - (lam / (2 * (mu + lam)) * σ.trace) • (1 : Mat2))

/-- Simp set that reduces every statement about `2×2` matrices to statements about their
four entries. -/
macro "mat2_simp" : tactic =>
  `(tactic| simp only [frob, frobSq, skw, sym, dev, matC, matCinv, Fin.sum_univ_two,
      Matrix.trace_fin_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.neg_apply, Matrix.transpose_apply, Matrix.one_apply, smul_eq_mul,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff,
      OfNat.ofNat_ne_one,
      OfNat.one_ne_ofNat, ite_true, ite_false, Nat.succ_ne_self,
      one_ne_zero, zero_ne_one, mul_one, mul_zero, sub_zero, add_zero])

/-! ### The Frobenius product -/

theorem frob_comm (σ τ : Mat2) : frob σ τ = frob τ σ := by
  mat2_simp; ring

theorem frob_add_left (σ₁ σ₂ τ : Mat2) : frob (σ₁ + σ₂) τ = frob σ₁ τ + frob σ₂ τ := by
  mat2_simp; ring

theorem frob_add_right (σ τ₁ τ₂ : Mat2) : frob σ (τ₁ + τ₂) = frob σ τ₁ + frob σ τ₂ := by
  mat2_simp; ring

theorem frob_sub_left (σ₁ σ₂ τ : Mat2) : frob (σ₁ - σ₂) τ = frob σ₁ τ - frob σ₂ τ := by
  mat2_simp; ring

theorem frob_sub_right (σ τ₁ τ₂ : Mat2) : frob σ (τ₁ - τ₂) = frob σ τ₁ - frob σ τ₂ := by
  mat2_simp; ring

theorem frob_smul_left (c : ℝ) (σ τ : Mat2) : frob (c • σ) τ = c * frob σ τ := by
  mat2_simp; ring

theorem frob_smul_right (c : ℝ) (σ τ : Mat2) : frob σ (c • τ) = c * frob σ τ := by
  mat2_simp; ring

theorem frobSq_nonneg (τ : Mat2) : 0 ≤ frobSq τ := by
  mat2_simp
  linarith [mul_self_nonneg (τ 0 0), mul_self_nonneg (τ 0 1), mul_self_nonneg (τ 1 0),
    mul_self_nonneg (τ 1 1)]

theorem frobSq_eq_zero_iff (τ : Mat2) : frobSq τ = 0 ↔ τ = 0 := by
  constructor
  · intro h
    simp only [frobSq, frob, Fin.sum_univ_two] at h
    have n00 := mul_self_nonneg (τ 0 0)
    have n01 := mul_self_nonneg (τ 0 1)
    have n10 := mul_self_nonneg (τ 1 0)
    have n11 := mul_self_nonneg (τ 1 1)
    have h00 : τ 0 0 = 0 := mul_self_eq_zero.mp (by linarith)
    have h01 : τ 0 1 = 0 := mul_self_eq_zero.mp (by linarith)
    have h10 : τ 1 0 = 0 := mul_self_eq_zero.mp (by linarith)
    have h11 : τ 1 1 = 0 := mul_self_eq_zero.mp (by linarith)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  · rintro rfl
    simp [frobSq, frob]

/-! ### Symmetric and skew-symmetric parts -/

theorem sym_add_skw (τ : Mat2) : sym τ + skw τ = τ := by
  ext i j; fin_cases i <;> fin_cases j <;> mat2_simp <;> ring

theorem skw_transpose (τ : Mat2) : (skw τ)ᵀ = -skw τ := by
  ext i j; fin_cases i <;> fin_cases j <;> mat2_simp <;> ring

theorem sym_transpose (τ : Mat2) : (sym τ)ᵀ = sym τ := by
  ext i j; fin_cases i <;> fin_cases j <;> mat2_simp <;> ring

/-- A matrix is skew-symmetric iff it equals its skew-symmetric part. -/
theorem skw_eq_self_iff (η : Mat2) : skw η = η ↔ ηᵀ = -η := by
  constructor
  · intro h
    rw [← h, skw_transpose]
  · intro h
    have h00 : η 0 0 = -η 0 0 := by simpa using congrFun (congrFun h 0) 0
    have h01 : η 1 0 = -η 0 1 := by simpa using congrFun (congrFun h 0) 1
    have h10 : η 0 1 = -η 1 0 := by simpa using congrFun (congrFun h 1) 0
    have h11 : η 1 1 = -η 1 1 := by simpa using congrFun (congrFun h 1) 1
    ext i j
    fin_cases i <;> fin_cases j <;> mat2_simp <;> linarith

/-- Skew-symmetric matrices are trace free (used on p. 30: `(Cγ, σ) = 2μ (γ, σ)`). -/
theorem trace_skw (τ : Mat2) : (skw τ).trace = 0 := by
  mat2_simp; ring

theorem trace_eq_zero_of_skew {η : Mat2} (h : ηᵀ = -η) : η.trace = 0 := by
  rw [← (skw_eq_self_iff η).mpr h]; exact trace_skw η

/-- Symmetric and skew-symmetric matrices are Frobenius-orthogonal. -/
theorem frob_sym_skw (σ τ : Mat2) : frob (sym σ) (skw τ) = 0 := by
  mat2_simp; ring

/-! ### The deviator and the identities (12) -/

theorem trace_dev (τ : Mat2) : (dev τ).trace = 0 := by
  mat2_simp; ring

/-- First identity of (12): `σ : (tr τ · I) = tr σ · tr τ`. -/
theorem frob_trace_smul_one (σ τ : Mat2) : frob σ (τ.trace • (1 : Mat2)) = σ.trace * τ.trace := by
  mat2_simp; ring

/-- Second identity of (12): `dev σ : dev τ = σ : τ - ½ tr σ · tr τ`. -/
theorem frob_dev_dev (σ τ : Mat2) : frob (dev σ) (dev τ) = frob σ τ - σ.trace * τ.trace / 2 := by
  mat2_simp; ring

/-- The deviator is Frobenius-orthogonal to multiples of the identity. -/
theorem frob_dev_one (σ : Mat2) : frob (dev σ) (1 : Mat2) = 0 := by
  mat2_simp; ring

/-- Pointwise inequality `|dev τ|² ≤ |τ|²` (p. 13). -/
theorem frobSq_dev_le (τ : Mat2) : frobSq (dev τ) ≤ frobSq τ := by
  mat2_simp; nlinarith [sq_nonneg (τ 0 0 + τ 1 1)]

/-- Pointwise inequality `(tr τ)² ≤ 2 |τ|²`, i.e. `|τ| ≥ c |tr τ|` with `c = 1/√2` (p. 13). -/
theorem trace_sq_le_two_mul_frobSq (τ : Mat2) : τ.trace ^ 2 ≤ 2 * frobSq τ := by
  mat2_simp; nlinarith [sq_nonneg (τ 0 0 - τ 1 1), sq_nonneg (τ 0 1), sq_nonneg (τ 1 0)]

/-- Norm version of `frobSq_dev_le`: `√(|dev τ|²) ≤ √(|τ|²)`. -/
theorem sqrt_frobSq_dev_le (τ : Mat2) : Real.sqrt (frobSq (dev τ)) ≤ Real.sqrt (frobSq τ) :=
  Real.sqrt_le_sqrt (frobSq_dev_le τ)

/-- Norm version of `trace_sq_le_two_mul_frobSq`: `|tr τ| ≤ √2 · √(|τ|²)`. -/
theorem abs_trace_le (τ : Mat2) : |τ.trace| ≤ Real.sqrt 2 * Real.sqrt (frobSq τ) := by
  rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (trace_sq_le_two_mul_frobSq τ)

/-! ### The material tensor `C` and its inverse -/

theorem trace_matC (lam mu : ℝ) (ε : Mat2) :
    (matC lam mu ε).trace = (2 * lam + 2 * mu) * ε.trace := by
  mat2_simp; ring

/-- `C ∘ C⁻¹ = id` (equation (4)). -/
theorem matC_matCinv (lam mu : ℝ) (hmu : mu ≠ 0) (hlm : mu + lam ≠ 0) (σ : Mat2) :
    matC lam mu (matCinv lam mu σ) = σ := by
  ext i j; fin_cases i <;> fin_cases j <;> mat2_simp <;> field_simp <;> ring

/-- `C⁻¹ ∘ C = id` (equation (4)). -/
theorem matCinv_matC (lam mu : ℝ) (hmu : mu ≠ 0) (hlm : mu + lam ≠ 0) (ε : Mat2) :
    matCinv lam mu (matC lam mu ε) = ε := by
  ext i j; fin_cases i <;> fin_cases j <;> mat2_simp <;> field_simp <;> ring

/-- `C` is symmetric with respect to the Frobenius product: `(C ε) : τ = ε : (C τ)`. -/
theorem frob_matC_symm (lam mu : ℝ) (ε τ : Mat2) :
    frob (matC lam mu ε) τ = frob ε (matC lam mu τ) := by
  mat2_simp; ring

/-- Explicit form of the energy: `(C ε) : ε = λ (tr ε)² + 2μ |ε|²`. -/
theorem frob_matC_self (lam mu : ℝ) (ε : Mat2) :
    frob (matC lam mu ε) ε = lam * ε.trace ^ 2 + 2 * mu * frobSq ε := by
  mat2_simp; ring

/-- `C` is positive semidefinite for `μ > 0`, `λ + μ > 0`. -/
theorem frob_matC_self_nonneg {lam mu : ℝ} (hmu : 0 < mu) (hlm : 0 < lam + mu) (ε : Mat2) :
    0 ≤ frob (matC lam mu ε) ε := by
  rw [frob_matC_self]
  have h1 := trace_sq_le_two_mul_frobSq ε
  nlinarith [sq_nonneg ε.trace]

/-- `C` is positive definite for `μ > 0`, `λ + μ > 0` (the Lamé parameters of the thesis are
positive, so `λ + μ > 0` holds automatically; the weaker hypothesis covers `λ ∈ (-μ, 0]`). -/
theorem frob_matC_self_pos {lam mu : ℝ} (hmu : 0 < mu) (hlm : 0 < lam + mu) {ε : Mat2}
    (hε : ε ≠ 0) : 0 < frob (matC lam mu ε) ε := by
  rw [frob_matC_self]
  have h1 := trace_sq_le_two_mul_frobSq ε
  have h2 : 0 < frobSq ε := by
    rcases (frobSq_nonneg ε).lt_or_eq with h | h
    · exact h
    · exact absurd ((frobSq_eq_zero_iff ε).mp h.symm) hε
  by_cases hlam : 0 ≤ lam
  · nlinarith [mul_nonneg hlam (sq_nonneg ε.trace), mul_pos hmu h2]
  · have hlam' : lam < 0 := not_le.mp hlam
    have h3 : lam * (2 * frobSq ε) ≤ lam * ε.trace ^ 2 :=
      mul_le_mul_of_nonpos_left h1 hlam'.le
    nlinarith [mul_pos hlm h2]

/-- `C⁻¹` is symmetric with respect to the Frobenius product, equation (6):
`(C⁻¹ σ) : τ = σ : (C⁻¹ τ)`. -/
theorem frob_matCinv_symm (lam mu : ℝ) (σ τ : Mat2) :
    frob (matCinv lam mu σ) τ = frob σ (matCinv lam mu τ) := by
  mat2_simp; ring

/-- Explicit form of equation (6): `(C⁻¹ σ) : τ = 1/(2μ) σ : τ - λ/(4μ(λ+μ)) tr σ tr τ`. -/
theorem frob_matCinv (lam mu : ℝ) (hmu : mu ≠ 0) (hlm : lam + mu ≠ 0) (σ τ : Mat2) :
    frob (matCinv lam mu σ) τ
      = 1 / (2 * mu) * frob σ τ - lam / (4 * mu * (lam + mu)) * (σ.trace * τ.trace) := by
  have hlm' : mu + lam ≠ 0 := by rwa [add_comm]
  mat2_simp; field_simp; ring

/-- Reformulation of the bilinear form `a(σ,τ)` via deviator and trace (p. 13):
`(C⁻¹ σ) : τ = 1/(2μ) dev σ : dev τ + 1/(4(λ+μ)) tr σ tr τ`. -/
theorem frob_matCinv_dev_trace (lam mu : ℝ) (hmu : mu ≠ 0) (hlm : lam + mu ≠ 0) (σ τ : Mat2) :
    frob (matCinv lam mu σ) τ
      = 1 / (2 * mu) * frob (dev σ) (dev τ) + 1 / (4 * (lam + mu)) * (σ.trace * τ.trace) := by
  rw [frob_matCinv lam mu hmu hlm, frob_dev_dev]
  field_simp
  ring

/-- `dev (C⁻¹ τ) = 1/(2μ) dev τ` (p. 14). -/
theorem dev_matCinv (lam mu : ℝ) (hmu : mu ≠ 0) (hlm : mu + lam ≠ 0) (τ : Mat2) :
    dev (matCinv lam mu τ) = (1 / (2 * mu)) • dev τ := by
  ext i j; fin_cases i <;> fin_cases j <;> mat2_simp <;> field_simp <;> ring

/-- Coercivity of `a` on all of `L²` with a `λ`-dependent constant (p. 13):
`(C⁻¹ τ) : τ ≥ 1/(2(λ+μ)) |τ|²`. -/
theorem frob_matCinv_self_ge {lam mu : ℝ} (hmu : 0 < mu) (hlam : 0 ≤ lam) (τ : Mat2) :
    1 / (2 * (lam + mu)) * frobSq τ ≤ frob (matCinv lam mu τ) τ := by
  have hlm : lam + mu ≠ 0 := by positivity
  rw [frob_matCinv lam mu hmu.ne' hlm]
  have h1 := trace_sq_le_two_mul_frobSq τ
  have hpos : 0 < 4 * mu * (lam + mu) := by positivity
  have key : 1 / (2 * mu) * frob τ τ - lam / (4 * mu * (lam + mu)) * (τ.trace * τ.trace)
      - 1 / (2 * (lam + mu)) * frobSq τ
      = lam * (2 * frobSq τ - τ.trace ^ 2) / (4 * mu * (lam + mu)) := by
    unfold frobSq; field_simp; ring
  rw [← sub_nonneg, key]
  exact div_nonneg (mul_nonneg hlam (sub_nonneg.mpr h1)) hpos.le

/-- `C η = 2μ η` for skew-symmetric `η` (p. 30: skew-symmetric matrices are trace free). -/
theorem matC_of_skew (lam mu : ℝ) {η : Mat2} (h : ηᵀ = -η) : matC lam mu η = (2 * mu) • η := by
  simp [matC, trace_eq_zero_of_skew h]

/-- `C⁻¹ η = 1/(2μ) η` for skew-symmetric `η`. -/
theorem matCinv_of_skew (lam mu : ℝ) {η : Mat2} (h : ηᵀ = -η) :
    matCinv lam mu η = (1 / (2 * mu)) • η := by
  simp [matCinv, trace_eq_zero_of_skew h]

/-- `(C γ) : σ = 2μ (γ : σ)` for skew-symmetric `γ`, the step used in the proofs of
Lemma 4.9 and Lemma 5.6. -/
theorem frob_matC_skew (lam mu : ℝ) {γ : Mat2} (h : γᵀ = -γ) (σ : Mat2) :
    frob (matC lam mu γ) σ = 2 * mu * frob γ σ := by
  rw [matC_of_skew lam mu h, frob_smul_left]

end

end MixedElasticEigenvalues
