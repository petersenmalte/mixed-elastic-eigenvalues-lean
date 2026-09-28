import MixedElasticEigenvalues.Statements.Cea

/-!
# Discrete solution operators (roadmap step 2)

Theorem 3.1 (`cea_existence`, `cea_unique`) makes the discrete source problem (17) uniquely
solvable on every mesh. This file turns that into actual data:

* `CeaHypotheses.solve` — the discrete solution of (17) for a right-hand side `f`;
* `DiscreteMixedSource.add`, `DiscreteMixedSource.smul` — superposition of solutions;
* `CeaHypotheses.σOp`, `uOp`, `γOp` — the discrete solution operators `f ↦ σₕ, uₕ, γₕ`,
  which are linear by uniqueness; `uOp i` is the discrete solution operator `Tₕ` of the
  eigenvalue analysis (Chapter 4);
* `DiscreteMixedSource.div_eq` — for `f ∈ Uₕ` the second equation of (17) holds strongly,
  `div σₕ = -f` (because `div Σₕ ⊆ Uₕ`);
* `uOp_eigenpair`, `eigenpairOfEigenvector` — the discrete eigenvalue problem (37) is the
  eigenvalue problem `Tₕ uₕ = κₕ⁻¹ uₕ` of the discrete solution operator on `Uₕ`;
* `solve_estimate` — Theorem 3.1 for the constructed solutions.
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace

noncomputable section

variable {H U : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] {ι : Type*}
  {div : H →ₗ[ℝ] U} {X S₀ : Submodule ℝ H} {μ : ℝ}

/-! ### Superposition of discrete solutions -/

namespace DiscreteMixedSource

variable {M : MaterialOperator X μ} {Sₕ Xₕ : Submodule ℝ H} {Uₕ : Submodule ℝ U}

/-- The sum of solutions for `f` and `g` solves (17) for `f + g`. -/
def add {f g : U} (q₁ : DiscreteMixedSource div M Sₕ Uₕ Xₕ f)
    (q₂ : DiscreteMixedSource div M Sₕ Uₕ Xₕ g) : DiscreteMixedSource div M Sₕ Uₕ Xₕ (f + g) where
  σₕ := q₁.σₕ + q₂.σₕ
  uₕ := q₁.uₕ + q₂.uₕ
  γₕ := q₁.γₕ + q₂.γₕ
  σₕ_mem := Sₕ.add_mem q₁.σₕ_mem q₂.σₕ_mem
  uₕ_mem := Uₕ.add_mem q₁.uₕ_mem q₂.uₕ_mem
  γₕ_mem := Xₕ.add_mem q₁.γₕ_mem q₂.γₕ_mem
  eq₁ τ hτ := by
    have h₁ := q₁.eq₁ τ hτ
    have h₂ := q₂.eq₁ τ hτ
    simp only [map_add, inner_add_left, inner_add_right]
    linarith
  eq₂ v hv := by
    have h₁ := q₁.eq₂ v hv
    have h₂ := q₂.eq₂ v hv
    simp only [map_add, inner_add_left]
    linarith
  eq₃ η hη := by
    have h₁ := q₁.eq₃ η hη
    have h₂ := q₂.eq₃ η hη
    simp only [inner_add_left]
    linarith

/-- A multiple of a solution for `f` solves (17) for `c • f`. -/
def smul (c : ℝ) {f : U} (q : DiscreteMixedSource div M Sₕ Uₕ Xₕ f) :
    DiscreteMixedSource div M Sₕ Uₕ Xₕ (c • f) where
  σₕ := c • q.σₕ
  uₕ := c • q.uₕ
  γₕ := c • q.γₕ
  σₕ_mem := Sₕ.smul_mem c q.σₕ_mem
  uₕ_mem := Uₕ.smul_mem c q.uₕ_mem
  γₕ_mem := Xₕ.smul_mem c q.γₕ_mem
  eq₁ τ hτ := by
    have h := q.eq₁ τ hτ
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    linear_combination c * h
  eq₂ v hv := by
    have h := q.eq₂ v hv
    simp only [map_smul, real_inner_smul_left]
    linear_combination c * h
  eq₃ η hη := by
    have h := q.eq₃ η hη
    simp only [real_inner_smul_left]
    linear_combination c * h

/-- For a right-hand side `f ∈ Uₕ` the second equation of (17) holds strongly:
`div σₕ = -f`, since `div σₕ + f ∈ Uₕ` is orthogonal to `Uₕ`. -/
theorem div_eq {f : U} (q : DiscreteMixedSource div M Sₕ Uₕ Xₕ f)
    (hdiv : ∀ τ ∈ Sₕ, div τ ∈ Uₕ) (hf : f ∈ Uₕ) : div q.σₕ = -f := by
  have hmem : div q.σₕ + f ∈ Uₕ := Uₕ.add_mem (hdiv _ q.σₕ_mem) hf
  have h := q.eq₂ _ hmem
  have h0 : ⟪div q.σₕ + f, div q.σₕ + f⟫_ℝ = 0 := by
    rw [inner_add_left, h]; ring
  rw [inner_self_eq_zero] at h0
  exact eq_neg_of_add_eq_zero_left h0

end DiscreteMixedSource

/-- A discrete eigenpair `(κₕ, σₕ, uₕ, γₕ)` of (37) solves the discrete source problem (17)
with right-hand side `f = κₕ uₕ`. -/
def DiscreteMixedEigenpair.toSource {M : MaterialOperator X μ} {Sₕ Xₕ : Submodule ℝ H}
    {Uₕ : Submodule ℝ U} (q : DiscreteMixedEigenpair div M Sₕ Uₕ Xₕ) :
    DiscreteMixedSource div M Sₕ Uₕ Xₕ (q.κₕ • q.uₕ) where
  σₕ := q.σₕ
  uₕ := q.uₕ
  γₕ := q.γₕ
  σₕ_mem := q.σₕ_mem
  uₕ_mem := q.uₕ_mem
  γₕ_mem := q.γₕ_mem
  eq₁ := q.eq₁
  eq₂ v _ := by rw [q.eq₂, neg_smul, inner_neg_left]
  eq₃ := q.eq₃

/-! ### The discrete solution operators -/

namespace CeaHypotheses

variable {D : DiscreteFamily div X S₀ ι} {M : MaterialOperator X μ} (hyp : CeaHypotheses D M)

/-- The discrete solution of the source problem (17) on mesh `i` with right-hand side `f`,
which exists by `cea_existence` (Theorem 3.1). -/
def solve (i : ι) (f : U) : DiscreteMixedSource div M (D.S i) (D.Uh i) (D.Xh i) f :=
  Classical.choice (cea_existence D M hyp i f)

/-- Every discrete solution coincides with `hyp.solve i f` (uniqueness in Theorem 3.1). -/
theorem eq_solve (i : ι) {f : U} (q : DiscreteMixedSource div M (D.S i) (D.Uh i) (D.Xh i) f) :
    q.σₕ = (hyp.solve i f).σₕ ∧ q.uₕ = (hyp.solve i f).uₕ ∧ q.γₕ = (hyp.solve i f).γₕ :=
  cea_unique hyp i f q (hyp.solve i f)

theorem solve_add (i : ι) (f g : U) :
    (hyp.solve i (f + g)).σₕ = (hyp.solve i f).σₕ + (hyp.solve i g).σₕ ∧
      (hyp.solve i (f + g)).uₕ = (hyp.solve i f).uₕ + (hyp.solve i g).uₕ ∧
      (hyp.solve i (f + g)).γₕ = (hyp.solve i f).γₕ + (hyp.solve i g).γₕ :=
  cea_unique hyp i (f + g) (hyp.solve i (f + g)) ((hyp.solve i f).add (hyp.solve i g))

theorem solve_smul (i : ι) (c : ℝ) (f : U) :
    (hyp.solve i (c • f)).σₕ = c • (hyp.solve i f).σₕ ∧
      (hyp.solve i (c • f)).uₕ = c • (hyp.solve i f).uₕ ∧
      (hyp.solve i (c • f)).γₕ = c • (hyp.solve i f).γₕ :=
  cea_unique hyp i (c • f) (hyp.solve i (c • f)) ((hyp.solve i f).smul c)

/-- The discrete stress solution operator `f ↦ σₕ`. -/
def σOp (i : ι) : U →ₗ[ℝ] H where
  toFun f := (hyp.solve i f).σₕ
  map_add' f g := (hyp.solve_add i f g).1
  map_smul' c f := (hyp.solve_smul i c f).1

/-- The discrete displacement solution operator `Tₕ : f ↦ uₕ` (Chapter 4). -/
def uOp (i : ι) : U →ₗ[ℝ] U where
  toFun f := (hyp.solve i f).uₕ
  map_add' f g := (hyp.solve_add i f g).2.1
  map_smul' c f := (hyp.solve_smul i c f).2.1

/-- The discrete rotation solution operator `f ↦ γₕ`. -/
def γOp (i : ι) : U →ₗ[ℝ] H where
  toFun f := (hyp.solve i f).γₕ
  map_add' f g := (hyp.solve_add i f g).2.2
  map_smul' c f := (hyp.solve_smul i c f).2.2

theorem σOp_apply (i : ι) (f : U) : hyp.σOp i f = (hyp.solve i f).σₕ := rfl
theorem uOp_apply (i : ι) (f : U) : hyp.uOp i f = (hyp.solve i f).uₕ := rfl
theorem γOp_apply (i : ι) (f : U) : hyp.γOp i f = (hyp.solve i f).γₕ := rfl

theorem σOp_mem (i : ι) (f : U) : hyp.σOp i f ∈ D.S i := (hyp.solve i f).σₕ_mem
theorem uOp_mem (i : ι) (f : U) : hyp.uOp i f ∈ D.Uh i := (hyp.solve i f).uₕ_mem
theorem γOp_mem (i : ι) (f : U) : hyp.γOp i f ∈ D.Xh i := (hyp.solve i f).γₕ_mem

/-- For `f ∈ Uₕ`: `div (σₕ f) = -f`. -/
theorem div_σOp (i : ι) {f : U} (hf : f ∈ D.Uh i) : div (hyp.σOp i f) = -f :=
  (hyp.solve i f).div_eq (D.div_mem i) hf

/-- Discrete eigenpairs are eigenvectors of the discrete solution operator:
`κₕ Tₕ uₕ = uₕ`. -/
theorem uOp_eigenpair (i : ι) (q : DiscreteMixedEigenpair div M (D.S i) (D.Uh i) (D.Xh i)) :
    q.κₕ • hyp.uOp i q.uₕ = q.uₕ := by
  rw [← map_smul]
  exact ((hyp.eq_solve i q.toSource).2.1).symm

/-- The other components of a discrete eigenpair are recovered from the solution operators:
`σₕ = σOp (κₕ uₕ)`, `γₕ = γOp (κₕ uₕ)`. -/
theorem eigenpair_eq_ops (i : ι) (q : DiscreteMixedEigenpair div M (D.S i) (D.Uh i) (D.Xh i)) :
    q.σₕ = hyp.σOp i (q.κₕ • q.uₕ) ∧ q.γₕ = hyp.γOp i (q.κₕ • q.uₕ) :=
  ⟨(hyp.eq_solve i q.toSource).1, (hyp.eq_solve i q.toSource).2.2⟩

/-- Conversely, an eigenvector `Tₕ w = λ w` with `λ ≠ 0` and `w ∈ Uₕ` yields a discrete
eigenpair of (37) with `κₕ = λ⁻¹` and `uₕ = w`. -/
def eigenpairOfEigenvector (i : ι) {w : U} (hw : w ∈ D.Uh i) {lam : ℝ} (hlam : lam ≠ 0)
    (h : hyp.uOp i w = lam • w) : DiscreteMixedEigenpair div M (D.S i) (D.Uh i) (D.Xh i) where
  κₕ := lam⁻¹
  σₕ := lam⁻¹ • hyp.σOp i w
  uₕ := w
  γₕ := lam⁻¹ • hyp.γOp i w
  σₕ_mem := (D.S i).smul_mem _ (hyp.σOp_mem i w)
  uₕ_mem := hw
  γₕ_mem := (D.Xh i).smul_mem _ (hyp.γOp_mem i w)
  eq₁ τ hτ := by
    have h1 := (hyp.solve i w).eq₁ τ hτ
    have e : ⟪div τ, w⟫_ℝ = lam⁻¹ * ⟪div τ, (hyp.solve i w).uₕ⟫_ℝ := by
      rw [← uOp_apply, h, real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
    rw [e, map_smul, real_inner_smul_left, real_inner_smul_left, σOp_apply, γOp_apply]
    linear_combination lam⁻¹ * h1
  eq₂ := by rw [map_smul, hyp.div_σOp i hw, smul_neg, neg_smul]
  eq₃ η hη := by rw [real_inner_smul_left, σOp_apply, (hyp.solve i w).eq₃ η hη, mul_zero]

@[simp] theorem eigenpairOfEigenvector_κₕ (i : ι) {w : U} (hw : w ∈ D.Uh i) {lam : ℝ}
    (hlam : lam ≠ 0) (h : hyp.uOp i w = lam • w) :
    (hyp.eigenpairOfEigenvector i hw hlam h).κₕ = lam⁻¹ := rfl

@[simp] theorem eigenpairOfEigenvector_uₕ (i : ι) {w : U} (hw : w ∈ D.Uh i) {lam : ℝ}
    (hlam : lam ≠ 0) (h : hyp.uOp i w = lam • w) :
    (hyp.eigenpairOfEigenvector i hw hlam h).uₕ = w := rfl

/-- **Theorem 3.1** for the constructed discrete solutions: with `C` independent of the mesh
and of `f`, `‖σ - σₕ‖₀ + ‖u - uₕ‖₀ + ‖γ - γₕ‖₀ ≤ C (inf ‖σ - τₕ‖₀ + inf ‖u - vₕ‖₀ +
inf ‖γ - ηₕ‖₀)` for every solution `(σ, u, γ)` of (11). -/
theorem solve_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (f : U) (p : MixedSource div X S₀ M f),
      ‖p.σ - hyp.σOp i f‖ + ‖p.u - hyp.uOp i f‖ + ‖p.γ - hyp.γOp i f‖
        ≤ C * (Metric.infDist p.σ (D.S i : Set H) + Metric.infDist p.u (D.Uh i : Set U)
            + Metric.infDist p.γ (D.Xh i : Set H)) := by
  obtain ⟨C, hC, h⟩ := cea_estimate D M hyp
  exact ⟨C, hC, fun i f p => h i f p (hyp.solve i f)⟩

end CeaHypotheses

end

end MixedElasticEigenvalues
