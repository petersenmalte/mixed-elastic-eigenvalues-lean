import MixedElasticEigenvalues.Statements.DiscreteSolution

/-!
# The continuous source problem and its solution operator (roadmap step 3)

The source problem (11) is uniquely solvable by Brezzi's theory (Proposition 2.1,
Lemma 2.2). Uniqueness only needs coercivity (16) on `ker (B + C)` and the continuous
inf-sup condition, and is proved here (`source_unique`). Existence requires the Hilbert
space theory of `H(div)` on a domain, which is not available at this level; it enters as the
hypothesis `exists_sol` of `SourceHypotheses`. From this:

* `SourceHypotheses.solve`, `σOp`, `uOp`, `γOp` — the solution operators `f ↦ σ, u, γ`,
  linear by uniqueness; `uOp` is the solution operator `T` of Chapter 4;
* `uOp_eigenpair`, `eigenpairOfEigenvector` — the eigenvalue problem (36) is the eigenvalue
  problem `T u = κ⁻¹ u` of the solution operator;
* `op_error` — Theorem 3.1 as an estimate of the operator errors `T f - Tₕ f` (and likewise
  for `σ`, `γ`), for the constructed continuous and discrete solutions.
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace

noncomputable section

variable {H U : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] {ι : Type*}
  {div : H →ₗ[ℝ] U} {X S₀ : Submodule ℝ H} {μ : ℝ}

/-! ### Superposition of continuous solutions -/

namespace MixedSource

variable {M : MaterialOperator X μ}

/-- The sum of solutions of (11) for `f` and `g` solves (11) for `f + g`. -/
def add {f g : U} (p₁ : MixedSource div X S₀ M f) (p₂ : MixedSource div X S₀ M g) :
    MixedSource div X S₀ M (f + g) where
  σ := p₁.σ + p₂.σ
  u := p₁.u + p₂.u
  γ := p₁.γ + p₂.γ
  σ_mem := S₀.add_mem p₁.σ_mem p₂.σ_mem
  γ_mem := X.add_mem p₁.γ_mem p₂.γ_mem
  eq₁ τ hτ := by
    have h₁ := p₁.eq₁ τ hτ
    have h₂ := p₂.eq₁ τ hτ
    simp only [map_add, inner_add_left, inner_add_right]
    linarith
  eq₂ v := by
    have h₁ := p₁.eq₂ v
    have h₂ := p₂.eq₂ v
    simp only [map_add, inner_add_left]
    linarith
  eq₃ η hη := by
    have h₁ := p₁.eq₃ η hη
    have h₂ := p₂.eq₃ η hη
    simp only [inner_add_left]
    linarith

/-- A multiple of a solution of (11) for `f` solves (11) for `c • f`. -/
def smul (c : ℝ) {f : U} (p : MixedSource div X S₀ M f) : MixedSource div X S₀ M (c • f) where
  σ := c • p.σ
  u := c • p.u
  γ := c • p.γ
  σ_mem := S₀.smul_mem c p.σ_mem
  γ_mem := X.smul_mem c p.γ_mem
  eq₁ τ hτ := by
    have h := p.eq₁ τ hτ
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    linear_combination c * h
  eq₂ v := by
    have h := p.eq₂ v
    simp only [map_smul, real_inner_smul_left]
    linear_combination c * h
  eq₃ η hη := by
    have h := p.eq₃ η hη
    simp only [real_inner_smul_left]
    linear_combination c * h

end MixedSource

/-- An eigenpair `(κ, σ, u, γ)` of (36) solves the source problem (11) with `f = κ u`. -/
def MixedEigenpair.toSource {M : MaterialOperator X μ} (p : MixedEigenpair div X S₀ M) :
    MixedSource div X S₀ M (p.κ • p.u) where
  σ := p.σ
  u := p.u
  γ := p.γ
  σ_mem := p.σ_mem
  γ_mem := p.γ_mem
  eq₁ := p.eq₁
  eq₂ v := by rw [p.eq₂, real_inner_smul_left]; ring
  eq₃ := p.eq₃

/-! ### Uniqueness and the solution operators -/

/-- Hypotheses for the continuous source problem (11): coercivity (16) of `a` on
`ker (B + C)`, the continuous inf-sup condition (Proposition 2.1, p. 13), and existence of
solutions (Brezzi's theorem, which needs the Hilbert space structure of `H(div)`). -/
structure SourceHypotheses (div : H →ₗ[ℝ] U) (X S₀ : Submodule ℝ H) (M : MaterialOperator X μ)
    where
  α : ℝ
  α_pos : 0 < α
  coercive : ∀ τ, IsKernel div X S₀ τ → α * ‖τ‖ ^ 2 ≤ ⟪M.Cinv τ, τ⟫_ℝ
  β : ℝ
  β_pos : 0 < β
  infsup : ∀ v : U, ∀ η ∈ X, ∃ τ ∈ S₀, τ ≠ 0 ∧
    β * hdivNorm div τ * (‖v‖ + ‖η‖) ≤ ⟪div τ, v⟫_ℝ + ⟪τ, η⟫_ℝ
  exists_sol : ∀ f : U, Nonempty (MixedSource div X S₀ M f)

namespace SourceHypotheses

variable {M : MaterialOperator X μ} (hyp : SourceHypotheses div X S₀ M)

include hyp in
/-- Uniqueness for the source problem (11), from coercivity on the kernel and the continuous
inf-sup condition (the continuous analogue of `cea_unique`). -/
theorem source_unique (f : U) (p p' : MixedSource div X S₀ M f) :
    p.σ = p'.σ ∧ p.u = p'.u ∧ p.γ = p'.γ := by
  have hdiff : ∀ τ ∈ S₀, ⟪M.Cinv (p.σ - p'.σ), τ⟫_ℝ + ⟪div τ, p.u - p'.u⟫_ℝ
      + ⟪p.γ - p'.γ, τ⟫_ℝ = 0 := by
    intro τ hτ
    simp only [map_sub, inner_sub_left, inner_sub_right]
    linarith [p.eq₁ τ hτ, p'.eq₁ τ hτ]
  have hdiv : ∀ v : U, ⟪div (p.σ - p'.σ), v⟫_ℝ = 0 := by
    intro v
    rw [map_sub, inner_sub_left, p.eq₂ v, p'.eq₂ v, sub_self]
  have hX : ∀ η ∈ X, ⟪p.σ - p'.σ, η⟫_ℝ = 0 := by
    intro η hη
    rw [inner_sub_left, p.eq₃ η hη, p'.eq₃ η hη, sub_self]
  have hker : IsKernel div X S₀ (p.σ - p'.σ) := ⟨S₀.sub_mem p.σ_mem p'.σ_mem, hdiv, hX⟩
  -- the stress difference vanishes by coercivity on the kernel
  have hσ : p.σ - p'.σ = 0 := by
    have h := hdiff _ hker.1
    have hξ : ⟪p.γ - p'.γ, p.σ - p'.σ⟫_ℝ = 0 :=
      (real_inner_comm _ _).trans (hX _ (X.sub_mem p.γ_mem p'.γ_mem))
    rw [hdiv, hξ, add_zero, add_zero] at h
    have hc := hyp.coercive _ hker
    rw [h] at hc
    have : ‖p.σ - p'.σ‖ ^ 2 ≤ 0 := by
      by_contra hne
      rw [not_le] at hne
      have := mul_pos hyp.α_pos hne
      linarith
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp
      (le_antisymm this (sq_nonneg _)))
  -- the displacement and rotation differences vanish by the inf-sup condition
  obtain ⟨τ, hτ, hτ0, hβ⟩ := hyp.infsup (p.u - p'.u) (p.γ - p'.γ) (X.sub_mem p.γ_mem p'.γ_mem)
  have h := hdiff τ hτ
  rw [hσ, map_zero, inner_zero_left, zero_add] at h
  rw [real_inner_comm (p.γ - p'.γ) τ, h] at hβ
  have hτpos : 0 < hdivNorm div τ :=
    lt_of_lt_of_le (norm_pos_iff.mpr hτ0) (norm_le_hdivNorm div τ)
  have hsum : ‖p.u - p'.u‖ + ‖p.γ - p'.γ‖ ≤ 0 := by
    by_contra hne
    rw [not_le] at hne
    have := mul_pos (mul_pos hyp.β_pos hτpos) hne
    linarith
  have hu : ‖p.u - p'.u‖ = 0 := le_antisymm (by linarith [norm_nonneg (p.γ - p'.γ)])
    (norm_nonneg _)
  have hγ : ‖p.γ - p'.γ‖ = 0 := le_antisymm (by linarith [norm_nonneg (p.u - p'.u)])
    (norm_nonneg _)
  exact ⟨sub_eq_zero.mp hσ, sub_eq_zero.mp (norm_eq_zero.mp hu),
    sub_eq_zero.mp (norm_eq_zero.mp hγ)⟩

/-- The solution of the source problem (11) with right-hand side `f`. -/
def solve (f : U) : MixedSource div X S₀ M f := Classical.choice (hyp.exists_sol f)

theorem eq_solve {f : U} (p : MixedSource div X S₀ M f) :
    p.σ = (hyp.solve f).σ ∧ p.u = (hyp.solve f).u ∧ p.γ = (hyp.solve f).γ :=
  hyp.source_unique f p (hyp.solve f)

theorem solve_add (f g : U) :
    (hyp.solve (f + g)).σ = (hyp.solve f).σ + (hyp.solve g).σ ∧
      (hyp.solve (f + g)).u = (hyp.solve f).u + (hyp.solve g).u ∧
      (hyp.solve (f + g)).γ = (hyp.solve f).γ + (hyp.solve g).γ :=
  hyp.source_unique (f + g) (hyp.solve (f + g)) ((hyp.solve f).add (hyp.solve g))

theorem solve_smul (c : ℝ) (f : U) :
    (hyp.solve (c • f)).σ = c • (hyp.solve f).σ ∧
      (hyp.solve (c • f)).u = c • (hyp.solve f).u ∧
      (hyp.solve (c • f)).γ = c • (hyp.solve f).γ :=
  hyp.source_unique (c • f) (hyp.solve (c • f)) ((hyp.solve f).smul c)

/-- The stress solution operator `f ↦ σ`. -/
def σOp : U →ₗ[ℝ] H where
  toFun f := (hyp.solve f).σ
  map_add' f g := (hyp.solve_add f g).1
  map_smul' c f := (hyp.solve_smul c f).1

/-- The displacement solution operator `T : f ↦ u` (Chapter 4). -/
def uOp : U →ₗ[ℝ] U where
  toFun f := (hyp.solve f).u
  map_add' f g := (hyp.solve_add f g).2.1
  map_smul' c f := (hyp.solve_smul c f).2.1

/-- The rotation solution operator `f ↦ γ`. -/
def γOp : U →ₗ[ℝ] H where
  toFun f := (hyp.solve f).γ
  map_add' f g := (hyp.solve_add f g).2.2
  map_smul' c f := (hyp.solve_smul c f).2.2

theorem σOp_apply (f : U) : hyp.σOp f = (hyp.solve f).σ := rfl
theorem uOp_apply (f : U) : hyp.uOp f = (hyp.solve f).u := rfl
theorem γOp_apply (f : U) : hyp.γOp f = (hyp.solve f).γ := rfl

/-- `div (σ f) = -f`: the second equation of (11) holds strongly. -/
theorem div_σOp (f : U) : div (hyp.σOp f) = -f := by
  have h := (hyp.solve f).eq₂ (div (hyp.σOp f) + f)
  have h0 : ⟪div (hyp.σOp f) + f, div (hyp.σOp f) + f⟫_ℝ = 0 := by
    rw [σOp_apply] at h ⊢
    rw [inner_add_left, h]; ring
  rw [inner_self_eq_zero] at h0
  exact eq_neg_of_add_eq_zero_left h0

/-- Eigenpairs of (36) are eigenvectors of the solution operator: `κ T u = u`. -/
theorem uOp_eigenpair (p : MixedEigenpair div X S₀ M) : p.κ • hyp.uOp p.u = p.u := by
  rw [← map_smul]
  exact ((hyp.eq_solve p.toSource).2.1).symm

/-- Conversely, an eigenvector `T w = λ w` with `λ ≠ 0` yields an eigenpair of (36) with
`κ = λ⁻¹` and `u = w`. -/
def eigenpairOfEigenvector {w : U} {lam : ℝ} (hlam : lam ≠ 0) (h : hyp.uOp w = lam • w) :
    MixedEigenpair div X S₀ M where
  κ := lam⁻¹
  σ := lam⁻¹ • hyp.σOp w
  u := w
  γ := lam⁻¹ • hyp.γOp w
  σ_mem := S₀.smul_mem _ (hyp.solve w).σ_mem
  γ_mem := X.smul_mem _ (hyp.solve w).γ_mem
  eq₁ τ hτ := by
    have h1 := (hyp.solve w).eq₁ τ hτ
    have e : ⟪div τ, w⟫_ℝ = lam⁻¹ * ⟪div τ, (hyp.solve w).u⟫_ℝ := by
      rw [← uOp_apply, h, real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
    rw [e, map_smul, real_inner_smul_left, real_inner_smul_left, σOp_apply, γOp_apply]
    linear_combination lam⁻¹ * h1
  eq₂ v := by
    rw [map_smul, real_inner_smul_left, σOp_apply, (hyp.solve w).eq₂ v]
    ring
  eq₃ η hη := by rw [real_inner_smul_left, σOp_apply, (hyp.solve w).eq₃ η hη, mul_zero]

/-- **Theorem 3.1** for the solution operators: `‖σ f - σₕ f‖₀ + ‖T f - Tₕ f‖₀ +
‖γ f - γₕ f‖₀ ≤ C (inf ‖σ f - τₕ‖₀ + inf ‖T f - vₕ‖₀ + inf ‖γ f - ηₕ‖₀)` with `C`
independent of the mesh and of `f`. -/
theorem op_error {D : DiscreteFamily div X S₀ ι} (hd : CeaHypotheses D M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (f : U),
      ‖hyp.σOp f - hd.σOp i f‖ + ‖hyp.uOp f - hd.uOp i f‖ + ‖hyp.γOp f - hd.γOp i f‖
        ≤ C * (Metric.infDist (hyp.σOp f) (D.S i : Set H)
            + Metric.infDist (hyp.uOp f) (D.Uh i : Set U)
            + Metric.infDist (hyp.γOp f) (D.Xh i : Set H)) := by
  obtain ⟨C, hC, h⟩ := hd.solve_estimate
  exact ⟨C, hC, fun i f => h i f (hyp.solve f)⟩

end SourceHypotheses

end

end MixedElasticEigenvalues
