import MixedElasticEigenvalues.Statements.Framework

/-!
# Theorem 3.1: quasi-optimality of the discrete source problem

Statement of Theorem 3.1 (p. 16, [5, Theorem 3.1]) in the abstract framework. The finite
element input — inclusion of the kernel (19), discrete inf-sup condition (20), coercivity
(16), continuity of `a`, and an `L²`-quasi-optimal Fortin operator — is collected in
`CeaHypotheses`. The proof is left open (`sorry`), see the comment at `cea_estimate`.
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace
open Filter Topology

noncomputable section

variable {H U : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] {ι : Type*}
  {div : H →ₗ[ℝ] U} {X S₀ : Submodule ℝ H} {μ : ℝ}

/-- Hypotheses of Theorem 3.1 (pp. 15–16) for a family of discrete spaces `D`:

* continuity of `a(σ, τ) = (C⁻¹σ, τ)` with constant `Ma`;
* inclusion of the kernel (19), `ker (Bₕ + Cₕ) ⊆ ker (B + C)`;
* coercivity of `a` on `ker (B + C)` with constant `α` (equation (16), which by Lemma 2.2
  holds uniformly in `λ`);
* the discrete inf-sup condition (20) with constant `β`, uniformly in the mesh;
* a Fortin operator `fort i : S₀ → Sₕ` (p. 16) that is quasi-optimal in `L²` with constant
  `Cfort`. The last hypothesis is not spelled out in Theorem 3.1 of the thesis, but the `L²`
  form of the estimate (rather than the `H(div)` form given by Brezzi's theory) requires
  it; for Falk's element it is provided by the construction of Section 3 together with
  Lee [21, Theorem 2], cf. (35). -/
structure CeaHypotheses (D : DiscreteFamily div X S₀ ι) (M : MaterialOperator X μ) where
  Ma : ℝ
  a_bound : ∀ σ τ : H, |⟪M.Cinv σ, τ⟫_ℝ| ≤ Ma * ‖σ‖ * ‖τ‖
  kernel_incl : ∀ i τ, IsDiscreteKernel div (D.S i) (D.Uh i) (D.Xh i) τ → IsKernel div X S₀ τ
  α : ℝ
  α_pos : 0 < α
  coercive : ∀ τ, IsKernel div X S₀ τ → α * ‖τ‖ ^ 2 ≤ ⟪M.Cinv τ, τ⟫_ℝ
  β : ℝ
  β_pos : 0 < β
  infsup : ∀ i, ∀ v ∈ D.Uh i, ∀ η ∈ D.Xh i, ∃ τ ∈ D.S i, τ ≠ 0 ∧
    β * hdivNorm div τ * (‖v‖ + ‖η‖) ≤ ⟪div τ, v⟫_ℝ + ⟪τ, η⟫_ℝ
  fort : ι → H → H
  fort_mem : ∀ i τ, fort i τ ∈ D.S i
  fortin : ∀ i τ, ∀ v ∈ D.Uh i, ∀ η ∈ D.Xh i,
    ⟪div (τ - fort i τ), v⟫_ℝ + ⟪τ - fort i τ, η⟫_ℝ = 0
  Cfort : ℝ
  fort_approx : ∀ i τ, ‖τ - fort i τ‖ ≤ Cfort * Metric.infDist τ (D.S i : Set H)

/-- Coercivity of `a` on the discrete kernel (p. 15): a direct consequence of the inclusion
of the kernel (19) and of the coercivity on `ker (B + C)`. -/
theorem CeaHypotheses.coercive_discrete {D : DiscreteFamily div X S₀ ι}
    {M : MaterialOperator X μ} (hyp : CeaHypotheses D M) (i : ι) {τ : H}
    (hτ : IsDiscreteKernel div (D.S i) (D.Uh i) (D.Xh i) τ) :
    hyp.α * ‖τ‖ ^ 2 ≤ ⟪M.Cinv τ, τ⟫_ℝ :=
  hyp.coercive τ (hyp.kernel_incl i τ hτ)

/-- **Theorem 3.1** (p. 16, [5, Theorem 3.1]). Suppose the spaces `Sₕ, Uₕ, Xₕ` satisfy the
inclusion of the kernel property (19) and the inf-sup condition (20). Then (17) admits a
unique solution `(σₕ, uₕ, γₕ)` and
`‖σ - σₕ‖₀ + ‖u - uₕ‖₀ + ‖γ - γₕ‖₀ ≤ C (inf ‖σ - τₕ‖₀ + inf ‖u - vₕ‖₀ + inf ‖γ - ηₕ‖₀)`
with `C` independent of the mesh and of the right-hand side `f`. -/
theorem cea_estimate (D : DiscreteFamily div X S₀ ι) (M : MaterialOperator X μ)
    (hyp : CeaHypotheses D M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (f : U),
      (∃ q : DiscreteMixedSource div M (D.S i) (D.Uh i) (D.Xh i) f,
        ∀ q' : DiscreteMixedSource div M (D.S i) (D.Uh i) (D.Xh i) f,
          q'.σₕ = q.σₕ ∧ q'.uₕ = q.uₕ ∧ q'.γₕ = q.γₕ) ∧
      ∀ (p : MixedSource div X S₀ M f)
        (q : DiscreteMixedSource div M (D.S i) (D.Uh i) (D.Xh i) f),
        ‖p.σ - q.σₕ‖ + ‖p.u - q.uₕ‖ + ‖p.γ - q.γₕ‖
          ≤ C * (Metric.infDist p.σ (D.S i : Set H) + Metric.infDist p.u (D.Uh i : Set U)
              + Metric.infDist p.γ (D.Xh i : Set H)) := by
  -- Not proved here. Uniqueness: for `f = 0`, `σₕ ∈ ker (Bₕ + Cₕ)`, so `σₕ = 0` by
  -- `coercive_discrete`, and then `uₕ = γₕ = 0` by the inf-sup condition; existence
  -- follows from uniqueness by finite dimensionality. Quasi-optimality: `σₕ - fort σ` lies
  -- in the discrete kernel, so coercivity plus continuity bound `‖σₕ - fort σ‖` by
  -- `‖σ - fort σ‖` and `inf ‖γ - ηₕ‖`; the inf-sup condition then bounds `‖uₕ - vₕ‖ +
  -- ‖γₕ - ηₕ‖` by `Ma ‖σ - σₕ‖ + ‖u - vₕ‖ + ‖γ - ηₕ‖` (Brezzi [9], Boffi–Brezzi–Fortin
  -- [5]). This is a page of estimates with `Metric.infDist` that was not carried out.
  sorry

/-- The hypotheses of Theorem 3.1 are satisfiable: the trivial model `H = U = ℝ`, `div = id`,
`C = id`, `Sₕ = Uₕ = ℝ`, `Xₕ = ⊥` satisfies them with `Ma = α = 1`, `β = 1/2`, `Cfort = 1`. -/
example (μ : ℝ) : CeaHypotheses trivialFamily (trivialMaterial μ) where
  Ma := 1
  a_bound := fun σ τ => by simpa [trivialMaterial] using abs_real_inner_le_norm σ τ
  kernel_incl := fun i τ hτ => ⟨Submodule.mem_top, fun v => hτ.2.1 v Submodule.mem_top,
    fun η hη => by simp [(Submodule.mem_bot ℝ).mp hη]⟩
  α := 1
  α_pos := one_pos
  coercive := fun τ _ => by simp [trivialMaterial]
  β := 1 / 2
  β_pos := by norm_num
  infsup := fun i v _ η hη => by
    simp only [trivialFamily, Submodule.mem_bot] at hη
    subst hη
    by_cases hv : v = 0
    · exact ⟨1, Submodule.mem_top, one_ne_zero, by simp [hv]⟩
    · refine ⟨v, Submodule.mem_top, hv, ?_⟩
      simp only [hdivNorm, LinearMap.id_coe, id_eq, norm_zero, add_zero, inner_zero_right,
        real_inner_self_eq_norm_sq]
      nlinarith [norm_nonneg v]
  fort := fun _ τ => τ
  fort_mem := fun _ _ => Submodule.mem_top
  fortin := fun _ _ _ _ _ _ => by simp
  Cfort := 1
  fort_approx := fun i τ => by
    have := Metric.infDist_nonneg (x := τ) (s := (trivialFamily.S i : Set ℝ))
    simpa using this

end

end MixedElasticEigenvalues
