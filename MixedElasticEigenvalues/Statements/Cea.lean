import MixedElasticEigenvalues.Statements.Framework

/-!
# Theorem 3.1: quasi-optimality of the discrete source problem

Theorem 3.1 (p. 16, [5, Theorem 3.1]) in the abstract framework. The finite element
input — inclusion of the kernel (19), discrete inf-sup condition (20), coercivity (16),
continuity of `a`, and an `L²`-quasi-optimal Fortin operator — is collected in
`CeaHypotheses`.

The theorem is split into its three assertions:

* `cea_unique` — the discrete problem (17) has at most one solution. Proved.
* `cea_quasi_optimal` / `cea_estimate` — the error estimate, in best-approximation form
  and in the `inf` form of the thesis. Proved.
* `cea_existence` — existence of a discrete solution, by finite-dimensional duality.
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
  Ma_nonneg : 0 ≤ Ma
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
  Cfort_nonneg : 0 ≤ Cfort
  fort_approx : ∀ i τ, ‖τ - fort i τ‖ ≤ Cfort * Metric.infDist τ (D.S i : Set H)

/-- Coercivity of `a` on the discrete kernel (p. 15): a direct consequence of the inclusion
of the kernel (19) and of the coercivity on `ker (B + C)`. -/
theorem CeaHypotheses.coercive_discrete {D : DiscreteFamily div X S₀ ι}
    {M : MaterialOperator X μ} (hyp : CeaHypotheses D M) (i : ι) {τ : H}
    (hτ : IsDiscreteKernel div (D.S i) (D.Uh i) (D.Xh i) τ) :
    hyp.α * ‖τ‖ ^ 2 ≤ ⟪M.Cinv τ, τ⟫_ℝ :=
  hyp.coercive τ (hyp.kernel_incl i τ hτ)

/-- An element of `ker (Bₕ + Cₕ)` is divergence free, because `div Σₕ ⊆ Uₕ` for Falk's
element (p. 23) makes `div τₕ` orthogonal to itself (p. 28). -/
theorem div_eq_zero_of_isDiscreteKernel (D : DiscreteFamily div X S₀ ι) (i : ι) {τ : H}
    (hτ : IsDiscreteKernel div (D.S i) (D.Uh i) (D.Xh i) τ) : div τ = 0 :=
  inner_self_eq_zero.mp (hτ.2.1 (div τ) (D.div_mem i τ hτ.1))

/-- Uniqueness part of **Theorem 3.1** (p. 16): the discrete problem (17) has at most one
solution. Only the inclusion of the kernel (19), the coercivity (16) and the discrete
inf-sup condition (20) are used. -/
theorem cea_unique {D : DiscreteFamily div X S₀ ι} {M : MaterialOperator X μ}
    (hyp : CeaHypotheses D M) (i : ι) (f : U)
    (q q' : DiscreteMixedSource div M (D.S i) (D.Uh i) (D.Xh i) f) :
    q.σₕ = q'.σₕ ∧ q.uₕ = q'.uₕ ∧ q.γₕ = q'.γₕ := by
  set e := q.σₕ - q'.σₕ with he
  have hemem : e ∈ D.S i := (D.S i).sub_mem q.σₕ_mem q'.σₕ_mem
  have hker : IsDiscreteKernel div (D.S i) (D.Uh i) (D.Xh i) e := by
    refine ⟨hemem, fun v hv => ?_, fun η hη => ?_⟩
    · rw [he, map_sub, inner_sub_left, q.eq₂ v hv, q'.eq₂ v hv, sub_self]
    · rw [he, inner_sub_left, q.eq₃ η hη, q'.eq₃ η hη, sub_self]
  have hdive : div e = 0 := div_eq_zero_of_isDiscreteKernel D i hker
  -- the stress components agree by coercivity on the discrete kernel
  have hz : ∀ (r : DiscreteMixedSource div M (D.S i) (D.Uh i) (D.Xh i) f),
      ⟪M.Cinv r.σₕ, e⟫_ℝ = 0 := by
    intro r
    have h1 := r.eq₁ e hemem
    have h2 : ⟪div e, r.uₕ⟫_ℝ = 0 := by rw [hdive, inner_zero_left]
    have h3 : ⟪r.γₕ, e⟫_ℝ = 0 := by
      rw [real_inner_comm]; exact hker.2.2 r.γₕ r.γₕ_mem
    linarith
  have hzero : ⟪M.Cinv e, e⟫_ℝ = 0 := by
    rw [he, map_sub, inner_sub_left, hz q, hz q', sub_zero]
  have hcoer := hyp.coercive e (hyp.kernel_incl i e hker)
  have hσ : q.σₕ = q'.σₕ := by
    have hn : ‖e‖ = 0 := by
      rw [hzero] at hcoer
      have h1 : ‖e‖ ^ 2 ≤ 0 := by
        by_contra hc
        push_neg at hc
        nlinarith [mul_pos hyp.α_pos hc]
      exact sq_eq_zero_iff.mp (le_antisymm h1 (sq_nonneg _))
    have := norm_eq_zero.mp hn
    rw [he] at this
    exact sub_eq_zero.mp this
  -- the remaining components agree by the discrete inf-sup condition
  set w := q.uₕ - q'.uₕ with hw
  set g := q.γₕ - q'.γₕ with hg
  have hwmem : w ∈ D.Uh i := (D.Uh i).sub_mem q.uₕ_mem q'.uₕ_mem
  have hgmem : g ∈ D.Xh i := (D.Xh i).sub_mem q.γₕ_mem q'.γₕ_mem
  have hzero2 : ∀ τ ∈ D.S i, ⟪div τ, w⟫_ℝ + ⟪g, τ⟫_ℝ = 0 := by
    intro τ hτ
    have h1 := q.eq₁ τ hτ
    have h2 := q'.eq₁ τ hτ
    rw [hσ] at h1
    rw [hw, hg, inner_sub_right, inner_sub_left]
    linarith
  obtain ⟨τ, hτS, hτ0, hbound⟩ := hyp.infsup i w hwmem g hgmem
  have hnτ : 0 < hdivNorm div τ :=
    lt_of_lt_of_le (norm_pos_iff.mpr hτ0) (norm_le_hdivNorm div τ)
  have hrhs : ⟪div τ, w⟫_ℝ + ⟪τ, g⟫_ℝ = 0 := by
    rw [real_inner_comm g τ]; exact hzero2 τ hτS
  have hsum : ‖w‖ + ‖g‖ ≤ 0 := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_pos (mul_pos hyp.β_pos hnτ) hc, hbound, hrhs]
  refine ⟨hσ, ?_, ?_⟩
  · have : ‖w‖ = 0 := le_antisymm (by linarith [norm_nonneg g]) (norm_nonneg w)
    have := norm_eq_zero.mp this
    rw [hw] at this
    exact sub_eq_zero.mp this
  · have : ‖g‖ = 0 := le_antisymm (by linarith [norm_nonneg w]) (norm_nonneg g)
    have := norm_eq_zero.mp this
    rw [hg] at this
    exact sub_eq_zero.mp this

/-- Quasi-optimality of **Theorem 3.1** (p. 16, [5, Theorem 3.1]) in best-approximation
form: for every `vₕ ∈ Uₕ` and `ηₕ ∈ Xₕ`,
`‖σ - σₕ‖₀ + ‖u - uₕ‖₀ + ‖γ - γₕ‖₀ ≤ C (dist(σ, Σₕ) + ‖u - vₕ‖₀ + ‖γ - ηₕ‖₀)`,
with `C` independent of the mesh and of the right-hand side `f`. Taking the infimum over
`vₕ` and `ηₕ` gives the form stated in the thesis, see `cea_estimate`. -/
theorem cea_quasi_optimal (D : DiscreteFamily div X S₀ ι) (M : MaterialOperator X μ)
    (hyp : CeaHypotheses D M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (f : U) (p : MixedSource div X S₀ M f)
      (q : DiscreteMixedSource div M (D.S i) (D.Uh i) (D.Xh i) f),
      ∀ vₕ ∈ D.Uh i, ∀ ηₕ ∈ D.Xh i,
        ‖p.σ - q.σₕ‖ + ‖p.u - q.uₕ‖ + ‖p.γ - q.γₕ‖
          ≤ C * (Metric.infDist p.σ (D.S i : Set H) + ‖p.u - vₕ‖ + ‖p.γ - ηₕ‖) := by
  have ha := hyp.α_pos
  have hb := hyp.β_pos
  have hMa := hyp.Ma_nonneg
  have hCf := hyp.Cfort_nonneg
  have hab : 0 < hyp.α * hyp.β := mul_pos ha hb
  obtain ⟨K, hK⟩ : ∃ K, K = hyp.Cfort * (hyp.β + hyp.Ma) * (hyp.α + hyp.Ma)
      + (hyp.β + hyp.Ma) + hyp.α * hyp.β + hyp.α := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨K / (hyp.α * hyp.β) + 1, by positivity, fun i f p q vₕ hv ηₕ hη => ?_⟩
  set Pi := hyp.fort i p.σ with hPi
  set e := q.σₕ - Pi with he
  have hemem : e ∈ D.S i := (D.S i).sub_mem q.σₕ_mem (hyp.fort_mem i p.σ)
  -- the Fortin property, separately in `v` and in `η`
  have hfortv : ∀ v ∈ D.Uh i, ⟪div (p.σ - Pi), v⟫_ℝ = 0 := by
    intro v hv'
    have h := hyp.fortin i p.σ v hv' 0 (Submodule.zero_mem _)
    rw [hPi]
    simpa using h
  have hfortη : ∀ η ∈ D.Xh i, ⟪p.σ - Pi, η⟫_ℝ = 0 := by
    intro η hη'
    have h := hyp.fortin i p.σ 0 (Submodule.zero_mem _) η hη'
    rw [hPi]
    simpa using h
  -- `σₕ - Πσ` lies in the discrete kernel, hence is divergence free
  have hker : IsDiscreteKernel div (D.S i) (D.Uh i) (D.Xh i) e := by
    refine ⟨hemem, fun v hv' => ?_, fun η hη' => ?_⟩
    · have h1 := q.eq₂ v hv'
      have h2 := p.eq₂ v
      have h3 := hfortv v hv'
      rw [map_sub, inner_sub_left] at h3
      rw [he, map_sub, inner_sub_left, h1]
      linarith
    · have h1 := q.eq₃ η hη'
      have h2 := p.eq₃ η (D.Xh_le i hη')
      have h3 := hfortη η hη'
      rw [inner_sub_left] at h3
      rw [he, inner_sub_left, h1]
      linarith
  have hdive : div e = 0 := div_eq_zero_of_isDiscreteKernel D i hker
  have hz1 : ⟪div e, q.uₕ⟫_ℝ = 0 := by rw [hdive, inner_zero_left]
  have hz2 : ⟪div e, p.u⟫_ℝ = 0 := by rw [hdive, inner_zero_left]
  have hz3 : ⟪q.γₕ, e⟫_ℝ = 0 := by rw [real_inner_comm]; exact hker.2.2 q.γₕ q.γₕ_mem
  have hz4 : ⟪ηₕ, e⟫_ℝ = 0 := by rw [real_inner_comm]; exact hker.2.2 ηₕ hη
  have hq1 := q.eq₁ e hemem
  have hp1 := p.eq₁ e (D.S_le i hemem)
  have hA1 : ⟪M.Cinv q.σₕ, e⟫_ℝ = 0 := by rw [hz1, hz3] at hq1; linarith
  have hA2 : ⟪M.Cinv p.σ, e⟫_ℝ = -⟪p.γ, e⟫_ℝ := by rw [hz2] at hp1; linarith
  have hkey : ⟪M.Cinv e, e⟫_ℝ = ⟪p.γ - ηₕ, e⟫_ℝ + ⟪M.Cinv (p.σ - Pi), e⟫_ℝ := by
    have t1 : ⟪M.Cinv e, e⟫_ℝ = ⟪M.Cinv q.σₕ, e⟫_ℝ - ⟪M.Cinv Pi, e⟫_ℝ := by
      rw [he, map_sub, inner_sub_left]
    have t2 : ⟪M.Cinv (p.σ - Pi), e⟫_ℝ = ⟪M.Cinv p.σ, e⟫_ℝ - ⟪M.Cinv Pi, e⟫_ℝ := by
      rw [map_sub, inner_sub_left]
    have t3 : ⟪p.γ - ηₕ, e⟫_ℝ = ⟪p.γ, e⟫_ℝ - ⟪ηₕ, e⟫_ℝ := by rw [inner_sub_left]
    rw [t1, t2, t3, hA1, hA2, hz4]
    ring
  -- coercivity on the discrete kernel bounds `‖σₕ - Πσ‖`
  have hcoer := hyp.coercive e (hyp.kernel_incl i e hker)
  have hb1 : ⟪p.γ - ηₕ, e⟫_ℝ ≤ ‖p.γ - ηₕ‖ * ‖e‖ := real_inner_le_norm _ _
  have hb2 : ⟪M.Cinv (p.σ - Pi), e⟫_ℝ ≤ hyp.Ma * ‖p.σ - Pi‖ * ‖e‖ :=
    le_trans (le_abs_self _) (hyp.a_bound _ _)
  have hnorm : hyp.α * ‖e‖ ≤ ‖p.γ - ηₕ‖ + hyp.Ma * ‖p.σ - Pi‖ := by
    rcases eq_or_lt_of_le (norm_nonneg e) with h0 | h0
    · rw [← h0, mul_zero]
      have := mul_nonneg hMa (norm_nonneg (p.σ - Pi))
      linarith [norm_nonneg (p.γ - ηₕ)]
    · have hsq : hyp.α * ‖e‖ ^ 2 ≤ (‖p.γ - ηₕ‖ + hyp.Ma * ‖p.σ - Pi‖) * ‖e‖ := by
        rw [hkey] at hcoer
        linarith [hb1, hb2]
      have h2 : (hyp.α * ‖e‖) * ‖e‖ ≤ (‖p.γ - ηₕ‖ + hyp.Ma * ‖p.σ - Pi‖) * ‖e‖ := by
        linarith [hsq]
      exact le_of_mul_le_mul_right h2 h0
  have hS : ‖p.σ - Pi‖ ≤ hyp.Cfort * Metric.infDist p.σ (D.S i : Set H) := by
    rw [hPi]; exact hyp.fort_approx i p.σ
  have hAsig : ‖p.σ - q.σₕ‖ ≤ ‖p.σ - Pi‖ + ‖e‖ := by
    have hrw : p.σ - q.σₕ = (p.σ - Pi) - e := by rw [he]; abel
    rw [hrw]; exact norm_sub_le _ _
  -- the discrete inf-sup condition bounds the displacement and the skew part
  obtain ⟨τ, hτS, hτ0, hbound⟩ := hyp.infsup i (q.uₕ - vₕ) ((D.Uh i).sub_mem q.uₕ_mem hv)
    (q.γₕ - ηₕ) ((D.Xh i).sub_mem q.γₕ_mem hη)
  have hq1τ := q.eq₁ τ hτS
  have hp1τ := p.eq₁ τ (D.S_le i hτS)
  have hRHS : ⟪div τ, q.uₕ - vₕ⟫_ℝ + ⟪τ, q.γₕ - ηₕ⟫_ℝ
      = ⟪M.Cinv (p.σ - q.σₕ), τ⟫_ℝ + ⟪div τ, p.u - vₕ⟫_ℝ + ⟪p.γ - ηₕ, τ⟫_ℝ := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    rw [real_inner_comm q.γₕ τ, real_inner_comm ηₕ τ]
    linarith [hq1τ, hp1τ]
  have hτle : ‖τ‖ ≤ hdivNorm div τ := norm_le_hdivNorm div τ
  have hdτle : ‖div τ‖ ≤ hdivNorm div τ := norm_div_le_hdivNorm div τ
  have hnτ : 0 < hdivNorm div τ := lt_of_lt_of_le (norm_pos_iff.mpr hτ0) hτle
  have hinf : hyp.β * (‖q.uₕ - vₕ‖ + ‖q.γₕ - ηₕ‖)
      ≤ hyp.Ma * ‖p.σ - q.σₕ‖ + ‖p.u - vₕ‖ + ‖p.γ - ηₕ‖ := by
    have hcs1 : ⟪M.Cinv (p.σ - q.σₕ), τ⟫_ℝ ≤ hyp.Ma * ‖p.σ - q.σₕ‖ * ‖τ‖ :=
      le_trans (le_abs_self _) (hyp.a_bound _ _)
    have hcs2 : ⟪div τ, p.u - vₕ⟫_ℝ ≤ ‖div τ‖ * ‖p.u - vₕ‖ := real_inner_le_norm _ _
    have hcs3 : ⟪p.γ - ηₕ, τ⟫_ℝ ≤ ‖p.γ - ηₕ‖ * ‖τ‖ := real_inner_le_norm _ _
    have m1 : hyp.Ma * ‖p.σ - q.σₕ‖ * ‖τ‖ ≤ hyp.Ma * ‖p.σ - q.σₕ‖ * hdivNorm div τ :=
      mul_le_mul_of_nonneg_left hτle (mul_nonneg hMa (norm_nonneg _))
    have m2 : ‖div τ‖ * ‖p.u - vₕ‖ ≤ hdivNorm div τ * ‖p.u - vₕ‖ :=
      mul_le_mul_of_nonneg_right hdτle (norm_nonneg _)
    have m3 : ‖p.γ - ηₕ‖ * ‖τ‖ ≤ ‖p.γ - ηₕ‖ * hdivNorm div τ :=
      mul_le_mul_of_nonneg_left hτle (norm_nonneg _)
    have hUp : hyp.β * (‖q.uₕ - vₕ‖ + ‖q.γₕ - ηₕ‖) * hdivNorm div τ
        ≤ (hyp.Ma * ‖p.σ - q.σₕ‖ + ‖p.u - vₕ‖ + ‖p.γ - ηₕ‖) * hdivNorm div τ := by
      linarith [hbound, hRHS, hcs1, hcs2, hcs3, m1, m2, m3]
    exact le_of_mul_le_mul_right hUp hnτ
  have hWtri : ‖p.u - q.uₕ‖ + ‖p.γ - q.γₕ‖
      ≤ (‖p.u - vₕ‖ + ‖p.γ - ηₕ‖) + (‖q.uₕ - vₕ‖ + ‖q.γₕ - ηₕ‖) := by
    have t1 : ‖p.u - q.uₕ‖ ≤ ‖p.u - vₕ‖ + ‖q.uₕ - vₕ‖ := by
      have hrw : p.u - q.uₕ = (p.u - vₕ) - (q.uₕ - vₕ) := by abel
      rw [hrw]; exact norm_sub_le _ _
    have t2 : ‖p.γ - q.γₕ‖ ≤ ‖p.γ - ηₕ‖ + ‖q.γₕ - ηₕ‖ := by
      have hrw : p.γ - q.γₕ = (p.γ - ηₕ) - (q.γₕ - ηₕ) := by abel
      rw [hrw]; exact norm_sub_le _ _
    linarith
  -- assembly, with denominators cleared
  obtain ⟨dσ, hdσ⟩ : ∃ d, d = Metric.infDist p.σ (D.S i : Set H) := ⟨_, rfl⟩
  have hdσ0 : 0 ≤ dσ := by rw [hdσ]; exact Metric.infDist_nonneg
  rw [← hdσ] at hS ⊢
  have hA'' : hyp.α * ‖p.σ - q.σₕ‖ ≤ (hyp.α + hyp.Ma) * (hyp.Cfort * dσ) + ‖p.γ - ηₕ‖ := by
    have h0 := mul_le_mul_of_nonneg_left hAsig ha.le
    have h1 : hyp.α * ‖p.σ - Pi‖ ≤ hyp.α * (hyp.Cfort * dσ) :=
      mul_le_mul_of_nonneg_left hS ha.le
    have h2 : hyp.Ma * ‖p.σ - Pi‖ ≤ hyp.Ma * (hyp.Cfort * dσ) :=
      mul_le_mul_of_nonneg_left hS hMa
    linarith [h0, h1, h2, hnorm]
  have hW' : hyp.β * (‖p.u - q.uₕ‖ + ‖p.γ - q.γₕ‖)
      ≤ hyp.β * (‖p.u - vₕ‖ + ‖p.γ - ηₕ‖)
        + (hyp.Ma * ‖p.σ - q.σₕ‖ + ‖p.u - vₕ‖ + ‖p.γ - ηₕ‖) := by
    have h0 := mul_le_mul_of_nonneg_left hWtri hb.le
    linarith [h0, hinf]
  have hexact : (hyp.α * hyp.β) * (‖p.σ - q.σₕ‖ + ‖p.u - q.uₕ‖ + ‖p.γ - q.γₕ‖)
      ≤ (hyp.Cfort * (hyp.β + hyp.Ma) * (hyp.α + hyp.Ma)) * dσ
        + (hyp.α * hyp.β + hyp.α) * ‖p.u - vₕ‖
        + ((hyp.β + hyp.Ma) + hyp.α * hyp.β + hyp.α) * ‖p.γ - ηₕ‖ := by
    have e1 := mul_le_mul_of_nonneg_left hA'' hb.le
    have e2 := mul_le_mul_of_nonneg_left hW' ha.le
    have e3 := mul_le_mul_of_nonneg_left hA'' hMa
    linarith [e1, e2, e3]
  have hβMa : (0:ℝ) ≤ hyp.β + hyp.Ma := by linarith
  have hαMa : (0:ℝ) ≤ hyp.α + hyp.Ma := by linarith
  have hprod : (0:ℝ) ≤ hyp.Cfort * (hyp.β + hyp.Ma) * (hyp.α + hyp.Ma) :=
    mul_nonneg (mul_nonneg hCf hβMa) hαMa
  have hKb : (hyp.Cfort * (hyp.β + hyp.Ma) * (hyp.α + hyp.Ma)) * dσ
      + (hyp.α * hyp.β + hyp.α) * ‖p.u - vₕ‖
      + ((hyp.β + hyp.Ma) + hyp.α * hyp.β + hyp.α) * ‖p.γ - ηₕ‖
      ≤ K * (dσ + ‖p.u - vₕ‖ + ‖p.γ - ηₕ‖) := by
    have c1 : hyp.Cfort * (hyp.β + hyp.Ma) * (hyp.α + hyp.Ma) ≤ K := by
      rw [hK]; linarith [hab, hβMa]
    have c2 : hyp.α * hyp.β + hyp.α ≤ K := by rw [hK]; linarith [hprod, hβMa]
    have c3 : (hyp.β + hyp.Ma) + hyp.α * hyp.β + hyp.α ≤ K := by rw [hK]; linarith [hprod]
    linarith [mul_nonneg (sub_nonneg.mpr c1) hdσ0,
      mul_nonneg (sub_nonneg.mpr c2) (norm_nonneg (p.u - vₕ)),
      mul_nonneg (sub_nonneg.mpr c3) (norm_nonneg (p.γ - ηₕ))]
  have hsum0 : 0 ≤ dσ + ‖p.u - vₕ‖ + ‖p.γ - ηₕ‖ := by
    linarith [norm_nonneg (p.u - vₕ), norm_nonneg (p.γ - ηₕ)]
  have hfin := le_trans hexact hKb
  calc ‖p.σ - q.σₕ‖ + ‖p.u - q.uₕ‖ + ‖p.γ - q.γₕ‖
      = ((hyp.α * hyp.β) * (‖p.σ - q.σₕ‖ + ‖p.u - q.uₕ‖ + ‖p.γ - q.γₕ‖))
          / (hyp.α * hyp.β) := by field_simp
    _ ≤ (K * (dσ + ‖p.u - vₕ‖ + ‖p.γ - ηₕ‖)) / (hyp.α * hyp.β) := by gcongr
    _ = (K / (hyp.α * hyp.β)) * (dσ + ‖p.u - vₕ‖ + ‖p.γ - ηₕ‖) := by ring
    _ ≤ (K / (hyp.α * hyp.β) + 1) * (dσ + ‖p.u - vₕ‖ + ‖p.γ - ηₕ‖) := by linarith [hsum0]

/-- Existence for the discrete problem (17), p. 16. The three equations define a linear
map from `Σₕ × Uₕ × Xₕ` to its dual. Uniqueness makes this map injective, hence surjective
because the domain and its dual have the same finite dimension. -/
theorem cea_existence (D : DiscreteFamily div X S₀ ι) (M : MaterialOperator X μ)
    (hyp : CeaHypotheses D M) (i : ι) (f : U) :
    Nonempty (DiscreteMixedSource div M (D.S i) (D.Uh i) (D.Xh i) f) := by
  let := D.finite_S i
  let := D.finite_Uh i
  let := D.finite_Xh i
  let P := D.S i × D.Uh i × D.Xh i
  let F : P →ₗ[ℝ] Module.Dual ℝ P :=
    { toFun := fun x =>
        { toFun := fun y =>
            ⟪M.Cinv x.1, y.1⟫_ℝ + ⟪div y.1, x.2.1⟫_ℝ + ⟪(x.2.2 : H), y.1⟫_ℝ
              + ⟪div x.1, y.2.1⟫_ℝ + ⟪(x.1 : H), y.2.2⟫_ℝ
          map_add' := by
            intro y z
            simp [P, Prod.add_def, inner_add_left, inner_add_right]
            ring
          map_smul' := by
            intro r y
            simp [P, Prod.smul_def, inner_smul_right, real_inner_smul_left]
            ring }
      map_add' := by
        intro x z
        apply LinearMap.ext
        intro y
        simp [P, Prod.add_def, inner_add_left, inner_add_right]
        ring
      map_smul' := by
        intro r x
        apply LinearMap.ext
        intro y
        simp [P, Prod.smul_def, inner_smul_right, real_inner_smul_left]
        ring }
  -- Testing the combined equation with one nonzero component recovers (17).
  let solution (g : U) (x : P)
      (hx : ∀ y : P, F x y = -⟪g, (y.2.1 : U)⟫_ℝ) :
      DiscreteMixedSource div M (D.S i) (D.Uh i) (D.Xh i) g :=
    { σₕ := x.1
      uₕ := x.2.1
      γₕ := x.2.2
      σₕ_mem := x.1.property
      uₕ_mem := x.2.1.property
      γₕ_mem := x.2.2.property
      eq₁ := by
        intro τ hτ
        simpa [F] using hx (⟨τ, hτ⟩, 0, 0)
      eq₂ := by
        intro v hv
        simpa [F] using hx (0, ⟨v, hv⟩, 0)
      eq₃ := by
        intro η hη
        simpa [F] using hx (0, 0, ⟨η, hη⟩) }
  have hF : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    let q := solution 0 x (by intro y; simp [hx])
    let q₀ := solution 0 0 (by intro y; simp)
    obtain ⟨hσ, hu, hγ⟩ := cea_unique hyp i 0 q q₀
    exact Prod.ext (Subtype.ext hσ) (Prod.ext (Subtype.ext hu) (Subtype.ext hγ))
  have hsurj : Function.Surjective F :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := P)).symm).mp hF
  let b : Module.Dual ℝ P :=
    { toFun := fun y => -⟪f, (y.2.1 : U)⟫_ℝ
      map_add' := by intro y z; simp [P, Prod.add_def, inner_add_right]; ring
      map_smul' := by intro r y; simp [P, Prod.smul_def, inner_smul_right] }
  obtain ⟨x, hx⟩ := hsurj b
  exact ⟨solution f x (fun y => congrArg (fun l : Module.Dual ℝ P => l y) hx)⟩

/-- **Theorem 3.1** (p. 16, [5, Theorem 3.1]), quasi-optimality in the form stated in the
thesis: `‖σ - σₕ‖₀ + ‖u - uₕ‖₀ + ‖γ - γₕ‖₀ ≤ C (inf ‖σ - τₕ‖₀ + inf ‖u - vₕ‖₀ +
inf ‖γ - ηₕ‖₀)` with `C` independent of the mesh and of the right-hand side `f`.
Uniqueness of the discrete solution is `cea_unique`, existence is `cea_existence`. -/
theorem cea_estimate (D : DiscreteFamily div X S₀ ι) (M : MaterialOperator X μ)
    (hyp : CeaHypotheses D M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (f : U) (p : MixedSource div X S₀ M f)
      (q : DiscreteMixedSource div M (D.S i) (D.Uh i) (D.Xh i) f),
        ‖p.σ - q.σₕ‖ + ‖p.u - q.uₕ‖ + ‖p.γ - q.γₕ‖
          ≤ C * (Metric.infDist p.σ (D.S i : Set H) + Metric.infDist p.u (D.Uh i : Set U)
              + Metric.infDist p.γ (D.Xh i : Set H)) := by
  obtain ⟨C, hC, hbound⟩ := cea_quasi_optimal D M hyp
  refine ⟨C, hC, fun i f p q => ?_⟩
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ε / (2 * C) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hCδ : C * δ = ε / 2 := by rw [hδ]; field_simp
  have hUne : (D.Uh i : Set U).Nonempty := ⟨0, (D.Uh i).zero_mem⟩
  have hXne : (D.Xh i : Set H).Nonempty := ⟨0, (D.Xh i).zero_mem⟩
  obtain ⟨vₕ, hv, hvlt⟩ := (Metric.infDist_lt_iff hUne).mp (lt_add_of_pos_right _ hδ0)
  obtain ⟨ηₕ, hη, hηlt⟩ := (Metric.infDist_lt_iff hXne).mp (lt_add_of_pos_right _ hδ0)
  rw [dist_eq_norm] at hvlt hηlt
  have h1 := hbound i f p q vₕ hv ηₕ hη
  have e1 : C * ‖p.u - vₕ‖ ≤ C * (Metric.infDist p.u (D.Uh i : Set U) + δ) :=
    mul_le_mul_of_nonneg_left hvlt.le hC.le
  have e2 : C * ‖p.γ - ηₕ‖ ≤ C * (Metric.infDist p.γ (D.Xh i : Set H) + δ) :=
    mul_le_mul_of_nonneg_left hηlt.le hC.le
  linarith [h1, e1, e2, hCδ]

/-- The hypotheses of Theorem 3.1 are satisfiable: the trivial model `H = U = ℝ`, `div = id`,
`C = id`, `Sₕ = Uₕ = ℝ`, `Xₕ = ⊥` satisfies them with `Ma = α = 1`, `β = 1/2`, `Cfort = 1`. -/
example (μ : ℝ) : CeaHypotheses trivialFamily (trivialMaterial μ) where
  Ma := 1
  Ma_nonneg := zero_le_one
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
  Cfort_nonneg := zero_le_one
  fort_approx := fun i τ => by
    have := Metric.infDist_nonneg (x := τ) (s := (trivialFamily.S i : Set ℝ))
    simpa using this

end

end MixedElasticEigenvalues
