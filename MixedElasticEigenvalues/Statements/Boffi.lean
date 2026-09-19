import MixedElasticEigenvalues.Statements.Cea

/-!
# Theorem 4.7: uniform convergence of the solution operators (Boffi)

Statement of Theorem 4.7 (p. 28, [3, Theorem 14.6]) in the abstract framework: weak
approximability (Definition 4.4), strong approximability (Definition 4.5) and the Fortid
condition (Definition 4.6) imply uniform convergence of the solution operators
`R, S, T` of the source problem, `‖Rf - Rₕf‖₀ + ‖Sf - Sₕf‖₀ + ‖Tf - Tₕf‖₀ ≤ C(h) ‖f‖₀`
with `C(h) → 0`. The proof is left open (`sorry`).
-/

namespace MixedElasticEigenvalues

open scoped InnerProductSpace
open Filter Topology

noncomputable section

variable {H U : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] {ι : Type*}
  {div : H →ₗ[ℝ] U} {X S₀ : Submodule ℝ H} {μ : ℝ}

/-- Hypotheses of Theorem 4.7 (pp. 27–28):

* `stab`: the uniform discrete stability of Theorem 3.1 (used by the proof in [3]);
* `sol f = (Rf, Sf, Tf)` and `dsol i f = (Rₕf, Sₕf, Tₕf)`: the solution operators of the
  continuous and discrete source problems (p. 26 and (38));
* `regH`, `regU`: the norms of the regularity spaces `Σ⁰, U⁰, X⁰` (p. 27), with the
  regularity estimate `reg`;
* `weak`: weak approximability of `U⁰` w.r.t. `‖·‖_a = (C⁻¹·,·)^{1/2}` (Definition 4.4);
* `strong`: strong approximability of `U⁰` (Definition 4.5);
* `strongX`: strong approximability of `X⁰` — not listed in Theorem 4.7 of the thesis,
  but needed for the third component `‖Tf - Tₕf‖₀` (for Falk's element it holds by the
  argument given on p. 28 for `U⁰`);
* `fortid`: the Fortid condition (Definition 4.6) for the Fortin operator `stab.fort`. -/
structure BoffiHypotheses (D : DiscreteFamily div X S₀ ι) (M : MaterialOperator X μ) where
  stab : CeaHypotheses D M
  sol : ∀ f : U, MixedSource div X S₀ M f
  dsol : ∀ (i : ι) (f : U), DiscreteMixedSource div M (D.S i) (D.Uh i) (D.Xh i) f
  regH : H → ℝ
  regU : U → ℝ
  Creg : ℝ
  reg : ∀ f, regH (sol f).σ + regU (sol f).u + regH (sol f).γ ≤ Creg * ‖f‖
  CW : ι → ℝ
  CW_tendsto : Tendsto CW D.l (𝓝 0)
  weak : ∀ i τ, IsDiscreteKernel div (D.S i) (D.Uh i) (D.Xh i) τ → ∀ f,
    ⟪div τ, (sol f).u⟫_ℝ ≤ CW i * Real.sqrt ⟪M.Cinv τ, τ⟫_ℝ * regU (sol f).u
  CS : ι → ℝ
  CS_tendsto : Tendsto CS D.l (𝓝 0)
  strong : ∀ i f, ∃ vₕ ∈ D.Uh i, ‖(sol f).u - vₕ‖ ≤ CS i * regU (sol f).u
  strongX : ∀ i f, ∃ ηₕ ∈ D.Xh i, ‖(sol f).γ - ηₕ‖ ≤ CS i * regH (sol f).γ
  CF : ι → ℝ
  CF_tendsto : Tendsto CF D.l (𝓝 0)
  fortid : ∀ i f, ‖(sol f).σ - stab.fort i (sol f).σ‖ ≤ CF i * regH (sol f).σ

/-- **Theorem 4.7** (p. 28, [3, Theorem 14.6]). If the weak approximability of `U⁰` w.r.t.
`(·,·)_a`, the strong approximability of `U⁰` and the Fortid condition are satisfied, then
there is a constant `C(h)` with `C(h) → 0` as `h → 0` such that
`‖Rf - Rₕf‖₀ + ‖Sf - Sₕf‖₀ + ‖Tf - Tₕf‖₀ ≤ C(h) ‖f‖₀` for every `f`. -/
theorem uniform_convergence (D : DiscreteFamily div X S₀ ι) (M : MaterialOperator X μ)
    (hyp : BoffiHypotheses D M) :
    ∃ C : ι → ℝ, Tendsto C D.l (𝓝 0) ∧ ∀ (i : ι) (f : U),
      ‖(hyp.sol f).σ - (hyp.dsol i f).σₕ‖ + ‖(hyp.sol f).u - (hyp.dsol i f).uₕ‖
        + ‖(hyp.sol f).γ - (hyp.dsol i f).γₕ‖ ≤ C i * ‖f‖ := by
  -- Not proved here. With the quasi-optimality argument of Theorem 3.1 (`cea_estimate`,
  -- itself open), `‖Rf - Rₕf‖ + ‖Sf - Sₕf‖ + ‖Tf - Tₕf‖` is bounded by a constant times
  -- `‖σ - fort σ‖ + inf ‖u - vₕ‖ + inf ‖γ - ηₕ‖`, which by `fortid`, `strong`, `strongX`
  -- and `reg` is at most `C₀ (CF i + CS i) ‖f‖`; hence `C i := C₀ (CF i + CS i) → 0`.
  sorry

/-- The hypotheses of Theorem 4.7 are satisfiable in the trivial model (all constants
`C(h)` equal to zero, since the discrete solutions coincide with the continuous ones). -/
example (μ : ℝ) (stab : CeaHypotheses trivialFamily (trivialMaterial μ))
    (hfort : ∀ i τ, stab.fort i τ = τ) : BoffiHypotheses trivialFamily (trivialMaterial μ) where
  stab := stab
  sol := trivialSource μ
  dsol := fun n f => trivialDiscreteSource μ f n
  regH := fun x => ‖x‖
  regU := fun x => ‖x‖
  Creg := 2
  reg := fun f => by simp [trivialSource]; linarith [norm_nonneg f]
  CW := fun _ => 0
  CW_tendsto := tendsto_const_nhds
  weak := fun i τ hτ f => by
    have h0 : τ = 0 := by
      have := hτ.2.1 τ Submodule.mem_top
      simpa [inner_self_eq_zero] using this
    simp [h0]
  CS := fun _ => 0
  CS_tendsto := tendsto_const_nhds
  strong := fun i f => ⟨(trivialSource μ f).u, Submodule.mem_top, by simp⟩
  strongX := fun i f => ⟨0, Submodule.zero_mem _, by simp [trivialSource]⟩
  CF := fun _ => 0
  CF_tendsto := tendsto_const_nhds
  fortid := fun i f => by simp [hfort]

end

end MixedElasticEigenvalues
