# Roadmap

Numbers refer to the thesis in `thesis/`. The current status of every result is in the
table of `README.md`; this file lists what is still open, in the suggested order.

| Step | Content | Notes |
|---|---|---|
| 1 | Prove `cea_existence` (Theorem 3.1, existence) and then `uniform_convergence` (Theorem 4.7) | Assemble the three equations of (17) into one linear map on `Σₕ × Uₕ × Xₕ` and use `cea_unique` with `LinearMap.injective_iff_surjective`; Theorem 4.7 then follows from `cea_estimate` plus the approximability hypotheses. |
| 2 | Prove `reliability` (Theorem 6.2) and `eigenvalue_reliability` (Theorem 6.4) | The central estimate of Lemma 6.1 is done (`residual_bound`); what remains is applying `stab` to the error triple, replacing `ũₕ` by `u*ₕ` via (67), and Jensen's inequality. The absorption argument of `postprocessed_eigenvalue_rate` can be reused for Theorem 6.4. |
| 3 | Connect `Material.lean` with the abstract layer | Frobenius inner product space structure on `Matrix (Fin 2) (Fin 2) ℝ` and a `MaterialOperator` instance built from `matC`/`matCinv`. |
| 4 | Concrete finite elements | Triangulations, `BDMₖ`, Falk's element, Sobolev spaces on domains: the expensive part, currently out of reach of Mathlib. |
