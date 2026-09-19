# Roadmap

Numbers refer to the thesis in `thesis/`. The current status of every result is in the
table of `README.md`; this file lists what is still open, in the suggested order.

| Step | Content | Notes |
|---|---|---|
| 1 | Prove `eigenvalue_rate` (Theorem 4.10) | Direct from `eigenvalue_identity` and the rate hypotheses; only operator-norm bounds for `C`, `C⁻¹` are needed. |
| 2 | Prove `postprocessed_eigenvalue_rate` (Theorem 5.7) | Direct from `postprocessed_eigenvalue_identity`; needs `u*ₕ ≠ 0` for small `h` and the absorption argument. |
| 3 | Prove `postprocessed_eigenfunction_rate` (Theorem 5.1) | Hilbert space argument; first prove `P*ₕ = Pₕ + P̃ₕ` (51) from the orthogonality relations. |
| 4 | Prove `cea_estimate` (Theorem 3.1) and then `uniform_convergence` (Theorem 4.7) | Brezzi-type estimates with `Metric.infDist`; existence via finite dimensionality. |
| 5 | Prove `reliability` (Theorem 6.2) and `eigenvalue_reliability` (Theorem 6.4) | Lemma 6.1 first. |
| 6 | Connect `Material.lean` with the abstract layer | Frobenius inner product space structure on `Matrix (Fin 2) (Fin 2) ℝ` and a `MaterialOperator` instance built from `matC`/`matCinv`. |
| 7 | Concrete finite elements | Triangulations, `BDMₖ`, Falk's element, Sobolev spaces on domains: the expensive part, currently out of reach of Mathlib. |
