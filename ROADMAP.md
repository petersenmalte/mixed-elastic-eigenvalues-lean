# Roadmap

Numbers refer to the thesis in `thesis/`. The current status of every result is in the
table of `README.md`; this file lists what is still open, in the suggested order.

| Step | Content | Notes |
|---|---|---|
| 1 | Prove `cea_existence` (Theorem 3.1, existence) | Assemble the three equations of (17) into one linear map on `Σₕ × Uₕ × Xₕ` and use `cea_unique` with `LinearMap.injective_iff_surjective`. The only place where finite dimensionality of the discrete spaces is needed. |
| 2 | Connect `Material.lean` with the abstract layer | Frobenius inner product space structure on `Matrix (Fin 2) (Fin 2) ℝ` and a `MaterialOperator` instance built from `matC`/`matCinv`. |
| 3 | Concrete finite elements | Triangulations, `BDMₖ`, Falk's element, Sobolev spaces on domains: the expensive part, currently out of reach of Mathlib. |
