# Roadmap

Numbers refer to the thesis in `thesis/`. The current status of every result is in the
table of `README.md`; this file lists what is still open, in the suggested order.

The discrete existence theorem (`cea_existence`) and the eigenvalue reliability theorem
(`eigenvalue_reliability`) are proved. All current mathematical modules undergo strict
axiom checks, and unfinished proofs are rejected throughout the project.

| Step | Content | Notes |
|---|---|---|
| 1 | Connect `Material.lean` with the abstract layer | Frobenius inner product space structure on the `2×2` matrices and a `MaterialOperator` built from `matC`/`matCinv`. |
| 2 | Connect the abstract results | Construct discrete solution data using `cea_existence`; derive the input rates of Theorem 5.7 from Theorem 5.1 and the remaining rate hypotheses. Require a nontrivial refinement filter (`NeBot`) in `DiscreteFamily`. |
| 3 | Construct postprocessing and solution operators | Prove existence and uniqueness of the postprocessing; develop the continuous source problem rather than supplying its solutions as data. |
| 4 | Derive eigenfunction and superconvergence rates | Supply the spectral approximation argument and the content of Theorem 4.8 and Lemmas 4.11 and 4.14 that currently enter as hypotheses. |
| 5 | Control the a posteriori remainder | Formalize Theorem 6.3 and prove the relevant higher-order or absorption estimates for `hot`; the present reliability bounds still contain exact-solution errors. |
| 6 | Concrete finite elements and analysis | Construct triangulations, `BDMₖ`, Falk's element and Sobolev spaces on domains, and prove the stability, regularity and interpolation hypotheses for them. This is the largest remaining part. |
