# Roadmap (preliminary)

Numbers refer to the thesis in `thesis/`. Status: nothing is formalized yet.

| Thesis | Content | Idea for Lean |
|---|---|---|
| Ch. 3, Thm 3.2 | Well-posedness of saddle point problems (Brezzi) | Abstract Hilbert-space statement (inf-sup, coercivity on the kernel); Mathlib has Lax-Milgram only |
| Ch. 4, Def 4.2 – Thm 4.7 | Convergence of discrete eigenvalue problems, weak/strong approximability (Boffi) | Abstract operator-theoretic statements, no finite elements needed |
| Ch. 4, Thm 4.8, 4.10, Lemma 4.11, 4.14 | A priori estimates, estimate for P_h u − u_h | Needs abstract approximation assumptions; concrete Sobolev/FE facts stay as hypotheses at first |
| Ch. 5, Def 5.5, Lemma 5.6 | Postprocessed eigenvalue as Rayleigh quotient, error identity | Good first target: purely algebraic/inner-product-space argument |
| Ch. 5, Thm 5.1 | Local postprocessing, convergence of postprocessed eigenfunction | Depends on polynomial/FE approximation properties |
| Ch. 6, Thm 6.2 – 6.4 | Reliable and efficient a posteriori estimator | Abstract identity first, estimator bounds later |

Concrete finite element spaces (BDM, Falk element), Sobolev spaces on domains and the
interpolation theory are the most expensive parts; the plan is to first formalize the
abstract layer above with these ingredients as explicit hypotheses.
