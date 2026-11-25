::: {.main-results}

**The front theorem** · [Corollary 4.8](#node-corollary-4-8) [machine-checked]{.badge .ok}
:   Under (S) and (A1), the Pareto front is the set of minimal points $(c(X), M(X))$ over the multisets $X$ of $s = 2t - p$ central landings, where $M(X)$ is the least largest load of an admissible partition of $X$. With [Theorem 4.1](#node-theorem-4-1) [parts in Lean]{.badge .informal} (achievability; Lean builds the plan with its cost and makespan, the part the front theorem uses), [Theorem 4.7](#node-theorem-4-7) [machine-checked]{.badge .ok} (the converse under (A1)) and [Theorem 4.10](#node-theorem-4-10) [machine-checked]{.badge .ok} (the converse under (AΔ)).

**Role configurations bound every non-symmetric plan** · [Theorem 6.1](#node-theorem-6-1) [parts in Lean]{.badge .informal}
:   Under (A1-NS), every feasible plan has a role configuration with $t$ passengers, no larger cost and every role load at most the plan's makespan: the form Lean proves, and the one the checker uses.

**Schedulable domination** · [Theorem 6.9](#node-theorem-6-9) [parts in Lean]{.badge .informal}
:   Under (A1-NS), every feasible plan is matched by a role configuration of no larger cost with orders and a link matching whose template has makespan at most the plan's. Lean proves the bound on the template's closed form; that the closed form is the template's makespan is Lemma 6.3, written only.

**The link-forest DP is exact** · [Theorem 7.5](#node-theorem-7-5) [parts in Lean]{.badge .informal}
:   The dynamic program over link forests computes $E(T)$, the least cost of an admissible partition whose loads are all at most $T$. Lean proves this equality, not the DP's time and memory bounds.

**The σ-DP is exact** · [Theorem 7.6](#node-theorem-7-6) [parts in Lean]{.badge .informal}
:   A shortest path over parity states also computes $E(T)$. Lean proves it for the σ-DP on the non-dominated cities, the form the solver runs.

[**The verified solver**](#node-verified-solver) [machine-checked]{.badge .ok}
:   Under (S) and (A1), with $1 \le p \le t$, `solveFront` returns exactly the Pareto front; `lake exe zeno-front` runs it.

**Certificates are sound** · [Theorem 9.1](#node-theorem-9-1) [parts in Lean]{.badge .informal}
:   If a certificate's four obligations hold, its points are exactly the Pareto front. Lean proves it for the gap bounds its own checker supports, so a certificate that the Lean checker accepts lists exactly the front.

[**The non-symmetric checker is sound**](#node-version-2-checker) [machine-checked]{.badge .ok}
:   For non-symmetric instances, a version 2 certificate that `Cert2.check` accepts lists exactly the Pareto front, under (A1-NS) when it uses a gap kind other than `relaxed`.

:::
