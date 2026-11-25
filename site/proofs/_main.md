::: {.main-results}

**The symmetric front (H1)** · [Theorem 4.5](#node-theorem-4-5) [machine-checked]{.badge .ok}
:   Under (S) and the hub triangles (H), with $p \le t$, the Pareto front is the set of minimal points $(c(X), M(X))$ over the multisets $X$ of $s = 2t - p$ central landings, $M(X)$ the least largest load of an admissible partition of $X$; the same holds for planes ending anywhere. With [Theorem 4.1](#node-theorem-4-1) [machine-checked]{.badge .ok} (achievability) and [Theorem 4.4](#node-theorem-4-4) [machine-checked]{.badge .ok} (the converse under (S) and (H)).

**Schedulable domination** · [Theorem 5.3](#node-theorem-5-3) [machine-checked]{.badge .ok}
:   Under (A1-NS), every feasible plan is weakly dominated by a valid scheduled configuration of no larger cost whose template value, the makespan of its template plan, is at most the plan's.

**The non-symmetric front (H4)** · [Corollary 5.6](#node-corollary-5-6) [machine-checked]{.badge .ok}
:   Under (A1-NS), with $p \le t$, the Pareto front is the set of minimal points $(c(S), M_{\rm tmpl}(S))$ of the valid scheduled configurations with $2t - p$ landings. With [Theorem 5.3](#node-theorem-5-3) [machine-checked]{.badge .ok} (schedulable domination) and [Lemma 5.5](#node-lemma-5-5) [machine-checked]{.badge .ok} (template plans).

**The link-forest DP is exact** · [Theorem 6.7](#node-theorem-6-7) [machine-checked]{.badge .ok}
:   The dynamic program over link forests computes $E(T)$, the least cost of an admissible partition whose loads are all at most $T$.

**The verified solver (H2)** · [Theorem 6.9](#node-theorem-6-9) [machine-checked]{.badge .ok}
:   Under (S) and (H), with $1 \le p \le t$, `solveFront` returns exactly the Pareto front; `lake exe zeno-front` runs it.

**The v1 checker is sound (H3)** · [Theorem 8.2](#node-theorem-8-2) [machine-checked]{.badge .ok}
:   A format v1 certificate that `Cert.check` accepts lists exactly the Pareto front, for every central table satisfying (H), and for every table if all its gaps are `relaxed`.

**The v2 checker is sound (H3)** · [Theorem 8.7](#node-theorem-8-7) [machine-checked]{.badge .ok}
:   For non-symmetric instances, a format v2 certificate that `Cert2.check` accepts lists exactly the Pareto front, for every central table satisfying (A1-NS) when the certificate lists it, and for every table otherwise.

:::
