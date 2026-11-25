::: {.main-results}

**The front theorem** · [Corollary 4.8](#node-corollary-4-8) [machine-checked]{.badge .ok}
:   Under (S) and (A1), the Pareto front is the set of minimal points $(c(X), M(X))$ over the multisets $X$ of $s = 2t - p$ central landings, where $M(X)$ is the least largest load of an admissible partition of $X$. With [Theorem 4.1](#node-theorem-4-1) [machine-checked]{.badge .ok} (achievability, without waiting), [Theorem 4.7](#node-theorem-4-7) [machine-checked]{.badge .ok} (the converse under (A1)) and [Theorem 4.10](#node-theorem-4-10) [machine-checked]{.badge .ok} (the converse under (AΔ)).

**Role configurations bound every non-symmetric plan** · [Theorem 6.1](#node-theorem-6-1) [machine-checked]{.badge .ok}
:   Under (A1-NS), every feasible plan has a role configuration with $t$ passengers, no larger cost, and role loads no larger than the flight times of its planes.

**Schedulable domination** · [Theorem 6.9](#node-theorem-6-9) [machine-checked]{.badge .ok}
:   Under (A1-NS), every feasible plan is matched by a role configuration of no larger cost whose template schedule is no longer, so the search over role configurations finds the non-symmetric front.

**The link-forest DP is exact** · [Theorem 7.5](#node-theorem-7-5) [machine-checked]{.badge .ok}
:   The dynamic program over link forests computes $E(T)$, the least cost of an admissible partition whose loads are all at most $T$.

**The σ-DP is exact** · [Theorem 7.6](#node-theorem-7-6) [machine-checked]{.badge .ok}
:   A shortest path over parity states also computes $E(T)$, without building link forests.

[**The verified solver**](#node-verified-solver) [machine-checked]{.badge .ok}
:   Under (S) and (A1), with $1 \le p \le t$, `solveFront` returns exactly the Pareto front; `lake exe zeno-front` runs it.

**Certificates are sound** · [Theorem 9.1](#node-theorem-9-1) [machine-checked]{.badge .ok}
:   If a certificate's four obligations hold, its points are exactly the Pareto front, and the Lean checker that tests them is proved sound.

[**The non-symmetric checker is sound**](#node-version-2-checker) [machine-checked]{.badge .ok}
:   For non-symmetric instances, a version 2 certificate that `Cert2.check` accepts lists exactly the Pareto front.

:::
