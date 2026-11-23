# Exact Pareto fronts for MultiZenoTravel: proofs, algorithm, complexity

This note closes the gaps found in the optimality arguments of Quemy & Schoenauer (EvoCOP 2015) and of
Quemy, Schoenauer & Dréo (arXiv:2304.14659, 2023). It gives a written proof of every statement that the
exact solver and its certificates rely on, in a form meant to feed a Lean blueprint. A statement without a
complete proof is marked sketch (S) or open (O), with what is missing. The note also specifies the exact
algorithm, analyses its complexity and lists the computational evidence.

The only goal is the exact Pareto front: weak dominance is enough throughout, and one plan per front point
is sufficient.

*Numbering.* This revision renumbers the results of the first version: Theorem 4.3 is now 4.7, Lemma 4.4 is
4.6, Corollary 4.5 is 4.8, Conjecture 4.6 is 4.10, Conjecture 6.2 is 6.5 and Conjecture 6.4 is 6.7.

## 0. Status

P: complete written proof in this note. S: argument given, not complete. O: open. Evidence is in §11.

**By setting.**

| | (S) and (A1) | (S) only | Non-symmetric |
|---|---|---|---|
| Lower bound valid for every plan | $E$ (Thm 4.7) and $L$ | $L$ (Lemma 3.4) | role loads under (A1-NS) (Thm 6.1); relaxed roles under (AΔ) (Lemma 6.2) |
| Front characterised by admissible partitions | P (Cor 4.8) | O (Conj 4.10) | false by role loads (Prop 6.5); O (Conj 6.7) |
| Front computed exactly | P, pseudo-polynomial (§7) | wherever $L$ meets $E$ (§9) | wherever a plan meets the bound (§6.5) |
| Ends of the front in closed form | P (Prop 7.10) | P (Prop 7.10) | — |
| Linear family (default generator) | P, closed form (Thm 10.1) | P, same front | — |
| Per-PPP greedy of both papers is optimal | false (§5) | false | false |

Every PDDL problem the generator writes is symmetric and satisfies (A1) (§1.3), so the first column covers
every emitted benchmark.

**By statement.** Names in brackets are those used in the design reviews.

| # | Statement | Hypotheses | Status | Uses |
|---|---|---|---|---|
| 1.1 | A finite dominating subset has the same front | — | P | — |
| 1.2 | PDDL plans of the domain file correspond to plans of §1.2, makespan in the limit ε → 0 | — | S | — |
| 2.1 | $\#A - \#\bar A = 1$ per plane | — | P | — |
| 2.2 | Admissibility defined by a parity matrix [Claim A] | definition | — | — |
| 2.3 | Integer form of admissibility [A′] | — | P | 2.2 |
| 2.4 | Component form; a parity matrix inside any spanning forest | — | P | 2.2 |
| 2.5 | $h_k \le \lvert X_k\rvert - 1$ for every parity matrix | — | P | 2.2 |
| 2.6 | Admissible iff a link forest exists [LF] | — | P | 2.3, 2.4 |
| 2.7 | At most $t-p$ links; trees of at most $q_{\max} = \min(p, t-p+1)$ planes | $\lvert X\rvert = s$ | P | 2.6 |
| 2.8 | Some parity matrix touches at most $\min(p-1, t-p)$ cities [B′] | $\lvert X\rvert = s$ | P | 2.5 |
| 2.9 | A city shared by all even groups makes a partition admissible | — | P | 2.4 |
| 3.1 | Cleaning, in event order | — | P | — |
| 3.2 | At least $s = 2t-p$ segments and central landings [counting] | — | P | — |
| 3.3 | Segment durations | (S) or (AΔ) | P | — |
| 3.4 | Every plan $(C, M)$ has $C \ge L(\lfloor M/2\rfloor)$ [R] | (S) | P | 3.2, 3.3 |
| 4.1 | Admissible partition gives a plan of makespan $\max_k \ell(X_k)$ [achievability] | (S) | P | 2.6 |
| 4.3 | Direct selection: plan to role configuration [DS] | simple, clean plan | P | 2.1, 3.1, 3.3 |
| 4.4 | Shrinking a role configuration [SH] | — | P | — |
| 4.5 | Role configuration to admissible partition [PAR] | — | P | 2.2 |
| 4.6 | Adding a plane [AP] (corrects former Lemma 4.4) | — | P | 2.5 |
| 4.7 | Converse: every plan is dominated by an admissible partition | (S), (A1) | P | 3.1, 4.3–4.5 |
| 4.8 | Front characterisation | (S), (A1) | P | 1.1, 4.1, 4.7 |
| 4.9 | Planes ending anywhere give the same front [B3] | (S), (A1) | P | 1.1, 3.1, 4.1, 4.3–4.8 |
| 4.10 | Converse without (A1) | (S), (AΔ) | O | — |
| 6.1 | Converse to role configurations [N1] | (A1-NS) | P | 3.1, 4.3, 4.4 |
| 6.2 | Relaxed role-load lower bound | (AΔ) | P | 2.1, 3.3, 4.4 |
| 6.3 | Template schedule and closed-form makespan [N3] | — | P | 3.3 |
| 6.4 | One pick-up (or one drop-off) per plane never waits harmfully [W1] | (AΔ-path) | P | 6.3 |
| 6.5 | No harmful waiting in general — **false**: counterexample, front checked by the exhaustive oracle (Prop 6.5) | (AΔ-path) | refuted | 6.1, 6.3 |
| 6.6 | Imbalance-vector DP for the role-load bound [N5] | — | P | 7.2 |
| 6.7 | Shuttle triples complete the front | (AΔ) | O | — |
| 7.1 | Front = breakpoints of $E$ | (S), (A1) | P | 4.8 |
| 7.2 | One-plane table $G$ | — | P | — |
| 7.3 | $L \le E \le U_3 \le U$ | — | P | 2.6, 7.2 |
| 7.4 | $U = E$ if $q_{\max} \le 2$; $U_3 = E$ if $q_{\max} \le 3$ | — | P | 2.6, 2.7, 7.3 |
| 7.5 | Link-forest DP computes $E(T)$; complexity | — | P | 2.6, 2.7, 7.2 |
| 7.6 | σ-DP computes $E(T)$ [Claim C] | — | P | 2.2, 2.8, 7.2 |
| 7.7, 7.8 | Pareto-set variant [PS] | — | P | 1.1, 7.6 |
| 7.9 | Dominated cities can be removed [DOM] | — ; fronts: (S), (A1) | P | 2.2, 7.1 |
| 7.10 | Closed-form ends of the front [END] | (S) | P | 2.9, 3.2, 3.4, 4.1 |
| 8.1 | Deciding $M(X) \le 2T$ is strongly NP-complete | $p$ in the input | P | 2.4 |
| 8.2 | NP-complete for $p = 2$; pseudo-polynomial for fixed $p$ | — | P | 2.2, 2.4 |
| 8.3 | $E(T)$ and the front in pseudo-polynomial time | — | P | 7.5 |
| 9.1 | Certificate obligations 1–4 imply the front [X3] | — | P | 1.1 |
| 9.2, 9.3 | Potentials and default potentials for the σ-DP [X2] | — | P | 7.6 |
| 10.1 | Linear family: closed-form front, exact under (S) alone | (S) | P | 1.1, 2.9, 3.4, 4.1, 7.2, 7.10 |
| 10.2 | The papers' greedy is exact on the linear family | (S), (A1) | O | — |
| §5 | Greedy counterexamples | (S), (A1) | P (computed) | 4.8 |
| App. A | Normal-form proof N1–N6 of 4.7 (superseded) | (S), (A1) | P | 4.6 |

## 1. Model

### 1.1 Instances

* Cities: $C_I$ (initial) and $C_G$ (goal), the *hubs*, and central cities $1,\dots,n$.
* Flights are undirected: an existing flight joins two distinct cities and has one duration, used in both
  directions. $C_I$–$i$ lasts $d_i \ge 0$, $i$–$C_G$ lasts $\bar d_i \ge 0$, and a central flight $i$–$j$
  ($i \ne j$), if it exists, lasts $d_{ij} = d_{ji} \ge 0$. There is no flight $C_I$–$C_G$.
  $\mathrm{dur}(a,b)$ denotes the duration of the flight $a$–$b$.
* Landing in central city $i$ costs $c_i \ge 0$; landing in a hub is free.
* $p \ge 1$ planes and $t \ge p$ passengers start in $C_I$ at time 0. A plane carries at most one passenger.
* Durations and times lie in an archimedean ordered field $\mathbb K$ ($\mathbb Q$ or $\mathbb R$), so that
  $\lfloor\cdot\rfloor$ is defined. From §7 on, durations are integers.

### 1.2 Plans

**Definition (plan).** A plan on a finite set $Q$ of planes (all $p$ planes unless stated otherwise)
consists of

1. for every plane $k \in Q$, a *route*: a finite sequence of *legs* $(k,1),\dots,(k,\nu_k)$, where leg
   $(k,j)$ uses an existing flight joining $v_{k,j-1}$ and $v_{k,j}$, flown from $v_{k,j-1}$ to $v_{k,j}$,
   and departs at time $e_{k,j}$, with $v_{k,0} = C_I$, $e_{k,1} \ge 0$ and
   $e_{k,j+1} \ge a_{k,j} := e_{k,j} + \mathrm{dur}(v_{k,j-1}, v_{k,j})$;
2. for every passenger $\pi$, a *journey*: a non-empty sequence of legs whose first leg departs from $C_I$,
   whose last leg arrives in $C_G$, and in which each leg departs from the city where the previous one
   arrives, no earlier than that arrival, and, if both are legs of the same plane, at a later position of
   its route;
3. *capacity*: the journeys are pairwise disjoint, and none repeats a leg.

Below, "flight" also means a leg when no confusion is possible. The plan is *feasible* if every route ends in
$C_G$ ($\nu_k \ge 1$ and $v_{k,\nu_k} = C_G$). Its *cost*
$C = \sum_{k,j} c(v_{k,j})$ sums the landing costs of all flights (hubs are free). Its *makespan*
$M = \max_k a_{k,\nu_k}$ is the time at which the last plane reaches $C_G$ for the last time. $\mathcal A$
is the set of pairs $(C, M)$ of feasible plans.

Waiting is implicit: a departure may be later than the preceding arrival, for planes and for passengers.
Boarding and debarking are instantaneous: a passenger changing planes debarks when its flight arrives and
boards when the next one departs, and the only constraint is the time inequality of item 2. Several planes
may be in a city at once.

*Event order.* "First" and "last" refer to positions in a journey or in a route. With zero durations
several events can share a time; the sequences fix their order, and every argument below reads them this
way.

The *flight time* of plane $k$ is $F_k = \sum_j \mathrm{dur}(f_{k,j})$. Its flights are sequential, so
$F_k \le a_{k,\nu_k} \le M$.

*Planes ending anywhere.* In the variant of Theorem 4.9, every plan counts (routes need not end in $C_G$ and
may be empty), journeys still end in $C_G$, and the makespan $M'$ is the largest arrival time over all legs;
there is at least one leg since $t \ge 1$. $\mathcal A'$ is the set of pairs $(C, M')$ of all plans.

### 1.3 PDDL semantics

The domain file `pddl/multi-zeno-travel.pddl` (PDDL 2.1, level 3) has

* a durative action `fly` lasting `(timeTerre ?from ?to)`, whose only condition is that the plane is at
  `?from` at the start, and which adds `(citythreat ?to)` to `total-cost` at its end;
* instantaneous actions `board` and `debark`, and the predicate `libre` enforcing capacity one;
* goals putting every person and every plane in $C_G$, and the metric minimising `total-time` and
  `total-cost`.

`generatePDDL` (`src/utils.cpp`) writes `timeTerre` for both orders of each pair. It gives the $C_I$ and
$C_G$ legs of city $i$ the same duration $d_i$, and a central flight the duration $d_i + d_j + 100$. Emitted
problems are therefore symmetric and satisfy (A1). A non-symmetric run of the solver still emits a
symmetric file. Problem files written before plane goals were added (PR #9) have the semantics of planes
ending anywhere; Theorem 4.9 shows that their front is the same.

**Statement 1.2 (PDDL correspondence, S).** A plan of the domain under ε-separation yields a plan of §1.2
with the same cost and a makespan at most its `total-time`: each plane's `fly` actions in time order form
its route, each person's flights between `board` and `debark` form its journey, and `libre` gives capacity
one. Conversely, a plan of §1.2 with makespan $M$ yields PDDL plans with `total-time` at most $M + K\varepsilon$,
where $K$ bounds the length of a chain of dependent actions: delay each action by ε per predecessor. So the
model's makespan is the PDDL makespan in the limit ε → 0, which is what ZenoSolver reports. This is argued
here, not formalised.

### 1.4 Assumptions

Used only where stated.

* (S) symmetry: $d_i = \bar d_i$ for all $i$.
* (A1) central flights are useless: under (S), $d_{ij} \ge d_i + d_j$ for every existing central flight.
  This is the EvoCOP 2015 assumption (stated there with $>$).
* (A1-NS) $d_{ij} \ge \min(d_i + d_j,\ \bar d_i + \bar d_j)$ for every existing central flight.
* (AΔ) triangle inequality for the flights that exist: $\mathrm{dur}(a,b) \le \mathrm{dur}(a,x) + \mathrm{dur}(x,b)$
  whenever the three flights exist.
* (AΔ-path) for all central $i$ and $z$: $\bar d_i \le d_i + d_z + \bar d_z$ and
  $d_i \le \bar d_i + \bar d_z + d_z$. A hub leg of $i$ is no longer than the detour through $z$ and the
  other hub. (S) implies it, and (AΔ) implies it when the central flight $i$–$z$ exists.

### 1.5 Fronts

For points $y, z \in \mathbb K^2$ (cost, makespan), $y \preceq z$, *$y$ weakly dominates $z$*, if
$y \le z$ componentwise. For $\mathcal S \subseteq \mathbb K^2$, $\mathrm{Min}\,\mathcal S$ is the set of
$z \in \mathcal S$ such that no $y \in \mathcal S$ other than $z$ has $y \preceq z$. The *front* is
$\mathcal F = \mathrm{Min}\,\mathcal A$.

**Lemma 1.1 (dominating subset).** Let $\mathcal S' \subseteq \mathcal S \subseteq \mathbb K^2$ with
$\mathcal S'$ finite and every point of $\mathcal S$ weakly dominated by a point of $\mathcal S'$. Then
$\mathrm{Min}\,\mathcal S = \mathrm{Min}\,\mathcal S'$, and every point of $\mathcal S$ is weakly dominated
by a point of $\mathrm{Min}\,\mathcal S$.

*Proof.* Let $z \in \mathrm{Min}\,\mathcal S$. Some $y \in \mathcal S'$ has $y \preceq z$, so $y = z$, and
$z$ is minimal in $\mathcal S' \subseteq \mathcal S$. Let $z \in \mathrm{Min}\,\mathcal S'$ and $y \in \mathcal S$
with $y \preceq z$. Some $y' \in \mathcal S'$ has $y' \preceq y \preceq z$, so $y' = z$ and then $y = z$.
Finally, for $z \in \mathcal S$, take $y \in \mathcal S'$ with $y \preceq z$ and a $\preceq$-minimal element
of the finite set $\{y' \in \mathcal S' : y' \preceq y\}$; it lies in $\mathrm{Min}\,\mathcal S' = \mathrm{Min}\,\mathcal S$. $\square$

**Notation.** $s = 2t - p$, so $s \ge p$ and $s \equiv p \pmod 2$; $\kappa = \lceil s/p\rceil$;
$d_{\max} = \max_i d_i$. For multisets of central cities: $Y(i)$ is the multiplicity of $i$, $|Y|$ the size,
$\mathrm{supp}\,Y$ the support, $Y + Z$ the sum, $Z \le Y$ inclusion and $Y - Z$ the difference for
$Z \le Y$; $c(Y) = \sum_{w\in Y} c_w$, $\delta(Y) = \sum_{w\in Y} d_w$, $\bar\delta(Y) = \sum_{w\in Y} \bar d_w$,
and under (S) the *load* $\ell(Y) = 2\delta(Y)$. A *partition* of $X$ over a finite set $Q$ of planes is a
family $(X_k)_{k \in Q}$ (one group per plane, possibly empty) with $\sum_{k\in Q} X_k = X$. Unless stated
otherwise $Q$ is the set of all $p$ planes, written $X_1,\dots,X_p$; definitions and results of §2 hold for
any $Q$, with $p$ replaced by $|Q|$.

## 2. Segments, admissible partitions, link forests

**Segments.** Let a route $v_0 = C_I, v_1, \dots, v_\nu$ end in a hub, and let
$0 = j_0 < j_1 < \dots < j_r = \nu$ be the positions where it is in a hub. The $l$-th *segment* is the part
$v_{j_{l-1}}, \dots, v_{j_l}$. No flight joins two hubs, so every segment visits a central city. Types:

* $A$: $C_I \to \dots \to C_G$, &nbsp; $\bar A$: $C_G \to \dots \to C_I$,
* $B$: $C_I \to \dots \to C_I$, &nbsp; $\bar B$: $C_G \to \dots \to C_G$.

A segment is *simple* if it visits exactly one central city; it then consists of two flights. A plane has
as many segments as arrivals in hubs. $F(\gamma)$ is the flight time of segment $\gamma$, and
$F_k = \sum_\gamma F(\gamma)$ over the segments of plane $k$.

**Lemma 2.1.** On every route from $C_I$ to $C_G$, $\#A - \#\bar A = 1$.

*Proof.* Only $A$ and $\bar A$ segments change hub. The route starts in $C_I$ and ends in $C_G$, so the
changes are $A, \bar A, \dots, A$. $\square$

**Definition 2.2 (admissible partition).** Let $X_1,\dots,X_p$ be a partition of $X$. A *parity matrix* for
it is $h \in \{0,1\}^{p\times n}$ such that

* (h1) $h_{k,i} = 1$ implies $X_k(i) \ge 1$;
* (h2) $h_k := \sum_i h_{k,i} \equiv |X_k| + 1 \pmod 2$ for every plane $k$;
* (h3) $\sum_k h_{k,i} \equiv 0 \pmod 2$ for every city $i$.

The partition is *admissible* if it has a parity matrix. Write $\eta_k = \{i : h_{k,i} = 1\}$, so that
$|\eta_k| = h_k$, and $Z(h) = \bigcup_k \eta_k$ for the cities that $h$ *touches*. A plane with $|X_k|$ even
is an *even plane*. An empty group would need $h_k = 0 \equiv 1$ by (h1)–(h2), so admissible partitions have
non-empty groups. Admissibility is decidable by enumerating $h$ on the support of the groups. This
definition replaces the component form of the first version (Lemma 2.4 shows they agree), and is the one to
formalise.

**Lemma 2.3 (integer form) [A′].** A partition is admissible if and only if some
$\tilde h \in \mathbb N^{p\times n}$ has $\tilde h_{k,i} \le X_k(i)$, $\sum_i \tilde h_{k,i} \equiv |X_k| + 1$
for every $k$, and $\sum_k \tilde h_{k,i} \equiv 0$ for every $i$.

*Proof.* A parity matrix is such an $\tilde h$, by (h1). Conversely, $h = \tilde h \bmod 2$ satisfies
(h1)–(h3): $h_{k,i} = 1$ forces $\tilde h_{k,i} \ge 1$, and reduction mod 2 keeps both parity conditions. $\square$

**Lemma 2.4 (component form).** Let $H$ be the bipartite graph on planes and cities with an edge $\{k,i\}$
iff $X_k(i) \ge 1$.

(a) The partition is admissible iff every connected component of $H$ contains an even number of even planes.

(b) If it is admissible, then for every spanning forest $\Theta$ of $H$ it has a parity matrix whose support
$\{(k,i) : h_{k,i} = 1\}$ is a set of edges of $\Theta$.

*Proof.* By (h1), the support $J$ of a parity matrix is a set of edges of $H$. By (h2), $\deg_J(k)$ is odd
exactly at the even planes, and by (h3) $\deg_J(i)$ is even at every city. So parity matrices are the
$\mathcal T$-joins of $H$, for the set $\mathcal T$ of even planes. If $J$ exists, the degrees in a component
$K$ sum to $2|J \cap E(K)|$, so $K$ has an even number of odd-degree vertices, that is, of even planes.
Conversely, assume this parity condition and root every tree of $\Theta$. For a vertex $v$ let
$\epsilon(v) \in \{0,1\}$ be the parity of the number of even planes in the subtree of $v$, and put the edge
from $v$ to its parent in $J$ iff $\epsilon(v) = 1$. Then $\deg_J(v) = \epsilon(v) + \sum_u \epsilon(u)$
over the children $u$ of $v$ (without the first term at a root), and
$\epsilon(v) \equiv [v \in \mathcal T] + \sum_u \epsilon(u)$. So $\deg_J(v) \equiv [v \in \mathcal T]$ at a
non-root. At a root, $\epsilon(v) = 0$ by assumption, so $\deg_J(v) = \sum_u \epsilon(u) \equiv [v \in \mathcal T]$. $\square$

**Lemma 2.5.** For every parity matrix and every plane $k$, $h_k \le |X_k| - 1$.

*Proof.* $h_k \le |\mathrm{supp}\,X_k| \le |X_k|$ by (h1), and $h_k \ne |X_k|$ by (h2). $\square$

**Definition (link forest).** A *link forest* for $X_1,\dots,X_p$ is a forest $\Lambda$ on the planes
(without loops or parallel edges) whose edges carry city labels, such that

* (F1) for every plane $u$ and city $i$, at most $X_u(i)$ edges at $u$ are labelled $i$;
* (F2) $r_u := |X_u| - \deg_\Lambda(u)$ is odd for every plane $u$.

An edge $\{u, v\}$ labelled $i$ is a *link at $i$*. By (F1) the links at $u$ can be given distinct copies of
landings of $X_u$: the multiset of their labels is $\le X_u$. The remaining $r_u \ge 1$ landings are the
*free landings* of $u$.

**Lemma 2.6 (link forest) [LF].** A partition is admissible if and only if it has a link forest. An
admissible partition has a link forest with at most one edge of each label at each plane.

*Proof.* (If.) Let $\tilde h_{u,i}$ be the number of edges at $u$ labelled $i$. Then $\tilde h_{u,i} \le X_u(i)$
by (F1), $\sum_i \tilde h_{u,i} = \deg_\Lambda(u) \equiv |X_u| + 1$ by (F2), and $\sum_u \tilde h_{u,i}$ is
twice the number of edges labelled $i$. Lemma 2.3 applies. This direction holds for any loopless multigraph
(a loop would add 2 to the degree but 1 to $\tilde h_{u,i}$).

(Only if.) Take a spanning forest $\Theta$ of $H$ and a parity matrix with support $J \subseteq E(\Theta)$
(Lemma 2.4(b)). At each city $i$, $\deg_J(i)$ is even. Split the planes $J$-adjacent to $i$ into
$\deg_J(i)/2$ pairs, and for each pair $\{u, v\}$ add to $\Lambda$ an edge $uv$ labelled $i$. Then $u \ne v$,
since $J$ has at most one edge per plane and city. At most one edge at $u$ is labelled $i$, and only if
$(u,i) \in J$, hence $X_u(i) \ge 1$: (F1) holds. $\deg_\Lambda(u) = \deg_J(u) = h_u \equiv |X_u| + 1$: (F2)
holds.

$\Lambda$, built so far as a multigraph, has no cycle, and in particular no parallel edges. Take a cycle: a
closed trail $u_0, u_1, \dots, u_{m-1}, u_0$ with $m \ge 2$ distinct edges $u_{j-1}u_j$ labelled $i_j$
(indices mod $m$), with distinct vertices if $m \ge 3$; $m = 2$ is the case of parallel edges. It gives the
closed walk $u_0, i_1, u_1, i_2, \dots, i_m, u_0$
in $J$, which never uses the same edge twice in a row, even cyclically. At a city $i_j$ it arrives from
$u_{j-1}$ and leaves to $u_j \ne u_{j-1}$. At a plane $u_j$ it arrives from $i_j$ and leaves to $i_{j+1}$;
if $i_j = i_{j+1}$, then $u_j$ would belong to two different pairs at that city (the two distinct edges of
the cycle at $u_j$). But a closed walk of positive length in a forest uses some edge twice in a row: at a
vertex of the walk farthest from the root of its tree, both neighbours on the walk are its parent. $\square$

**Corollary 2.7.** If $|X| = s$, every link forest has at most $t - p$ edges, and each of its trees has at
most $q_{\max} := \min(p,\ t - p + 1)$ planes.

*Proof.* By (F2), $\deg_\Lambda(u) \le |X_u| - 1$. Summing over planes, $2\#E(\Lambda) \le s - p = 2(t-p)$.
A tree with $q$ planes has $q - 1$ edges, so $q - 1 \le t - p$. $\square$

**Lemma 2.8 (few touched cities) [B′].** Let $X_1,\dots,X_p$ be admissible with $|X| = s$.

(a) Every parity matrix touches at most $t - p$ cities.

(b) A parity matrix with the fewest entries equal to 1 has an acyclic support, as a subgraph of $H$, and
touches at most $p - 1$ cities.

(c) So some parity matrix touches at most $w := \min(p-1,\ t-p)$ cities, and it has
$h_k \le \min(|X_k| - 1,\ w)$ for every $k$.

*Proof.* (a) By Lemma 2.5, $\sum_k h_k \le \sum_k (|X_k| - 1) = 2(t-p)$, and by (h3) each touched city
carries at least two of these entries.

(b) Parity matrices form a finite non-empty set, so one with the fewest entries exists; let $J$ be its
support. $H$ is a simple bipartite graph, so each vertex of a cycle of $H$ meets exactly two of its edges. If
$J$ contained a cycle, setting $h$ to 0 on it would lower the degree of each of its vertices by 2 and keep
(h1)–(h3), with fewer entries. So $J$ is a forest. Let $P'$ and $Z$ be the planes and the cities incident to
$J$. If $Z = \emptyset$ the bound is $0 \le p - 1$. Otherwise every city of $Z$ has $J$-degree at least 2,
so $2|Z| \le |J| \le |P'| + |Z| - 1$, and $|Z| \le |P'| - 1 \le p - 1$.

(c) Apply (a) to the matrix of (b). Then $h_k \le |X_k| - 1$ by Lemma 2.5, and $\eta_k \subseteq Z(h)$. $\square$

**Lemma 2.9 (shared city).** Let $X_1,\dots,X_p$ be non-empty groups with $\sum_k |X_k| \equiv p \pmod 2$.
If some city belongs to every even group, the partition is admissible. This holds in particular when all
groups contain a common city, and when all even groups are equal.

*Proof.* With $n_{\rm ev}$ even planes, $\sum_k |X_k| \equiv p - n_{\rm ev}$, so $n_{\rm ev}$ is even. All
even planes lie in the component of $H$ containing the shared city, and the other components contain none.
Lemma 2.4(a) applies. $\square$

## 3. Lemmas valid in every setting

**Lemma 3.1 (cleaning).** Every plan can be changed, keeping all routes (hence cost, makespan and flight
times), so that every journey is *clean*: its first flight is its only flight departing from $C_I$, and its
last flight is its only flight arriving in $C_G$. A clean journey has no flight arriving in $C_I$ and none
departing from $C_G$.

*Proof.* Replace each journey by its part from its last flight departing from $C_I$ to the first later flight
arriving in $C_G$, which exists since the journey ends in $C_G$. This is a journey, and capacity only gets
looser. In a clean journey, a flight arriving in $C_I$ would be followed by a flight departing from $C_I$
other than the first, since the journey ends in $C_G$. A flight departing from $C_G$ would follow a flight
arriving in $C_G$ other than the last. $\square$

**Lemma 3.2 (counting).** A feasible plan has at least $s = 2t - p$ segments, hence at least $s$ landings in
central cities.

*Proof.* For plane $k$, let $D^I_k$ and $A^I_k$ be its numbers of flights departing from and arriving in
$C_I$, and $D^G_k$, $A^G_k$ the same for $C_G$. The route is in $C_I$ at its start and after each arrival
there, and leaves after each of these visits since it ends in $C_G$: $D^I_k = A^I_k + 1$. It is in $C_G$ only
after arrivals, and leaves after each but the last: $D^G_k = A^G_k - 1$. The first flight of each journey
departs from $C_I$ and the last arrives in $C_G$; by capacity both maps are injective, so
$\sum_k D^I_k \ge t$ and $\sum_k A^G_k \ge t$. Segments end exactly at arrivals in hubs, so plane $k$ has
$A^I_k + A^G_k = D^I_k - 1 + A^G_k$ segments, and the plan at least $t - p + t = s$. Each segment contains a
landing in a central city, and different segments contain different landings. $\square$

No cleaning and no segment types are needed.

**Lemma 3.3 (segment durations).** Let a segment $\gamma$ visit the central cities $x_1,\dots,x_m$ in this
order.

(a) Under (S), $F(\gamma) \ge d_{x_1} + d_{x_m} \ge 2\min(d_{x_1}, d_{x_m})$.

(b) Under (AΔ), for every $j$, $F(\gamma) \ge d_{x_j} + \bar d_{x_j}$ for types $A$ and $\bar A$,
$F(\gamma) \ge 2d_{x_j}$ for $B$ and $F(\gamma) \ge 2\bar d_{x_j}$ for $\bar B$.

(c) A simple segment at $x$ lasts exactly $d_x + \bar d_x$ (types $A$, $\bar A$), $2d_x$ ($B$) or $2\bar d_x$
($\bar B$).

*Proof.* (c) It is two hub flights. (a) The first flight joins a hub to $x_1$ and lasts $d_{x_1}$ under (S);
the last joins $x_m$ to a hub and lasts $d_{x_m}$; for $m = 1$ these are the two flights, and every flight
lasts at least 0. (b) All hub flights exist, so by (AΔ) and induction along the route, the part of $\gamma$
from its first hub to $x_j$ lasts at least the direct flight between them, and likewise from $x_j$ to its
last hub. $\square$

**Lemma 3.4 (relaxation) [R].** Assume (S). For every feasible plan with cost $C$ and makespan $M$ there are
non-empty multisets $Y_1,\dots,Y_p$ with $\sum_k |Y_k| = s$, $c(Y_1 + \dots + Y_p) \le C$, and
$\ell(Y_k) \le F_k \le M$ for every $k$. Hence, with integer durations, $C \ge L(\lfloor M/2\rfloor)$, where
$$L(T) = \min\Big\{c(Y) : Y = Y_1 + \dots + Y_p,\ |Y| = s,\ Y_k \ne \emptyset \text{ and } \delta(Y_k) \le T\ \forall k\Big\}
\quad(\min\emptyset = \infty).$$
No assumption on central flights is needed.

*Proof.* For a segment $\gamma$, let $x^\star(\gamma)$ be whichever of its first and last central cities has
the smaller $d$. By Lemma 3.3(a), $F(\gamma) \ge 2d_{x^\star(\gamma)}$. Every route goes from $C_I$ to $C_G$,
so every plane has a segment, and by Lemma 3.2 the plan has at least $s \ge p$ segments. Choose one segment
per plane and any $s - p$ others, and let $Y_k$ collect $x^\star(\gamma)$ over the chosen segments $\gamma$
of plane $k$. Different segments have different landings, and $x^\star(\gamma)$ is a landing of $\gamma$, so
$c(Y) \le C$. Also $\ell(Y_k) = \sum_\gamma 2d_{x^\star(\gamma)} \le \sum_\gamma F(\gamma) \le F_k \le M$.
With integer durations, $\delta(Y_k)$ is an integer at most $M/2$. $\square$

## 4. Symmetric case

### 4.1 Achievability

**Theorem 4.1.** Assume (S). For every multiset $X$ with $|X| = s$ and every admissible partition
$X_1,\dots,X_p$ of $X$, there is a feasible plan whose central landings are exactly $X$ (so of cost $c(X)$),
in which plane $k$ flies for $\ell(X_k)$ and picks up at most one passenger, and whose makespan is
$\max_k \ell(X_k)$. The plan uses no central flight, so no assumption on them is needed.

*Proof.* Take a link forest $\Lambda$ (Lemma 2.6) and root each of its trees at a plane. For a link at $i$
between a parent $u$ and a child $v$, $u$ will drop a passenger in $i$ (a segment $B$) and $v$ will pick it
up (a segment $\bar B$). A non-root plane has exactly one parent link, so every plane picks up at most once.
Plane $u$ uses one copy of $i$ from $X_u$ per link at $u$ labelled $i$ (F1), and its $r_u$ free landings, an
odd number (F2), for crossings.

*Schedule of plane $k$.* Let $\tau^{\rm dr}_k$ be twice the sum of the durations of its child links (its
drop-offs) and $\tau^{\rm cr}_k$ the load of its free landings.

1. Its drop-offs, one after the other from time 0: $C_I \to i \to C_I$, each carrying a new passenger from
   $C_I$ and leaving it in $i$. These never wait.
2. Its $r_k$ free landings as crossings $A, \bar A, A, \dots, A$; each $A$ carries a new passenger from
   $C_I$ to $C_G$. These never wait.
3. If $k$ has a parent link at $i$: $C_G \to i \to C_G$, leaving $i$ once the passenger dropped there by
   its parent is present, and carrying it to $C_G$.

*Timing.* The drop-off of $u$ at $i$ reaches $i$ at a time at most $\tau^{\rm dr}_u - d_i$. Its child $v$
reaches $C_G$ at $\tau^{\rm dr}_v + \tau^{\rm cr}_v$, arrives in $i$ at $\tau^{\rm dr}_v + \tau^{\rm cr}_v + d_i$,
leaves at the later of this time and the drop-off's arrival, and is back at a time at most
$\max(\tau^{\rm dr}_v + \tau^{\rm cr}_v + 2d_i,\ \tau^{\rm dr}_u) = \max(\ell(X_v), \tau^{\rm dr}_u) \le \max(\ell(X_v), \ell(X_u))$.
A plane without a parent link finishes at $\ell(X_k)$. Every plane flies exactly $\ell(X_k)$, as its segments
are simple (Lemma 3.3(c)), so the makespan is $\max_k \ell(X_k)$.

*Passengers.* Let $\Lambda$ have $N$ links. There are $\sum_k r_k = s - 2N$ crossings, and each plane makes
one more $A$ than $\bar A$, so there are $(s - 2N + p)/2 = t - N$ segments $A$. They and the $N$ drop-offs
carry $t$ distinct passengers out of $C_I$, each delivered to $C_G$ by its $A$ or by the pick-up linked to
its drop-off. Every flight carries at most one passenger, every route ends in $C_G$, and the central landings
are exactly $X$. $\square$

This is the papers' rule ("western parts of P3 early, eastern parts late"), made precise by the link forest:
the forest guarantees at most one pick-up per plane, which is what makes the timing argument work.

### 4.2 Role configurations

**Definition 4.2 (role configuration).** A *role configuration* on a set $Q$ of planes is a family of
multisets of central cities $\mathrm{Dr}_k$ (drop-offs), $\mathrm{Pk}_k$ (pick-ups) and $\mathrm{Cr}_k$
(crossings), $k \in Q$, with $|\mathrm{Cr}_k|$ odd and the *per-city balance*
$\sum_{k\in Q}\mathrm{Dr}_k = \sum_{k\in Q}\mathrm{Pk}_k$. Its *passenger count* is
$t(\mathrm{cfg}) = \sum_k \big(|\mathrm{Dr}_k| + (|\mathrm{Cr}_k| + 1)/2\big)$, its cost is
$\sum_k c(\mathrm{Dr}_k + \mathrm{Pk}_k + \mathrm{Cr}_k)$, and the *role load* of plane $k$ is
$$\lambda_k = 2\delta(\mathrm{Dr}_k) + 2\bar\delta(\mathrm{Pk}_k) + \delta(\mathrm{Cr}_k) + \bar\delta(\mathrm{Cr}_k).$$
With $X_k = \mathrm{Dr}_k + \mathrm{Pk}_k + \mathrm{Cr}_k$, the balance gives
$\sum_k |X_k| = 2t(\mathrm{cfg}) - |Q|$, and under (S), $\lambda_k = \ell(X_k)$.

A plan is *simple* if each of its flights joins a hub and a central city; all its segments are then simple.

**Lemma 4.3 (direct selection) [DS].** (a) In a simple plan with clean journeys, whether or not its routes end
in $C_G$, every journey consists of exactly two flights, $C_I \to x$ and then $x \to C_G$, for a central
city $x$.

(b) Let $P$ be a simple plan on a set $Q$ of planes, every route ending in $C_G$, with clean journeys and
cost $C$. Then there is a role configuration on $Q$ with $t(\mathrm{cfg}) \ge t$, cost at most $C$,
$\lambda_k \le F_k$ for every $k$, and $\mathrm{Dr}_k + \mathrm{Pk}_k + \mathrm{Cr}_k$ a sub-multiset of the
central landings of plane $k$. No assumption on durations is needed.

*Proof.* (a) The first flight of a journey departs from $C_I$, so it goes to a central city $x$. As
$x \ne C_G$, the journey continues with a flight from $x$, which goes to a hub. That hub is not $C_I$
(Lemma 3.1), so the flight arrives in $C_G$, and it is the last flight of the journey (Lemma 3.1).

(b) *Journeys.* By (a), the first flight of a journey is the first flight of a segment of type $A$ or $B$,
written $o(\pi)$, and its second flight is the second flight of a segment at the same city $x$ of type $A$ or
$\bar B$, written $n(\pi)$. A segment has one first flight and one second flight, and by capacity a flight
carries at most one passenger, so $o$ and $n$ are injective. Passenger $\pi$ is a *hand-off* if
$o(\pi) \ne n(\pi)$. A $B$ is never an $n(\cdot)$, and a $\bar B$ never an $o(\cdot)$.

*Counts at a city $x$.* Let $\beta_x$ be the number of $B$ segments at $x$ that are an $o(\cdot)$, and
$\bar\beta_x$ the number of $\bar B$ segments at $x$ that are an $n(\cdot)$. Among the $A$ segments at $x$:
$\theta_x$ are $o(\pi) = n(\pi)$ for some $\pi$ (*through*); $\omega_x$ are $o(\pi)$ and $n(\pi')$ with
$\pi \ne \pi'$ (*swaps*); $\alpha_x$ are an $o(\cdot)$ and no $n(\cdot)$; $\bar\alpha_x$ are an $n(\cdot)$ and
no $o(\cdot)$; the others are *empty*. Every hand-off at $x$ has its $o$ among the $\beta_x + \alpha_x + \omega_x$
segments counted so, and its $n$ among the $\bar\beta_x + \bar\alpha_x + \omega_x$, and each of these segments
serves exactly one hand-off at $x$ in that role. Hence
$$\beta_x - \bar\beta_x = \bar\alpha_x - \alpha_x. \tag{1}$$
Every passenger has exactly one $o$, so
$$t = \textstyle\sum_x (\theta_x + \omega_x + \alpha_x + \beta_x). \tag{2}$$
Let $z_k$ be the number of non-empty $A$ segments of plane $k$. Then
$$\textstyle\sum_k z_k = \sum_x (\theta_x + \omega_x + \alpha_x + \bar\alpha_x). \tag{3}$$

*Selection.* At each city $x$, let $\mu_x = \min(\beta_x, \bar\beta_x)$. Select $\mu_x$ of the $B$ segments at
$x$ that are an $o(\cdot)$, and $\mu_x$ of the $\bar B$ segments at $x$ that are an $n(\cdot)$. For each plane
$k$, let $z'_k = \max(z_k, 1)$, and select its $z_k$ non-empty $A$ segments, $z'_k - 1$ of its $\bar A$
segments and, if $z_k = 0$, one (empty) $A$ segment. These exist: by Lemma 2.1, plane $k$ has at least one
$A$, and $\#\bar A_k = \#A_k - 1 \ge z_k - 1$. Let $\mathrm{Dr}_k$, $\mathrm{Pk}_k$ and $\mathrm{Cr}_k$ be the
cities of the selected $B$, $\bar B$, and $A$ or $\bar A$ segments of $k$. Then $|\mathrm{Cr}_k| = 2z'_k - 1$
is odd, and the balance holds since both sides contain $\mu_x$ copies of $x$.

*Count.* By (2) and (3),
$t(\mathrm{cfg}) = \sum_x \mu_x + \sum_k z'_k \ge \sum_x \mu_x + \sum_k z_k = t + \sum_x (\mu_x - \beta_x + \bar\alpha_x)$.
By (1), $\beta_x - \mu_x = (\beta_x - \bar\beta_x)^+ = (\bar\alpha_x - \alpha_x)^+ \le \bar\alpha_x$. So
$t(\mathrm{cfg}) \ge t$.

*Loads and cost.* The selected segments of $k$ are distinct and simple, and by Lemma 3.3(c) each lasts
exactly its role duration: $2d_x$ for $B$, $2\bar d_x$ for $\bar B$, $d_x + \bar d_x$ for $A$ and $\bar A$.
So $\lambda_k \le F_k$. Each selected segment contributes its single central landing, so
$\mathrm{Dr}_k + \mathrm{Pk}_k + \mathrm{Cr}_k$ is a sub-multiset of the landings of $k$, and the cost is at
most $C$. $\square$

**Lemma 4.4 (shrinking) [SH].** If a role configuration on $Q$ has $t(\mathrm{cfg}) > t \ge |Q|$, deleting
landings gives one on $Q$ with passenger count $t(\mathrm{cfg}) - 1$; its cost, its role loads and its groups
$X_k$ do not increase. Repeating, there is one with passenger count exactly $t$.

*Proof.* If some $|\mathrm{Cr}_k| \ge 3$, delete two of its crossings. Otherwise every $|\mathrm{Cr}_k| = 1$,
so $\sum_k |\mathrm{Dr}_k| = t(\mathrm{cfg}) - |Q| > t - |Q| \ge 0$: some plane $u$ drops off at some city
$x$, and by the balance some plane $v$ picks up at $x$. Delete one copy of $x$ from $\mathrm{Dr}_u$ and one
from $\mathrm{Pk}_v$. Oddness and balance are kept, and the passenger count drops by one. $\square$

**Lemma 4.5 (parity) [PAR].** For a role configuration on $Q$ with passenger count $t$, the groups
$X_k = \mathrm{Dr}_k + \mathrm{Pk}_k + \mathrm{Cr}_k$, $k \in Q$, form an admissible partition (Definition 2.2
with the planes of $Q$) of a multiset of size $2t - |Q|$, with the same cost.

*Proof.* Put $h_{k,i} = (\mathrm{Dr}_k(i) + \mathrm{Pk}_k(i)) \bmod 2$. (h1): $h_{k,i} = 1$ forces
$X_k(i) \ge 1$. (h2): $h_k \equiv |\mathrm{Dr}_k| + |\mathrm{Pk}_k| = |X_k| - |\mathrm{Cr}_k| \equiv |X_k| + 1$.
(h3): $\sum_k h_{k,i} \equiv \sum_k (\mathrm{Dr}_k(i) + \mathrm{Pk}_k(i)) = 2\sum_k \mathrm{Dr}_k(i) \equiv 0$
by the balance. The size is that of Definition 4.2. $\square$

**Lemma 4.6 (adding a plane) [AP].** Let $(X_k)_{k \in Q}$ be admissible with $q = |Q|$,
$\sum_k |X_k| = 2t - q$ and $t \ge q + 1$, and let $\star \notin Q$ be a further plane. Then some admissible
partition $(Y_k)_{k \in Q \cup \{\star\}}$ has $\sum_k |Y_k| = 2t - q - 1$, $c(Y) \le c(X)$ and
$\max_k \delta(Y_k) \le \max_k \delta(X_k)$. This corrects case (b) of the first version's Lemma 4.4, where
the support has $2(t-q)$ entries, not $t - q$.

*Proof.* Fix a parity matrix $h$. By Lemma 2.5, $f_k := |X_k| - h_k$ is odd and at least 1. In $X_k$, call
*free* the $X_k(i) - h_{k,i}$ copies of each city $i$ beyond one copy for each $i \in \eta_k$; there are
$f_k$ of them.

*Case (a): some $f_k \ge 3$.* Let $y, y'$ be two free landings of $X_k$. Set $Y_k = X_k - \{y, y'\}$,
$Y_\star = \{y\}$, keep the other groups, and give plane $\star$ a zero row. (h1) holds as
$Y_k(i) \ge h_{k,i}$ for every $i$. (h2) holds for $k$, since $|Y_k| = |X_k| - 2$, and for $\star$, since
$|Y_\star| = 1$ and $h_\star = 0$. (h3) is unchanged. Also $\delta(Y_\star) = d_y \le \delta(X_k)$ and
$c(Y) = c(X) - c_{y'}$.

*Case (b): every $f_k = 1$.* Then $2t - q = \sum_k (h_k + 1)$, so $\sum_k h_k = 2(t-q) \ge 2$. Some city $i$
has a non-zero column, which is even, so $h_{u,i} = h_{v,i} = 1$ for two planes $u \ne v$. Set
$Y_u = X_u - \{i\}$, $Y_v = X_v - \{i\}$ and $Y_\star = \{i\}$, set $h_{u,i} = h_{v,i} := 0$, and give plane
$\star$ a zero row. (h1) holds for $j \ne i$, as $Y_u(j) = X_u(j)$. (h2) holds for $u$ and $v$, whose group
size and row sum both drop by one, and for $\star$. Column $i$ drops by 2. $|Y_u| = h_u \ge 1$ (old $h_u$),
$\delta(Y_\star) = d_i \le \delta(X_u)$, and $c(Y) = c(X) - c_i$. $\square$

### 4.3 Converse under (A1)

**Theorem 4.7 (converse).** Assume (S) and (A1). For every feasible plan with cost $C$, makespan $M$ and flight
times $F_k$, there is an admissible partition $X_1,\dots,X_p$ of a multiset $X$ with $|X| = s$, $c(X) \le C$
and $\ell(X_k) \le F_k \le M$ for every $k$.

*Proof.* *Step 1: remove central flights.* This step applies to any plan, whether or not its routes end in
$C_G$. Replace a flight $a \to b$ between central cities, departing at $e$, by $a \to C_G$ departing at $e$
followed by $C_G \to b$ departing on arrival. The plane reaches $b$ at $e + d_a + d_b \le e + d_{ab}$ by (S)
and (A1), and waits there until its next departure, which is unchanged. A passenger on board is delivered at
$C_G$: its journey is cut after $a \to C_G$. Central landings are unchanged ($C_G$ is free), and no arrival
time and no $F_k$ increases; in a feasible plan the last flight of a route ends in $C_G$ and is never
replaced, so the makespan is unchanged. After finitely many replacements the plan is simple.

*Step 2.* Clean it (Lemma 3.1).

*Step 3.* Lemma 4.3(b) on all $p$ planes gives a role configuration with passenger count at least $t$, cost at
most $C$ and $\lambda_k \le F_k$. Lemma 4.4 ($t \ge p$) brings the count to $t$. Lemma 4.5 gives an
admissible partition of a multiset of size $2t - p = s$ with $\ell(X_k) = \lambda_k \le F_k \le M$. $\square$

### 4.4 Front characterisation

**Corollary 4.8.** Assume (S) and (A1). Let
$M(X) = \min\{\max_k \ell(X_k) : X_1,\dots,X_p \text{ an admissible partition of } X\}$ ($\infty$ if there is
none). Then
$$\mathcal F = \mathrm{Min}\,\mathcal X, \qquad \mathcal X = \{(c(X), M(X)) : |X| = s,\ M(X) < \infty\},$$
and every point of $\mathcal F$ is attained by a plan with exactly $s$ central landings (Theorem 4.1).

*Proof.* $\mathcal X$ is finite and, by Theorem 4.1, contained in $\mathcal A$. By Theorem 4.7, every point
$(C, M)$ of $\mathcal A$ is weakly dominated by a point of $\mathcal X$, since $c(X) \le C$ and
$M(X) \le \max_k \ell(X_k) \le M$. Lemma 1.1 applies. $\square$

Both papers' Proposition I (Pareto-optimal plans need exactly $2t - p$ landings) holds only in this front
sense. With zero costs, a plan with more landings can be Pareto-optimal. For $n = 1$, $d_1 = 1$, $c_1 = 0$,
$p = 3$ and $t = 5$, the front is $\{(0, 6)\}$, attained with groups of sizes 3, 3 and 1, all odd. The plane
with one landing can add a crossing pair $\bar A, A$ within its slack: the resulting plan has 9 landings and
still attains $(0, 6)$.

### 4.5 Planes ending anywhere (PDDL without plane goals)

**Theorem 4.9 (bridge) [B3].** Assume (S) and (A1). The front $\mathrm{Min}\,\mathcal A'$ of the variant in
which planes may end anywhere and the makespan is the last arrival time (§1.2) equals $\mathcal F$.

*Proof.* A feasible plan is a plan of the variant with the same cost and makespan, since the last arrival of
each route is its latest; so $\mathcal A \subseteq \mathcal A'$. Conversely, take a plan of the variant with
cost $C$ and makespan $M'$. We build an admissible partition of a multiset of size $s$ with cost at most $C$
and loads at most $M'$; its point in $\mathcal X$ (Corollary 4.8) weakly dominates $(C, M')$. So
$\mathcal X \subseteq \mathcal A \subseteq \mathcal A'$ is finite and dominates both sets, and Lemma 1.1 gives
$\mathrm{Min}\,\mathcal A' = \mathrm{Min}\,\mathcal X = \mathcal F$.

1. Apply Step 1 of Theorem 4.7, which applies to any plan. Clean the plan (Lemma 3.1). From every route,
   delete the flights after its last flight that carries a passenger. Cost and arrival times do not
   increase.
2. A route that is not empty now ends with a flight carrying a passenger $\pi$. That flight joins a hub and a
   central city, and it cannot arrive in $C_I$ or depart from $C_G$ (Lemma 3.1). So either it arrives in
   $C_G$, or it is $C_I \to x$, the first flight of $\pi$'s journey, arriving at some time $a$. In the
   second case the journey's second flight is $x \to C_G$ (Lemma 4.3(a)), departing at some
   $e' \ge a$ and arriving at $e' + \bar d_x \le M'$. Append to the route a flight $x \to C_G$ departing at
   $a$ and carrying $\pi$; it arrives at $a + \bar d_x \le M'$, and $\pi$'s old second flight becomes empty.
   Do this for all such routes at once: it only adds flights and empties others, so each inequality
   $e' \ge a$ refers to a flight that is still there.
3. Every route is now empty (an *idle* plane) or ends in $C_G$. Let $Q$ be the set of the $q$ planes that are
   not idle; $q \ge 1$ since $t \ge 1$, and $q \le p \le t$. On $Q$ this is a simple plan with clean
   journeys, every route ending in $C_G$, of cost at most $C$, with $F_k \le M'$. Lemmas 4.3(b), 4.4 and 4.5
   on $Q$ give an admissible partition over $Q$ of a multiset of size $2t - q$, with cost at most $C$ and
   loads at most $M'$.
4. Lemma 4.6, applied once per idle plane (each time with $t \ge q' + 1$ for the current number $q' < p \le t$
   of planes), gives a partition over all $p$ planes of size $s$, without increasing the cost or the largest
   load. $\square$

### 4.6 What remains under (AΔ) only

**Conjecture 4.10.** Theorem 4.7 holds under (S) and (AΔ), without (A1).

Lemmas 4.3–4.5 need only a simple plan, so the conjecture is equivalent to **Step 1 without (A1)**: every
feasible plan is weakly dominated, in (cost, makespan), by a simple feasible plan (if the conjecture holds,
Theorem 4.1 provides one). Splitting $a \to b$ through $C_G$ now costs $d_a + d_b$, which can exceed
$d_{ab}$. A segment can then only pay for one of its landings ($2d_a + 2d_b \le F(\gamma)$ is false in
general), while the hand-offs at $a$ and at $b$ may involve different planes.

This is exactly the "Figure 4" case of the arXiv paper. Its pairing argument has two flaws:

* It concludes "lower cost" from set inclusion ("each city in $\phi_0$ appears in $\phi$"). But moving both
  halves of a pairing to $C^\star = \arg\min(d_i, d_j)$ costs $2c_{C^\star}$, which can exceed $c_i + c_j$.
* It concludes "dominates" from per-pattern durations, which ignores the synchronisation of the new pairs.

**Partial result (one chain).** Consider a passenger handed along segments $\gamma_0, \dots, \gamma_m$ at
cities $x_1, \dots, x_m$. Let $x_{j^\star}$ minimise $d$. Give $\gamma_0$ and $\gamma_m$ the city $x_{j^\star}$,
charged to the two landings at $x_{j^\star}$. For an intermediate $\gamma_j$, keep $x_j$ if $j < j^\star$ and
$x_{j+1}$ otherwise. This is cost-injective, respects every segment's duration, and connects the two ends.

What is missing is doing this simultaneously for all chains when segments are shared between chains. That is
the proof obligation for Conjecture 4.10.

*Without the conjecture.* Under (S) alone, Lemma 3.4 and Theorem 4.1 bracket the least cost $C^\star(M)$ of a
plan with makespan at most $M$: $L(\lfloor M/2\rfloor) \le C^\star(M) \le E(\lfloor M/2\rfloor)$, with $E$
from §7. Where the bracket closes at the levels §9 needs, the front is certified without the conjecture.
It closes at every level on the linear family (Theorem 10.1). Evidence for the conjecture: §11.

## 5. Why the per-PPP greedy of both papers is not exact

Both papers prove optimality of a greedy that assigns the longest durations first to the least-loaded plane.
The proof (arXiv §3.2) rests on the sentence "the above algorithm gives the optimal distribution of the set
of times into $p$". The no-waiting construction is correct (Theorem 4.1); the optimal distribution is not.

* $d = (6, 10)$, $p = 2$, $t = 5$, PPP $a = (10,10,6,6,6)$, $\bar a = (10,6,6)$: the greedy gives every
  plane a 20-crossing first and ends at 52/68. The partition $\{10,10,10\} \mid \{6,6,6,6,6\}$ gives 60/60.
  The front point (260, 60) is missed.
* $d = (1,3)$, $c = (9,5)$, $t = 4$, $p = 2$: the point (42, 12) needs the plane making the drop-off to also
  take the long crossing; the no-duplicate greedy ends at 14.

Deciding $M(X) \le 2T$ is strongly NP-complete (Theorem 8.1), so no polynomial greedy can be exact unless
P = NP.

## 6. Non-symmetric case

### 6.1 Lower bounds

Lemmas 3.1–3.3 hold. Role configurations (Definition 4.2) carry role-dependent durations: a crossing at $w$
costs $d_w + \bar d_w$, a drop-off $2d_w$, a pick-up $2\bar d_w$.

**Theorem 6.1 (converse to role configurations) [N1].** Assume (A1-NS). For every feasible plan with cost $C$
and makespan $M$ there is a role configuration on all $p$ planes with passenger count $t$, cost at most $C$
and $\lambda_k \le F_k \le M$ for every $k$. (AΔ) is not needed.

*Proof.* Replace a central flight $a \to b$ departing at $e$ by $a \to h \to b$ through a hub $h$ with
$\mathrm{dur}(a,h) + \mathrm{dur}(h,b) \le d_{ab}$, which exists by (A1-NS). The plane waits in $b$ until its
next departure, and a passenger on board stays on board through $h$. Then clean (Lemma 3.1): a journey that
passes through $C_I$ now starts there, one that passes through $C_G$ ends there. The plan is simple, costs no
more, and no $F_k$ increases. Lemmas 4.3(b) and 4.4 conclude. $\square$

**Lemma 6.2 (relaxed role loads).** Assume (AΔ). For every feasible plan with cost $C$ and makespan $M$ there
are multisets $\mathrm{Dr}_k$, $\mathrm{Pk}_k$, $\mathrm{Cr}_k$ ($k = 1,\dots,p$) with $|\mathrm{Cr}_k|$ odd,
$\sum_k |\mathrm{Dr}_k| = \sum_k |\mathrm{Pk}_k|$ (only the totals balance), passenger count $t$, cost at most
$C$ and $\lambda_k \le F_k \le M$. So the least cost $L_{\rm NS}(T)$ of such a family with every
$\lambda_k \le T$ is a lower bound for every plan of makespan at most $T$, whatever its central flights and
including shuttle triples (§6.4).

*Proof.* Give each segment $\gamma$ any of its landings. By Lemma 3.3(b), $F(\gamma)$ is at least the role
duration of its type at that landing, reading $A$ and $\bar A$ as crossings, $B$ as drop-offs and $\bar B$ as
pick-ups. A segment has exactly one flight departing from a hub (its first) and one arriving in a hub (its
last). Mapping each passenger to the segment of its first flight (from $C_I$, so of type $A$ or $B$) and to
the segment of its last flight (into $C_G$, of type $A$ or $\bar B$) is injective by capacity, so
$\#A + \#B \ge t$ and $\#A + \#\bar B \ge t$. Take all $A$ and $\bar A$ segments of plane $k$ as its
crossings, so $|\mathrm{Cr}_k| = 2\#A_k - 1$ (Lemma 2.1), and $\min(\#B, \#\bar B)$ of the $B$ and of the
$\bar B$ segments as drop-offs and pick-ups. The passenger count is $\min(\#B, \#\bar B) + \#A \ge t$.
Shrink as in Lemma 4.4, removing in the second case a drop-off and a pick-up anywhere. $\square$

### 6.2 Scheduling role configurations

Fix a role configuration on all $p$ planes with passenger count $t$, an order of the drop-offs and of the
pick-ups of every plane, written $\mathrm{Dr}_u = (\mathrm{Dr}_u[1], \mathrm{Dr}_u[2], \dots)$ and
$\mathrm{Pk}_v = (\mathrm{Pk}_v[1], \dots)$, and a *link matching* $\mathcal L$: at each city, a bijection
between its copies in $\sum_k \mathrm{Dr}_k$ and in $\sum_k \mathrm{Pk}_k$. A link $(u, j; v, l)$ at city
$i$ means that the passenger dropped by the $j$-th drop-off of $u$ is picked up by the $l$-th pick-up of $v$.

A *schedule* of these data is a feasible plan such that:

* the route of plane $k$ is a concatenation of simple segments: exactly one $B$ at each element of
  $\mathrm{Dr}_k$, in the order of $\mathrm{Dr}_k$; exactly one $\bar B$ at each element of $\mathrm{Pk}_k$,
  in the order of $\mathrm{Pk}_k$; exactly one $A$ or $\bar A$ at each element of $\mathrm{Cr}_k$; and no
  other segment;
* for each link $(u, j; v, l)$ at $i$, one passenger's journey is the flight $C_I \to i$ of the $j$-th $B$ of
  $u$ followed by the flight $i \to C_G$ of the $l$-th $\bar B$ of $v$; for each $A$, one passenger's journey
  is its two flights; there are no other journeys.

The *template* is the schedule in which every plane flies its drop-offs in order from time 0, then its
crossings $A, \bar A, \dots, A$, then its pick-ups in order; every flight departs as soon as the plane
arrives, except the flight $i \to C_G$ of a pick-up, which departs at the later of the plane's arrival in $i$
and the arrival of the linked drop-off. The *least makespan* of a role configuration is the minimum makespan
of a schedule over all orders and matchings (finitely many).

Let $\mathrm{Pre}_u(j) = 2\sum_{j' < j} d_{\mathrm{Dr}_u[j']}$ and
$\mathrm{Suf}_v(l) = 2\sum_{l' > l} \bar d_{\mathrm{Pk}_v[l']}$.

**Lemma 6.3 (template) [N3].** The template is a schedule, and its makespan is
$$M_{\rm tmpl} = \max\Big(\max_k \lambda_k,\ \max_{(u,j;\,v,l) \in \mathcal L \text{ at } i}\ \mathrm{Pre}_u(j) + d_i + \bar d_i + \mathrm{Suf}_v(l)\Big).$$
Every schedule of the same configuration, orders and matching has makespan at least $M_{\rm tmpl}$. So the
least makespan of a role configuration is the minimum of $M_{\rm tmpl}$ over orders and matchings. No
assumption on durations is needed.

*Proof.* *Lower bound.* In any such schedule, plane $u$ starts its $j$-th drop-off after flying its earlier
drop-offs, so this drop-off reaches $i$ no earlier than $\mathrm{Pre}_u(j) + d_i$. The linked pick-up of $v$
leaves $i$ no earlier, flies $\bar d_i$ to $C_G$, and $v$ then still flies its later pick-ups, at least
$\mathrm{Suf}_v(l)$. Also every plane flies $\lambda_k$ (Lemma 3.3(c)), so it finishes no earlier than
$\lambda_k$.

*Template.* Drop-offs come first and wait for nothing, so the $j$-th drop-off of $u$ reaches $i$ exactly at
$\mathrm{Pre}_u(j) + d_i$, and no wait is cyclic. Let $\phi_v(l)$ be the time $v$ returns to $C_G$ after its
$l$-th pick-up, with $\phi_v(0) = 2\delta(\mathrm{Dr}_v) + \delta(\mathrm{Cr}_v) + \bar\delta(\mathrm{Cr}_v)$.
For the link $(u,j;v,l)$ at $i$,
$\phi_v(l) = \max\big(\phi_v(l-1) + 2\bar d_i,\ \mathrm{Pre}_u(j) + d_i + \bar d_i\big)$. Unrolling, the last
return of $v$ is the maximum of $\lambda_v$ and of the terms of the formula for the links into $v$. Planes
without pick-ups finish at $\lambda_k$. The passenger count is $t$, so every passenger is carried. $\square$

**Corollary 6.4 (one pick-up never waits harmfully) [W1].** Assume (AΔ-path). If every plane has at most one
pick-up, then $M_{\rm tmpl} = \max_k \lambda_k$ for every order and matching. The same holds if every plane has
at most one drop-off.

*Proof.* For a link $(u,j;v,1)$ at $i$, $\mathrm{Suf}_v(1) = 0$ and
$\mathrm{Pre}_u(j) \le 2\delta(\mathrm{Dr}_u) - 2d_i$. Plane $u$ has a crossing $z$, since $|\mathrm{Cr}_u| \ge 1$,
and $\bar d_i \le d_i + d_z + \bar d_z$. So the term is at most $2\delta(\mathrm{Dr}_u) + d_z + \bar d_z \le \lambda_u$.
For the second claim, take a link $(u,1;v,l)$ at $i$. Then $\mathrm{Pre}_u(1) = 0$ and
$\mathrm{Suf}_v(l) \le 2\bar\delta(\mathrm{Pk}_v) - 2\bar d_i$. Plane $v$ has a crossing $z$, and
$d_i \le \bar d_i + \bar d_z + d_z$, so the term is at most
$2\bar\delta(\mathrm{Pk}_v) + d_z + \bar d_z \le \lambda_v$. $\square$

This corrects §6.2 of the first version, which claimed that a pick-up after long drop-offs can push the
makespan above the largest load. Under (AΔ-path) a single pick-up never does.

**Conjecture 6.5 (no harmful waiting) — false.** The conjecture stated: assume (AΔ-path); every role
configuration has orders and a matching with $M_{\rm tmpl} = \max_k \lambda_k$. A weaker, front-level form,
which would have sufficed for exact fronts, stated that the front equals the Pareto set of
(cost, $\max_k \lambda_k$) over role configurations. Both forms are false.

**Proposition 6.5 (harmful waiting).** Take $n = 2$ central cities with $d = (3, 19)$, $\bar d = (3, 11)$,
$c = (5, 1)$, $t = 7$ passengers and $p = 4$ planes, and no central flights (so (A1-NS) holds). (AΔ-path)
holds: $\bar d_i \le d_i + d_z + \bar d_z$ for all $i, z$. The cheapest role configuration with every
$\lambda_k \le 73$ costs 14, but no plan of makespan $\le 73$ costs less than 18: the role-load front and the
true front differ.

*Status.* The second half is computer-checked: the brute-force oracle (`tests/oracle/bruteForce.hpp`), which
enumerates every pattern plan with its exact waiting, gives the front $(10, 90), (14, 74), (18, 68),
(22, 66), (26, 52), (34, 42), (38, 36), (42, 30), (50, 18)$ as (cost, makespan), and `zeno`'s upper front
equals it. The first half, and why every configuration of cost 14 and loads $\le 73$ waits, is the
following argument.

*Cost-14 configurations at level 73.* Write $1$ and $2$ for the cities. Loads: a crossing weighs 6 in city 1
and 30 in city 2; a drop-off 6 and 38; a pick-up 6 and 22. A role configuration has $s = 10$ landings, so
cost 14 means one landing in city 1 and nine in city 2. Each plane flies an odd number of crossings, and only
one plane, $v$, can cross in city 1; a plane crossing three times in city 2 weighs 90. So the three other
planes cross once, in city 2 (load 30), and with $\ell$ links (drop-off/pick-up pairs) $v$ crosses
$10 - 2\ell - 3$ times. For $\ell \le 2$, $v$ crosses at least 3 times, two of them in city 2, so it weighs
at least 66 and takes no link landing (a pick-up in city 2 adds 22); the other three planes can take one
link landing each (30 + 38 or 30 + 22; two would exceed 73), which leaves at least one of the $2\ell$ link
landings unplaced when $\ell = 2$, and fails the crossing count when $\ell \le 1$ ($v$ would weigh
$6 + 4 \cdot 30$ or more). So $\ell = 3$: every plane crosses once, the three planes crossing in city 2 take
one link landing each, and $v$ takes the other three; three drop-offs on $v$, or two, or one with two
pick-ups, would weigh $6 + 38 + 38$ or more, so $v$ has three pick-ups (load $6 + 3 \cdot 22 = 72$) and the
three others one drop-off each (load 68). Such a configuration exists, so the role-load bound at level 73 is
14.

*Why it waits.* Every drop-off reaches city 2 at time $\ge 19$. Plane $v$ starts in $C_I$ with no drop-off,
so it crosses first and reaches city 2 for its first pick-up at time $6 + 11 = 17$; it waits until 19, and
its two further pick-ups take 44 more: it finishes at $19 + 11 + 44 = 74 > 72 = \lambda_v$. The
configuration-level form of the conjecture fails on it, and since every cost-14 configuration at level 73 is
of this shape, so does the front-level form, as the oracle confirms. $\square$

The same mechanism also opens the gap between makespans 42 and 52: a configuration of cost 30 has all loads
$\le 50$, but its pick-up plane waits 2 at its first pick-up and finishes at 52.

What survives: the role-load front is a lower bound (Theorem 6.1), the template is optimal for fixed orders
and matching (Lemma 6.3), and Corollary 6.4 (one pick-up or one drop-off per plane) holds. The exact front of
a non-symmetric instance is therefore the Pareto set of (cost, exact schedule makespan) over role
configurations, where the exact makespan of a configuration is the minimum of $M_{\rm tmpl}$ over orders and
matchings. Mechanism: harmful waiting needs a plane with several pick-ups in a city $y$ whose first pick-up
arrives before the earliest drop-off there, i.e. $\min(\text{crossing}) + \bar d_y < d_y$; (AΔ-path) bounds
$\bar d$ by $d$ but not $d$ by $\bar d$. A configuration-level search (`checks/waiting_search.cpp`) finds such
configurations among random ones once every plane's crossing phase is short (§11).

### 6.3 Exact role-load bound

Let $E_{\rm NS}(T)$ be the least cost of a role configuration on the $p$ planes with passenger count $t$ and
every $\lambda_k \le T$. Under (A1-NS), by Theorem 6.1, every plan of makespan $M$ costs at least
$E_{\rm NS}(\lfloor M\rfloor)$ (integer durations). Let $G^{\rm cr}[r][\tau]$ be the least cost of $r$
crossings of total duration $\delta + \bar\delta \le \tau$, computed like $G$ in Lemma 7.2.

**Proposition 6.6 (imbalance-vector DP) [N5].** Process the planes in order, with states $(k, j, v)$: $k$
planes processed, $j$ landings used, and $v = \sum_{k' \le k} (\mathrm{Dr}_{k'} - \mathrm{Pk}_{k'}) \in \mathbb Z^n$
the imbalance. A plane option is a triple $(\mathrm{Dr}, \mathrm{Pk}, r)$ with $r$ odd, of weight
$c(\mathrm{Dr}) + c(\mathrm{Pk}) + G^{\rm cr}[r][T - 2\delta(\mathrm{Dr}) - 2\bar\delta(\mathrm{Pk})]$; it adds
$|\mathrm{Dr}| + |\mathrm{Pk}| + r$ to $j$ and $\mathrm{Dr} - \mathrm{Pk}$ to $v$. With states restricted to
$\|v\|_1 \le t - p$, the shortest path from $(0, 0, 0)$ to $(p, s, 0)$ has weight $E_{\rm NS}(T)$. There are at
most $(p+1)(s+1)\sum_{u \le t-p} 2^u \binom{n}{u}\binom{t-p}{u}$ states, a polynomial in $n$ and $s$ for fixed
$t - p$.

*Proof.* A path gives a role configuration whose cost is its weight, with $G^{\rm cr}$-optimal crossings:
the final imbalance 0 is the balance, and $|X| = s$ gives the passenger count $(s + p)/2 = t$. Conversely,
take a role configuration with passenger count $t$ and every $\lambda_k \le T$, and let
$N = \sum_k |\mathrm{Dr}_k|$ be its number of links. From $s = 2N + \sum_k |\mathrm{Cr}_k| \ge 2N + p$,
$N \le t - p$. For a prefix of $k$ planes and a city $i$, let $D^{\le}(i)$, $P^{\le}(i)$ count the drop-offs
and pick-ups at $i$ of these planes, and $D^{>}(i)$, $P^{>}(i)$ those of the others. By the balance,
$v_k(i) = D^{\le}(i) - P^{\le}(i) = P^{>}(i) - D^{>}(i)$, so $|v_k(i)| \le D^{\le}(i)$ if $v_k(i) \ge 0$ and
$|v_k(i)| \le D^{>}(i)$ otherwise. Summing over $i$, $\|v_k\|_1 \le N \le t - p$, so the configuration is a
path of the restricted graph, of weight at most its cost. To count the vectors $v$, choose a support of $u$
cities, signs, and positive values summing to at most $t - p$. $\square$

### 6.4 Short central flights: the shuttle triple

Without (A1-NS), the $2t-p$ model is beaten (11 of 140 random instances). The smallest example found has
$n = 2$, $t = 4$, $p = 3$, $d = (5,3)$, $\bar d = (2,3)$, $c = (1,5)$, and the central flight as short as (AΔ)
allows. Its point (18, 12) needs 6 landings, one more than $s = 5$.

This is the arXiv paper's $B\bar A\bar B$ situation: a drop-off at $i$, a shuttle $C_G \to i \to j \to C_I$,
and a pick-up at $j$.

**Conjecture 6.7 (extended Proposition I).** Under (AΔ), the front equals the front of role configurations
extended with *shuttle triples* (each adding exactly one landing), with exact makespans.

The bound of Lemma 6.2 stays valid with shuttle triples. The arXiv construction of §3.3 (virtual cities)
encodes the triples. It is sound only if a drop-off or pick-up at a virtual city is used together with its
shuttle. Its equation (4) should read $d^{\bar B}_k = 2\bar d_j$. The non-symmetric proofs of §2.3 need
repairs as well:

* the "finite number of patterns" argument is defeated by 2-cycles;
* "the central pattern cannot be $A$" is unproved;
* the multiplicity "exactly 1" is unproved.

### 6.5 Non-symmetric algorithm (conditional)

1. Bracket on every level. Below: $L_{\rm NS}$ (Lemma 6.2, valid under (AΔ), shuttle triples included) and
   $E_{\rm NS}$ (Proposition 6.6, valid under (A1-NS) by Theorem 6.1). Above: plans built by the template
   (Lemma 6.3), whose makespan equals the largest role load when every plane picks up at most once or drops
   off at most once (Corollary 6.4).
2. A point is exact only when a simulated plan meets the lower bound. Elsewhere, search over orders and
   matchings with the closed form of Lemma 6.3; Proposition 6.5 shows that the role-load bound can stay
   strictly below the front, so closing such a gap needs a search over the role configurations cheaper than
   the achieved point, each with its exact makespan. If Conjecture 6.7 holds, add shuttle triples.

The bounds were loose in the measurements (certified on 18–28% of instances), so the search dominates.

## 7. Exact algorithm (symmetric case)

### 7.1 Reformulation

Assume integer durations: scale rational durations to integers and divide them by their gcd $g$. For an
integer $T \ge 0$ let
$$E(T) = \min\{c(X) : |X| = s,\ X_1,\dots,X_p \text{ admissible},\ \delta(X_k) \le T\ \forall k\}.$$
$E$ is non-increasing, and $L \le E$ with $L$ from Lemma 3.4.

**Proposition 7.1.** Under (S) and (A1), $\mathcal F = \{(E(T), 2T) : T \in \mathbb N,\ E(T) < E(T-1)\}$ with
$E(-1) = \infty$, makespans in units of $g$.

*Proof.* Here $M(X)$ is an even integer and $E(T) = \min\{c(X) : M(X) \le 2T\}$. Let $(c, 2T) \in \mathrm{Min}\,\mathcal X$
(Corollary 4.8). Then $c = E(T)$, otherwise a cheaper $X$ with $M(X) \le 2T$ dominates it; and $E(T-1) > c$,
otherwise some $X$ with $c(X) \le c$ and $M(X) < 2T$ dominates it. Conversely, let $E(T) < E(T-1)$ and let $X$
attain $E(T)$; then $M(X) = 2T$. A point $(c(Y), M(Y)) \in \mathcal X$ dominating it has $M(Y) \le 2T$, hence
$M(Y) = 2T$ (otherwise $c(Y) \ge E(T-1) > E(T)$), and then $c(Y) = E(T)$. $\square$

### 7.2 One-plane table

$G[0][\tau] = 0$ for $\tau \ge 0$, $G[m][\tau] = \min_{i:\,d_i \le \tau} (c_i + G[m-1][\tau - d_i])$, and
$G[m][\tau] = \infty$ for $\tau < 0$.

**Lemma 7.2.** $G[m][\tau] = \min\{c(Y) : |Y| = m,\ \delta(Y) \le \tau\}$, and $G$ is non-increasing in $\tau$.

*Proof.* Induction on $m$: removing an element $i$ of an optimal $Y$ leaves an $(m-1)$-multiset within
$\tau - d_i$, and adding $i$ to such a multiset gives an $m$-multiset within $\tau$. $\square$

### 7.3 Bounds, and when they are exact

The bounds combine *gadgets*, sets of planes with their groups, by a knapsack over planes and landings:
$\mathrm{For}[0][0] = 0$ and $\mathrm{For}[P][J] = \min(\mathrm{For}[P - q][J - j] + \text{cost})$ over gadgets of
$q$ planes and $j$ landings. The bound is $\mathrm{For}[p][s]$. Let $\hat m = s - p + 1$, the largest group.

* $L$: one plane with $m \in [1, \hat m]$ landings, cost $G[m][T]$. This is the $L$ of Lemma 3.4.
* $U$: one plane with $m$ odd, cost $G[m][T]$; and a *pair*, two planes of even sizes $a$ and $b$ linked at
  $i$, cost $2c_i + G[a-1][T - d_i] + G[b-1][T - d_i]$.
* $U_3$: the gadgets of $U$ and a *chain*, three planes of sizes $a$ (even), $b$ (odd, at least 3) and $b'$
  (even), the first two linked at $i$ and the last two at $j$ ($i = j$ allowed), cost
  $2c_i + 2c_j + G[a-1][T-d_i] + G[b-2][T-d_i-d_j] + G[b'-1][T-d_j]$.

**Proposition 7.3.** $L(T) \le E(T) \le U_3(T) \le U(T)$.

*Proof.* $L \le E$: $E$ minimises over a subset. $U_3 \le U$: more gadgets. $E \le U_3$: each gadget with
$G$-optimal fillers is a link tree satisfying (F1)–(F2). A single plane has odd size and degree 0; in a pair,
both planes have even size and degree 1; in a chain, the ends have even size and degree 1 and the middle has
odd size and degree 2. A combination is a link forest whose groups have duration at most $T$, admissible by
Lemma 2.6. $\square$

**Proposition 7.4.** If $q_{\max} \le 2$, that is $p \le 2$ or $t \le p + 1$, then $E = U$. If
$q_{\max} \le 3$, that is $p \le 3$ or $t \le p + 2$, then $E = U_3$.

*Proof.* Take $X$ attaining $E(T)$ and a link forest (Lemma 2.6). Its trees have at most $q_{\max}$ planes
(Corollary 2.7), and trees with 1, 2 or 3 vertices are a vertex, an edge and a path. In each, a group consists
of its link copies and a filler of the size and budget used in the gadget formula, whose cost is at least the
corresponding $G$ value (Lemma 7.2). So the forest costs at least some combination of gadgets. $\square$

**Pairs are not enough.** Durations $(4,2,6,7)$ with multiplicities $(2,1,3,1)$ and $p = 3$: admissible
partitions reach 24 with $\{6,6\}$, $\{4,7\}$, $\{4,2,6\}$. The two even planes share no city and are linked
through the odd one, a chain. Pairs reach only 26.

### 7.4 The link-forest DP

Fix a level $T$. By Lemma 2.6 and Corollary 2.7, $E(T)$ is the least cost of $p$ groups with $s$ landings in
total, of duration at most $T$ each, carrying a link forest whose trees have at most $q_{\max}$ planes. Root
every tree at a plane. The tables below are those of the prototype `treeDP` (its names in brackets).

* $\mathrm{Ch}_q[\tau][j]$ [`K`]: least cost of a multiset of *child items*. An item is a link label $b$,
  with one copy of $b$ in the parent's group, and a subtree hanging from that link. The labels' durations sum
  to $\tau$, the subtrees have $q$ planes, and $j$ counts one landing per item plus the subtrees' landings.
  $\mathrm{Ch}_0[0][0] = 0$, and the other entries of $\mathrm{Ch}_0$ are $\infty$.
* $\mathrm{Sub}_a[q][j]$ [`Sb`]: least cost of a subtree with $q$ planes and $j$ landings whose root plane
  holds one copy of $a$ for its parent link, counted in $j$.
* $\mathrm{Root}[q][j]$ [`Root`]: least cost of a tree with $q$ planes and $j$ landings.
* $\mathrm{For}[P][J]$ [`Fo`]: least cost of a forest on $P$ planes with $J$ landings.

For $q = 1, 2, \dots, q_{\max}$ in this order, with $r$ ranging over odd integers at least 1 and $\tau$ over
$[0, T]$:
$$\mathrm{Sub}_a[q][j] = \min_{\tau,\ j' + 1 + r = j}\big(c_a + \mathrm{Ch}_{q-1}[\tau][j'] + G[r][T - d_a - \tau]\big),\qquad
\mathrm{Root}[q][j] = \min_{\tau,\ j' + r = j}\big(\mathrm{Ch}_{q-1}[\tau][j'] + G[r][T - \tau]\big),$$
and, for $q < q_{\max}$,
$$\mathrm{Ch}_q[\tau][j] = \min_{b,\ 1 \le q' \le q,\ j'}\big(\mathrm{Ch}_{q-q'}[\tau - d_b][j - 1 - j'] + c_b + \mathrm{Sub}_b[q'][j']\big).$$
Finally $\mathrm{For}[0][0] = 0$ and
$\mathrm{For}[P][J] = \min_{1 \le q \le \min(P, q_{\max}),\ j}\big(\mathrm{For}[P-q][J-j] + \mathrm{Root}[q][j]\big)$;
the value is $\mathrm{For}[p][s]$. Every entry uses entries computed before it: $\mathrm{Sub}$ and
$\mathrm{Root}$ for $q$ use $\mathrm{Ch}_{q-1}$, and $\mathrm{Ch}_q$ uses $\mathrm{Sub}_\cdot[q']$ with
$q' \le q$ and $\mathrm{Ch}_{q-q'}$ with $q - q' < q$. The prototype lets $q$ run up to $p$; by Corollary 2.7
the cap $q_{\max}$ loses nothing.

**Theorem 7.5.** $\mathrm{For}[p][s] = E(T)$. Given $G$, the computation takes
$O(n\,q_{\max}^2 s^2 T + p\,q_{\max} s^2)$ time and $O(q_{\max} s T + n q_{\max} s + p s)$ memory per level.

*Proof.* A *rooted structure* is a rooted tree on $q$ planes with city-labelled edges and a group $X_u$ for
each plane, such that the edges at $u$ have distinct copies in $X_u$ (F1), $r_u = |X_u| - \deg(u)$ is odd and
$\delta(X_u) \le T$. In a *hanging* structure with label $a$, the root's group holds one more copy of $a$,
counted in its degree and its duration. Each group splits into its link copies and its free landings, of odd
size $r_u$.

($\ge$) By induction on $q$, every finite entry is the cost of a structure of its kind, with $G$-optimal free
landings (Lemma 7.2): $\mathrm{Sub}_a$ and $\mathrm{Root}$ add a root with $r$ free landings within the
remaining budget to a multiset of child items, and $\mathrm{Ch}_q$ adds one item to a multiset of items. The
forest behind $\mathrm{For}[p][s]$ satisfies (F1)–(F2) and has $p$ planes, $s$ landings and groups of duration
at most $T$, so it is admissible by Lemma 2.6, and $\mathrm{For}[p][s] \ge E(T)$.

($\le$) Take $X$ attaining $E(T)$ and a link forest (Lemma 2.6); its trees have at most $q_{\max}$ planes
(Corollary 2.7). Root each tree. By induction on subtree size: the child items of a plane $u$ cost at least
$\mathrm{Ch}_{q-1}[\tau_u][j']$, where $\tau_u$ sums $d_b$ over the child links of $u$ (remove one item and
bound its subtree by $\mathrm{Sub}_b$); the free landings of $u$ have size $r_u$ and duration at most
$T - \tau_u$, less $d_a$ for a hanging root, so they cost at least the matching $G$ entry. So each subtree costs
at least its $\mathrm{Sub}$ or $\mathrm{Root}$ entry, and the forest at least $\mathrm{For}[p][s]$.

*Complexity.* $\mathrm{Ch}$ has $q_{\max}(T+1)(s+1)$ entries, each a minimum over $b$, $q'$ and $j'$, which is
$O(n\,q_{\max} s)$. $\mathrm{Sub}$ and $\mathrm{Root}$ range over $q$, $a$, $\tau$, $j'$ and $r$:
$O(n\,q_{\max} T s^2)$. $\mathrm{For}$ costs $O(p\,q_{\max} s^2)$. $\square$

Over the levels $[T_{\rm lo}, T_{\rm hi}]$ of Proposition 7.10, with $G$ built once in $O(n\,s\,T_{\rm hi})$,
the whole front takes $O(n\,q_{\max}^2 s^2\, T_{\rm hi}(T_{\rm hi} - T_{\rm lo} + 1))$ time. This is
pseudo-polynomial, since $T_{\rm hi} \le d_{\max}\kappa$.

### 7.5 The σ-DP and the Pareto-set variant

Let $w = \min(p-1,\ t-p)$. The *σ-graph* at level $T$ has nodes $(k, j, \sigma)$ with $0 \le k \le p$,
$0 \le j \le s$ and $\sigma$ a set of at most $w$ cities. Its arcs go from $(k, j, \sigma)$ to
$(k+1,\ j+m,\ \sigma \triangle \eta)$ for $1 \le m \le \hat m$ and a set $\eta$ of cities with
$|\eta| \equiv m + 1 \pmod 2$, $|\eta| \le \min(m-1, w)$ and $|\sigma \triangle \eta| \le w$. The arc has weight
$\mathrm{wt} = c(\eta) + G[m - |\eta|][T - \delta(\eta)]$; arcs of infinite weight are omitted.

**Theorem 7.6 (σ-DP) [Claim C].** The shortest path from $(0, 0, \emptyset)$ to $(p, s, \emptyset)$ has
weight $E(T)$.

*Proof.* *Paths give admissible partitions.* Take a path with options $(m_k, \eta_k)$. Let $R_k$ be a
$G$-optimal $(m_k - |\eta_k|)$-multiset within $T - \delta(\eta_k)$ and $X_k = \eta_k + R_k$. Then $|X| = s$,
$\delta(X_k) \le T$, and $h_{k,i} = [i \in \eta_k]$ is a parity matrix: (h1) as $\eta_k \le X_k$; (h2) as
$|\eta_k| \equiv m_k + 1$; (h3) because the final $\sigma = \eta_1 \triangle \dots \triangle \eta_p$ is empty,
so every city lies in an even number of the $\eta_k$. So the path's weight is at least $E(T)$.

*Admissible partitions give paths.* Take $X$ attaining $E(T)$ and a parity matrix touching at most $w$ cities
(Lemma 2.8(c)). With the options $(|X_k|, \eta_k)$, every prefix
$\sigma_k = \eta_1 \triangle \dots \triangle \eta_k \subseteq Z(h)$ has at most $w$ cities,
$|\eta_k| \le \min(|X_k| - 1, w)$, and $R_k = X_k - \eta_k$ costs at least
$G[|X_k| - |\eta_k|][T - \delta(\eta_k)]$. So some path has weight at most $c(X)$. $\square$

*Size.* An arc joins sets $\sigma, \sigma'$ with $|\sigma|, |\sigma'|, |\sigma \triangle \sigma'| \le w$, so
$|\sigma \cup \sigma'| \le \lfloor 3w/2\rfloor$; there are at most
$N_w = \sum_{u \le \lfloor 3w/2\rfloor} \binom{n}{u} 3^u$ such pairs. The DP takes $O(p\,s\,\hat m\,N_w)$ time
per level: polynomial in $n$ for fixed $w$, practical only for small $w$ or few cities. The link-forest DP is
the default otherwise.

**Lemma 7.7 (Pareto sets).** Let $\otimes$ be a binary operation on $\mathbb K^2$ that is monotone in the
product order. For finite $A$ and $B$, $\mathrm{Min}(A \otimes B) = \mathrm{Min}(\mathrm{Min}\,A \otimes \mathrm{Min}\,B)$
and $\mathrm{Min}(A \cup B) = \mathrm{Min}(\mathrm{Min}\,A \cup \mathrm{Min}\,B)$, where
$A \otimes B = \{a \otimes b : a \in A, b \in B\}$.

*Proof.* Every $a \in A$ is weakly dominated by some $a^\star \in \mathrm{Min}\,A$ (finiteness), so
$a \otimes b$ is weakly dominated by $a^\star \otimes b^\star \in \mathrm{Min}\,A \otimes \mathrm{Min}\,B \subseteq A \otimes B$.
This subset is finite and dominating, and Lemma 1.1 applies. The same argument works for $\cup$. $\square$

**Proposition 7.8 (Pareto-set variant) [PS].** In the σ-graph, replace the weight of the arc with option
$(m, \eta)$ by the finite set
$\mathrm{Opt}(m, \eta) = \mathrm{Min}\{(c(\eta) + G[m - |\eta|][\tau],\ \delta(\eta) + \tau) : 0 \le \tau \le T_{\rm hi} - \delta(\eta)\}$.
Combine along paths with $(c, \tau) \otimes (c', \tau') = (c + c', \max(\tau, \tau'))$, and keep at each node
the $\mathrm{Min}$ over its incoming arcs. The set obtained at $(p, s, \emptyset)$ is
$\mathrm{Min}\{(c(X), \max_k \delta(X_k)) : |X| = s,\ X_1,\dots,X_p \text{ admissible},\ \max_k \delta(X_k) \le T_{\rm hi}\}$.
Under (S) and (A1) its points $(c, \tau)$ are the front points $(c, 2\tau)$.

*Proof.* $\otimes$ is monotone. $\mathrm{Opt}(m, \eta)$ is the $\mathrm{Min}$ of the points
$(c(\eta) + c(R), \delta(\eta) + \delta(R))$ over all $R$ of size $m - |\eta|$ within the budget: each such
point is weakly dominated by the term with $\tau = \delta(R)$, and each term is attained or weakly dominated by
a $G$-optimal $R$. By Lemma 7.7 and induction over the layers, each node holds the $\mathrm{Min}$ of the
points of all paths reaching it, with arbitrary fillers. By both directions of Theorem 7.6 (with any filler
in place of the $G$-optimal one, and the restriction $w$ being independent of the level), these are exactly
the points of admissible partitions with $|X| = s$. The front statement is Corollary 4.8, and every front point
has $\tau \le T_{\rm hi}$ (Proposition 7.10). $\square$

Combining sets is no better than sweeping the levels in the worst case. It helps when durations are large and
the cost range is narrow.

### 7.6 Reductions and the ends of the front

**Proposition 7.9 (dominance) [DOM].** Let $i \ne i'$ with $d_{i'} \le d_i$ and $c_{i'} \le c_i$. Removing
city $i$ leaves $E(T)$ and $L(T)$ unchanged at every $T$. Under (S) and (A1), it leaves the front unchanged.

*Proof.* Removing a city can only raise $E$ and $L$. Conversely, in an optimal $X$ and its groups, replace
every copy of $i$ by $i'$: costs and durations do not increase. Nothing else is needed for $L$. For $E$, set
$h'_{k,i'} = (h_{k,i} + h_{k,i'}) \bmod 2$ and $h'_{k,i} = 0$. Row sums keep their parity, column $i'$ is the
sum of two even columns, and $h'_{k,i'} = 1$ means $X_k$ contained $i$ or $i'$, so the new group contains
$i'$. The instance without $i$ still satisfies (S) and (A1), and Proposition 7.1 expresses both fronts through
$E$. $\square$

Applied repeatedly: keep one city per class of equal $(d, c)$, and drop every city dominated by another.

**Proposition 7.10 (ends of the front) [END].** Assume (S). Let $d_{\min} = \min_i d_i$,
$c_{\min} = \min_i c_i$ and $d_{\rm cheap} = \min\{d_i : c_i = c_{\min}\}$.

(a) Every plan has makespan at least $M_1 := 2d_{\min}\kappa$, and some plan has makespan $M_1$.

(b) Every plan costs at least $s\,c_{\min}$. A plan of cost $s\,c_{\min}$ has makespan at least
$M_r := 2d_{\rm cheap}\kappa$, and some plan has cost $s\,c_{\min}$ and makespan $M_r$. So
$(s\,c_{\min}, M_r)$ is the cheapest point of $\mathcal F$, and every point of $\mathcal F$ has makespan at
least $M_1$.

(c) With integer durations, $E(T) < \infty$ iff $T \ge T_{\rm lo} := d_{\min}\kappa$, and $E(T) = s\,c_{\min}$
iff $T \ge T_{\rm hi} := d_{\rm cheap}\kappa$. The same holds for $L$.

No assumption on central flights is needed, and zero durations and ties are covered. The cost of the first
point is not in closed form; under (A1) it is $E(T_{\rm lo})$.

*Proof.* Pigeonhole: $p$ non-empty groups of total size $s$ include one of size at least $\kappa$.

(a) Lemma 3.4 gives such groups with $\ell(Y_k) \le M$, so $M \ge 2d_{\min}\kappa$. For the plan, put $s$
copies of a city of duration $d_{\min}$ into groups of sizes $\lfloor s/p\rfloor$ and $\lceil s/p\rceil$, all
non-empty as $s \ge p$. This is admissible by Lemma 2.9 ($s \equiv p$, one city), and Theorem 4.1 gives a
plan of makespan $2d_{\min}\kappa$.

(b) By Lemma 3.2 there are at least $s$ central landings, each costing at least $c_{\min}$. If
$C = s\,c_{\min}$, the multiset $Y$ of Lemma 3.4 has $c(Y) \le s\,c_{\min}$ and $|Y| = s$, so all its cities
cost $c_{\min}$ and have $d \ge d_{\rm cheap}$; pigeonhole gives $M \ge 2d_{\rm cheap}\kappa$. The plan is that
of (a) built on a cheapest city of duration $d_{\rm cheap}$. A point $(C, M) \in \mathcal A$ weakly dominating
$(s\,c_{\min}, M_r)$ has $C = s\,c_{\min}$, hence $M \ge M_r$.

(c) The same arguments apply to $E$ and $L$ directly: every partition has a group of size at least $\kappa$,
and the single-city partitions are admissible. $\square$

Only the levels $[T_{\rm lo}, T_{\rm hi}]$ need computing. On generator instances this range is about ten times
shorter than $[0, d_{\max}\hat m]$.

### 7.7 Orchestration

1. Check the regime: (S), (A1) on every central flight, integrality and $p \le t$. Scale durations to
   integers and divide by their gcd.
2. Remove dominated cities (Proposition 7.9).
3. Compute $T_{\rm lo}$ and $T_{\rm hi}$ (Proposition 7.10), and $G$ up to $T_{\rm hi}$.
4. On every level $T \in [T_{\rm lo}, T_{\rm hi}]$, compute $L(T)$ and $U(T)$. If $q_{\max} \le 2$, then
   $E = U$ (Proposition 7.4).
5. Otherwise compute $U_3$ on the levels with $L < U$. If $q_{\max} \le 3$, then $E = U_3$.
6. Otherwise run the link-forest DP (Theorem 7.5), or the σ-DP (Theorem 7.6) when $w$ is small, on the levels
   with $L < U_3$. As $E$ is non-increasing, $E(a) = E(b)$ for $a < b$ fixes $E$ on $[a, b]$, which allows
   bisection over runs of gap levels.
7. Emit $(E(T), 2T)$, times $g$, wherever $E(T) < E(T-1)$ (Proposition 7.1). For each point, rebuild a
   partition from the exact method's choices (never from $L$ unless it is checked admissible), compute a link
   forest from the partition as in the proof of Lemma 2.6, and build the plan of Theorem 4.1. A parity matrix
   found by the σ-DP need not have a forest support, so the forest is recomputed from the partition.

The C++ solver (branch `feat/exact-front-solver`) follows these steps with the link-forest DP as exact method.

## 8. Complexity

With $\hat m = s - p + 1$, $q_{\max} = \min(p, t-p+1)$, $w = \min(p-1, t-p)$ and $N_w$ as in §7.5:

| Step | Time | Memory |
|---|---|---|
| One-plane table $G$, all levels | $O(n\,\hat m\,T_{\rm hi})$ | $O(\hat m\,T_{\rm hi})$ |
| $L$ and $U$, per level | $O(p\,s^2 + n\,\hat m^2)$ | $O(p\,s + \hat m^2)$ |
| $U_3$ chains, per level | $O(n^2\,\hat m\,s + p\,s^2)$ | $O(p\,s)$ |
| Link-forest DP, per level | $O(n\,q_{\max}^2 s^2 T + p\,q_{\max} s^2)$ | $O(q_{\max} s T + n\,q_{\max} s)$ |
| σ-DP, per level | $O(p\,s\,\hat m\,N_w)$ | $O(s\sum_{u \le w}\binom{n}{u})$ per layer |
| Plan for one point | $O(s + n + p)$, up to union–find | $O(s + n + p)$ |

For all levels, multiply the per-level costs by $T_{\rm hi} - T_{\rm lo} + 1 \le (d_{\rm cheap} - d_{\min})\kappa + 1$.

**Theorem 8.1.** Deciding $M(X) \le 2T$, with $d$, $X$, $p$ and $T$ as input, is strongly NP-complete.

*Proof.* Membership: guess the partition and a parity matrix, and check Definition 2.2. Hardness, from
3-Partition, which is strongly NP-complete: given integers $a_1,\dots,a_{3m}$ with $B/4 < a_i < B/2$ and
$\sum_i a_i = mB$, can they be split into $m$ triples of sum $B$? Take $3m$ cities with $d_i = a_i$, $p = m$
and $t = 2m$ (so $s = 3m$), $X$ containing every city once, and $T = B$. Each city lies in one group, so every
component of $H$ is one plane with its cities, and admissibility makes every group odd (Lemma 2.4). A
3-partition gives $m$ triples, odd groups of duration $B$. Conversely, groups of duration at most $B$ summing
to $mB$ all have duration exactly $B$; a group of one or two items has duration below $B$ and one of four or
more above $B$, so all groups are triples. The numbers are those of the 3-Partition instance, so the reduction
preserves strong NP-hardness. $\square$

**Proposition 8.2 (fixed $p$).** For $p = 2$ the problem stays NP-complete, even with positive durations. For
every fixed $p$ it is solvable in time polynomial in $n$, $s$ and $T$. So for fixed $p$ it is weakly
NP-complete.

*Proof.* Hardness, from Partition: given $a_1,\dots,a_m$ with sum $2B$, is there a subset of sum $B$? Choose an
odd $r \ge m$, add $2r - m$ zero items, and give each of the $2r$ items its own city of duration $a_i + K$,
with $K = B + 1$. Let $p = 2$, $t = r + 1$ (so $s = 2r$) and $T = B + rK$. Distinct cities make both groups
odd (Lemma 2.4). If a subset of sum $B$ exists, pad both sides with zero items to $r$ items each, which
$r \ge m$ allows: two odd groups of duration $B + rK$. Conversely, the two groups have duration exactly
$B + rK$ each, since they sum to $2B + 2rK$. A group with $r + 1$ items or more has duration at least
$(r+1)K > B + rK$, so both groups have $r$ items, and the original items of one of them sum to $B$.

Algorithm for fixed $p$: process the cities one at a time, with states made of the group durations (each in
$[0, T]$), the parities of $|X_k|$ and of $h_k$, and whether each group is non-empty: $(T+1)^p 8^p$ states.
For city $i$, choose how its $X(i)$ copies split among the planes ($O(s^{p-1})$ ways), and an even set of
planes that received a copy, on which $h_{k,i} = 1$ (at most $2^{p-1}$ ways). Conditions (h1) and (h3) are
local to the city, and (h2) is checked at the end. The time is $O(n\,(T+1)^p\, 8^p\, s^{p-1}\, 2^p)$. $\square$

**Corollary 8.3.** $E(T)$, and under (S) and (A1) the front, are computable in pseudo-polynomial time
(Theorem 7.5). So computing the front is not strongly NP-hard unless P = NP. Whether deciding $E(T) \le C$ is
NP-hard, with $t$ in unary as in PDDL, is not established here.

## 9. Certificates

The certificate format is `doc/certificate-format.md` (branch `feat/exact-front-solver`). For a symmetric
instance and a list $(C_1, M_1), \dots, (C_r, M_r)$ with $M_1 < \dots < M_r$ and $C_1 > \dots > C_r$, a checker
verifies four obligations:

1. every listed point has a plan, which the checker simulates: feasible as in §1.2, of cost $C_i$ and
   makespan $M_i$;
2. no plan has makespan below $M_1$: the checker verifies $M_1 = 2d_{\min}\kappa$;
3. for every $i < r$, every plan with makespan below $M_{i+1}$ costs at least $C_i$: the checker establishes a
   lower bound of at least $C_i$ at level $T^\star_i = \lfloor \lfloor (M_{i+1} - 1)/2\rfloor / g\rfloor$ of
   the instance with durations divided by their gcd $g$;
4. no plan costs less than $C_r$: the checker verifies $C_r = s\,c_{\min}$.

**Theorem 9.1 (end to end) [X3].** If obligations 1–4 hold, then $\mathcal F = \{(C_i, M_i) : 1 \le i \le r\}$.

*Proof.* Let $(C, M) \in \mathcal A$. By 2, $M \ge M_1$. Let $i$ be the largest index with $M_i \le M$. If
$i < r$, then $M < M_{i+1}$ and $C \ge C_i$ by 3; if $i = r$, then $C \ge C_r$ by 4. Either way
$(C_i, M_i) \preceq (C, M)$. So the list, contained in $\mathcal A$ by 1, is a finite dominating subset, and by
Lemma 1.1, $\mathcal F$ is its $\mathrm{Min}$. That is the whole list, which is strictly monotone in both
coordinates. $\square$

**The level of obligation 3.** Durations are multiples of $g$. Take a plan with makespan $M < M_{i+1}$, where
$M_{i+1}$ is an integer. The groups $Y_k$ of Lemma 3.4, or $X_k$ of Theorem 4.7, satisfy
$2\delta(Y_k) \le M < M_{i+1}$. Writing $\delta(Y_k) = gx$ with $x$ an integer, $2gx \le M_{i+1} - 1$, so
$x \le T^\star_i$. As $L$ and $E$ are non-increasing, the plan costs at least $L(T^\star_i)$, and under (A1) at
least $E(T^\star_i)$. For a front point $M_{i+1} = 2gT_{i+1}$, so $T^\star_i = T_{i+1} - 1$.

**Obligations 2 and 4** are Proposition 7.10(a) and Lemma 3.2. They need only (S).

**Gap kinds.** Version 1 of the format has two kinds for obligation 3.

* `relaxed`: the checker recomputes $L(T^\star_i) \ge C_i$. This is sound under (S) alone by Lemma 3.4,
  whatever the central flights. A certificate whose gaps are all `relaxed` therefore certifies the front
  without (A1).
* `forest`: the checker recomputes $E(T^\star_i)$ with its own link-forest DP (Theorem 7.5, trees of at most
  $q_{\max}$ planes). This is sound under (S) and (A1) by Theorem 4.7.

Two further kinds are proved sound here and can be added to the format. `gadget` recomputes $U$ when
$q_{\max} \le 2$, or $U_3$ when $q_{\max} \le 3$ (Proposition 7.4). `sigma-potential` is a sparse dual
certificate for the σ-DP, based on the next two lemmas.

**Lemma 9.2 (potentials) [X2].** In a finite graph with arc weights in $\mathbb K$, let $V$ map nodes to
$\mathbb K \cup \{\infty\}$ with $V(\text{target}) \le 0$ and $V(u) \le \mathrm{wt}(u,v) + V(v)$ on every arc.
Then $V(\text{source})$ is at most the weight of every path from the source to the target.

*Proof.* Along a path $u_0, \dots, u_m$ ending at the target, $V(u_m) \le 0$, and by backward induction
$V(u_j) \le \sum_{j' \ge j} \mathrm{wt}(u_{j'}, u_{j'+1})$. $\square$

**Lemma 9.3 (default potentials).** At level $T$, let $G^a[m] = c_a + G[m-1][T - d_a]$, the cheapest
$m$-group containing $a$. Let $L_{\rm rest}(p, s) = 0$, $L_{\rm rest}(p, j) = \infty$ for $j \ne s$, and
$L_{\rm rest}(k, j) = \min_m \big(G[m][T] + L_{\rm rest}(k+1, j+m)\big)$. Let $L^a(p, j) = \infty$ and
$L^a(k, j) = \min_m \min\big(G^a[m] + L_{\rm rest}(k+1, j+m),\ G[m][T] + L^a(k+1, j+m)\big)$. Define
$V_0(k, j, \emptyset) = L_{\rm rest}(k, j)$ and $V_0(k, j, \sigma) = \max_{a\in\sigma} L^a(k, j)$ for
$\sigma \ne \emptyset$. Then $V_0(\text{target}) = 0$ and $V_0(u) \le \mathrm{wt}(u, v) + V_0(v)$ on every arc of the
σ-graph.

*Proof.* By induction from $k = p$, $L^a \ge L_{\rm rest}$, since $G^a[m] \ge G[m][T]$; so
$V_0(v) \ge L_{\rm rest}(v)$ at every node $v$. An arc leaving $(k, j, \sigma)$ with option $(m, \eta)$ has weight
at least $G[m][T]$, and at least $G^a[m]$ when $a \in \eta$, because $\eta$ with its filler is an $m$-group of
duration at most $T$. If $\sigma = \emptyset$:
$V_0(u) = L_{\rm rest}(k, j) \le G[m][T] + L_{\rm rest}(k+1, j+m) \le \mathrm{wt} + V_0(v)$. If $\sigma \ne \emptyset$
and $a \in \sigma$: when $a \in \eta$, $L^a(k, j) \le G^a[m] + L_{\rm rest}(k+1, j+m) \le \mathrm{wt} + V_0(v)$;
when $a \notin \eta$, $a \in \sigma \triangle \eta$, so $V_0(v) \ge L^a(k+1, j+m)$ and
$L^a(k, j) \le G[m][T] + L^a(k+1, j+m) \le \mathrm{wt} + V_0(v)$. Take the maximum over $a$. $\square$

*Sparse potential.* The certificate lists some nodes $u$ with values $V(u)$. The checker sets
$V'(u) = \max(V(u), V_0(u))$ on listed nodes and $V' = V_0$ elsewhere. It checks $V'(\text{target}) \le 0$,
$V'(u) \le \mathrm{wt}(u, v) + V'(v)$ on every arc leaving a listed node, and $V'(\text{source}) \ge C_i$. Arcs
leaving other nodes satisfy the inequality by Lemma 9.3, as $V' \ge V_0$. By Lemma 9.2 and Theorem 7.6,
$E(T^\star_i) \ge C_i$. The listed nodes are those that survive the solver's pruning.

**Primal side [X1].** Obligation 1 is sound if the simulator decides feasibility as defined in §1.2 and
computes cost and makespan. The format stores each plan as legs, so a solver bug in building plans can only
cause a rejection. The same holds if the checker rebuilds plans from partitions with its own Theorem 4.1
construction.

**What a checker trusts.** For `relaxed` certificates: Lemmas 3.2–3.4 and Proposition 7.10. For `forest`, in
addition: Theorem 4.7 (hence (A1), which the checker verifies on the instance), Lemma 2.6, Corollary 2.7 and
Theorem 7.5. For `gadget` and `sigma-potential`: Propositions 7.3–7.4, Theorem 7.6, Lemma 2.8 and Lemmas
9.2–9.3. If the checker applies the dominance reduction, also Proposition 7.9.

*Measured.* On 400 random instances, all but 15 of 5,277 gaps (on 14 instances) close with `relaxed`, so
386 of the 400 fronts are certified by Lemma 3.4 alone, without Theorem 4.7. On the linear family every gap
closes this way (Theorem 10.1).

## 10. The linear family (default generator)

With the default options (`-C 3 -D 3`, after the solver's reordering), the generator produces $d_i = r_0 i$ and
$c_i = r_0(n + 1 - i)$ for $i = 1,\dots,n$, where $r_0$ is the integer `adjustCoef`. Cost is affine and
decreasing in duration, and the durations form the full progression $r_0, 2r_0, \dots, nr_0$. Dividing
durations by $r_0$ (§7.1) gives $d_i = i$ and $c_i = \alpha - \beta i$, with $\alpha = r_0(n+1)$ and
$\beta = r_0$.

**Theorem 10.1.** Assume (S), $d_i = i$ and $c_i = \alpha - \beta i$ for $i = 1,\dots,n$, with $\beta \ge 0$ and
$\alpha \ge \beta n$. Let $q_0 = \lfloor s/p\rfloor$ and $\rho = s - pq_0$. For every integer $T \ge \kappa$,
$$L(T) = E(T) = \alpha s - \beta\,\Phi(T), \qquad \Phi(T) = (p - \rho)\min(T,\ nq_0) + \rho\min(T,\ n(q_0+1)),$$
and $L(T) = E(T) = \infty$ for $T < \kappa$. Consequently, whatever the central flights, the front is
$$\mathcal F = \{(\alpha s - \beta\,\Phi(T),\ 2T) : \kappa \le T \le n\kappa\} \text{ if } \beta > 0, \qquad
\mathcal F = \{(\alpha s,\ 2\kappa)\} \text{ if } \beta = 0,$$
with makespans in units of $r_0$. For $\beta > 0$ it has $(n-1)\kappa + 1$ points.

*Proof.* (1) *Affine cost.* $c(Y) = \alpha |Y| - \beta\,\delta(Y)$. An $m$-multiset of cities can have any
duration in $[m, nm]$: start from $m$ copies of city 1 and raise one landing by one at a time. So by Lemma 7.2,
$G[m][T] = \alpha m - \beta\min(T, nm)$ for $1 \le m \le T$, and $G[m][T] = \infty$ for $m > T$.

(2) *Convexity.* $m \mapsto \min(T, nm)$ is concave, so $m \mapsto G[m][T]$ is convex on $[1, T]$. A sum
$\sum_k G[m_k][T]$ with $\sum_k m_k = s$ is then minimised by the *balanced profile*, with $p - \rho$ groups
of size $q_0$ and $\rho$ of size $q_0 + 1$: if $m_u \ge m_v + 2$, moving one landing from $u$ to $v$ does not
increase the sum. The profile is feasible iff $\kappa \le T$; otherwise $L = E = \infty$ by
Proposition 7.10(c). So $L(T) = \sum_k G[m_k][T] = \alpha s - \beta\,\Phi(T)$.

(3) *Admissibility.* Give every group of size $m$ the same $G$-optimal multiset. Exactly one of $q_0$ and
$q_0 + 1$ is even, so all even groups are equal, and Lemma 2.9 makes the partition admissible. It costs
$L(T)$, so $E(T) \le L(T) \le E(T)$.

(4) *Front.* By Lemma 3.4 a plan with makespan $M$ costs at least $L(\lfloor M/2\rfloor) = E(\lfloor M/2\rfloor)$,
and Theorem 4.1 achieves $(E(T), 2T)$; both need only (S). $E$ is constant from $n\kappa$ on, so the finite set
$\{(E(T), 2T) : \kappa \le T \le n\kappa\} \subseteq \mathcal A$ dominates $\mathcal A$, and Lemma 1.1 gives
$\mathcal F$. For $\kappa < T \le n\kappa$, $\Phi(T) - \Phi(T-1)$ is $p$ when $T \le nq_0$ and $\rho$ when
$nq_0 < T \le n(q_0+1)$; the second range meets $[\kappa, n\kappa]$ only if $\rho \ge 1$. So for $\beta > 0$
every such $T$ is a breakpoint. $\square$

The count $(n-1)\kappa + 1$ matches the front sizes measured with the prototype on generator instances: 1,090
points for $n = 100$, $t = 60$, $p = 10$; 540 for $n = 50$ with the same $t$ and $p$; 399 for $n = 200$,
$t = 3$, $p = 2$. Neither link structures nor smoothing the free landings of a group are needed for this
family.

What the theorem does not cover:

* **Offset progressions.** For $d_i = a + bi$ with $a > 0$, $G[\cdot][T]$ need not be convex and $L < E$
  occurs. With $d = (5, 7, 9, 11)$, $c_i = 24 - 2d_i$, $t = 7$ and $p = 4$, $L(20) = 80 < E(20) = 84$ (by
  enumeration; 4 of 5,904 levels on 150 random offset instances). Contiguity from the step is essential: the
  two-city instance $d = (6, 10)$ of §5 is affine as well.
* **Conjecture 10.2.** The papers' per-PPP greedy reaches the front of Theorem 10.1. Evidence: equal fronts on
  115 instances with $n \le 6$, $p \le 5$ and $s \le 11$. Correctness does not depend on it, since the front
  is in closed form.
* The other generator families (logarithm, square root, $2^i$, $(5/2)i$) have no closed form; the general
  algorithm applies.

## 11. Evidence and how to reproduce it

All checks compare against exhaustive searches written independently of the solvers.

| Check | Result |
|---|---|
| Achievability construction (Thm 4.1) simulated with waiting, random admissible partitions | 19,323 / 19,323 makespan = largest load (971 with chains) |
| Characterisation vs brute force over schedules (multisets up to 10 landings, $p \le 5$) | 2,700 / 2,700 |
| Exact prototype (§7) vs search over all plans, symmetric, three central-flight regimes | 504 / 504 |
| $2t-p$ front vs all plans, symmetric (incl. 96 hub instances, shortest central flights) | 516 / 516 |
| $2t-p$ front vs all plans, non-symmetric, no useful central flights | 280 / 280 |
| same, shortest central flights | 129 / 140 (the 11 are shuttle triples) |
| Ignoring waiting, non-symmetric | 193 / 193 fronts unchanged |
| Golden fronts | 27 / 27 |
| Link-forest DP prototype vs enumeration | 600 instances, 25,919 levels, 0 mismatches |
| Link-forest DP (all tree sizes and $q \le q_{\max}$), σ-DP (with and without $w$), $U$ for $q_{\max} \le 2$, $U_3$ for $q_{\max} \le 3$, $L \le E \le U_3 \le U$, Prop 7.10(c), dominance, Pareto variant, each vs enumeration at every level | 9,000 instances ($n \le 5$, $s \le 10$; zero durations and costs, ties, duplicate cities, $p = 1$, $t = p$; 3,000 with anti-correlated costs), 348,682 levels, 0 mismatches. The bounds were loose on 306 levels ($L < E$) and 51 levels ($U > E$, all with $q_{\max} = 3$) |
| Parity matrices by brute force (Lemmas 2.4, 2.8) | 240,000 random partitions: a parity matrix exists iff the component form holds; every minimum-support matrix is a forest touching at most $\min(p-1, t-p)$ cities; every matrix touches at most $t-p$ |
| DS, SH, PAR (Lemmas 4.3–4.5) on random simple configurations | 166,697 / 166,697: count, balance, size $2t-p$, admissibility, sub-multiset, loads, non-symmetric role loads |
| Template closed form (Lemma 6.3) and its optimality over all interleavings; W1 (Cor 6.4) | 20,000 / 20,000 each |
| vs all plans (`truth`: $n \le 3$, $t \le 5$, $p \le 3$, 300 instances) | Cor 4.8: 600 / 600 (no or useless central flights); Thm 4.9: 600 / 600; Lemma 3.4: 900 / 900 (three regimes); Thm 4.1 points dominated by the true front: 900 / 900; shortest central flights: true front = $E$-front on 300 / 300 |
| Linear family closed form (Thm 10.1) vs link-forest DP | 336 instances, 5,844 levels; $L = U = E$ on 245 more instances (3,157 levels); offset progressions: $L < E$ on 4 of 5,904 levels |
| Papers' greedy on the linear family | 115 / 115 fronts equal |
| C++ solver (branch `feat/exact-front-solver`) | 27 / 27 golden fronts; every level of 300 random instances ($n \le 5$, $t \le 9$, $p \le 6$, $s \le 12$) equal to an independent enumeration oracle, the unrestricted-tree DP equal to the $q_{\max}$-restricted one |
| Harmful waiting (Prop 6.5), `checks/waiting_search.cpp`: exhaustive orders and matchings on random balanced configurations with a plane picking up twice and one dropping off twice, (AΔ-path) | Random crossing phases: 0 of 112,500 (p ≤ 4, ≤ 4 links, durations ≤ 12) and 0 of 192,270 (≤ 5 links, ≤ 15). One shortest crossing per plane: 6 of 189,964 (p ≤ 4, ≤ 5 links, ≤ 20), 5 of 190,040 (p ≤ 5, ≤ 6 links, ≤ 30), 1 of 71,538 (p ≤ 3, ≤ 6 links, ≤ 40) wait harmfully. On the instance of Prop 6.5 the bracket of `zeno` equals the oracle's front and leaves the two waiting gaps open |
| `relaxed` certificates (Lemma 3.4 alone) | 386 / 400 random fronts fully certified; 15 of 5,277 gaps (14 instances) need `forest` |

The exhaustive search over plans (`truth.cpp`) enforces that planes end in $C_G$ (`ANYWHERE=1` lifts this),
allows any flight, including central ones, and needs durations of at least 1. The programs and scripts are
in `doc/theory/checks` (`treedp.cpp`, `theorychecks.cpp` with `theorychecks_sweep.py` and
`theorychecks_anti.py`, `ds_check.py`, `ns_sched_check.py`, `truth.cpp` with `truth_checks.py`,
`linear_sweep.py`, `linear_closed_form.py`, `linear_greedy.py`, `achievability_check.py`); its README says
how to build and run them.

## 12. Next steps

1. Lean blueprint from this note, starting with the combinatorial core (Definition 2.2, Lemmas 2.3–2.9 and
   4.4–4.6, Theorems 7.5–7.6, Lemmas 9.2–9.3). Then plan semantics, Lemmas 3.1–3.4 and the `relaxed`
   checker, which already certifies 386 of 400 random fronts and the whole linear family without
   Theorem 4.7. Then Theorem 4.7.
2. Conjecture 4.10: search only where $L < E$; a proof needs simultaneous chain contraction for shared
   segments (§4.6).
3. Non-symmetric gaps left open by harmful waiting (Proposition 6.5): enumerate the balanced role
   configurations cheaper than the achieved point at the gap's level, each with its exact makespan by search
   over orders and matchings; the gap closes when none fits. This is only sound with a lemma that Theorem 6.1
   does not give: *schedulable domination*, every plan of cost $C$ and makespan $M$ is weakly dominated by a
   role configuration of cost $\le C$ whose template makespan (Lemma 6.3, best orders and matching) is at most
   $M$. Direct selection (Lemma 4.3) matches drop-offs to pick-ups by counts per city, not by the plan's own
   hand-offs, so its configuration need not inherit the plan's timing. Until the lemma is proved, such gaps
   stay open, as `zeno` reports them. (Former item: configuration-level search for
   Conjecture 6.5, $p \le 6$, several pick-ups
   per plane.
4. Conjecture 6.7: extend the exhaustive oracle with shuttle triples and compare on the 11 instances.
5. Conjecture 10.2, and the offset progressions.
6. Statement 1.2: differential tests against VAL on emitted PDDL plans.
7. Move the checkers of §11 into `tests/`.

## Appendix A. The normal-form proof of Theorem 4.7 (superseded)

The first version proved Theorem 4.7 by normalisation rules instead of Lemma 4.3. It is kept for reference,
with the corrections of the review; the main text does not depend on it. Assume (S) and (A1), and apply Steps
1 and 2 of Theorem 4.7, so that the plan is simple and clean. Use $o(\pi)$ and $n(\pi)$ from the proof of
Lemma 4.3, and record for each segment its type, its city $x(\gamma)$ and its duration
$F(\gamma) \ge 2d_{x(\gamma)}$. These data form a *configuration*. Only they are used from now on (no timing),
and every rewriting below keeps the cost and every $F_k$ from increasing.

**Normal form.** Apply the following rules while possible:

* N1: delete a $B$ segment that is no $o(\cdot)$.
* N2: delete a $\bar B$ segment that is no $n(\cdot)$.
* N3: if an $A$ segment is $o(\pi)$ with a hand-off but is no $n(\cdot)$, set $n(\pi) :=$ that segment.
* N4: if an $A$ segment is $n(\pi)$ with a hand-off but is no $o(\cdot)$, set $o(\pi) :=$ that segment.
* N5: if plane $k$ has a $B$ segment $\beta = o(\pi)$ and none of its $A$ segments is an $o$ or an $n$, delete
  $\beta$ and one $A$ segment, add an $A$ segment through $x(\beta)$ with duration $F(\beta)$, and set
  $o(\pi) = n(\pi) :=$ it. This needs (S): the crossing $d_x + \bar d_x$ must fit in the drop-off's $2d_x$.
* N6: the same as N5 with a $\bar B$ segment $= n(\pi)$, the new duration being $F(\bar\beta)$; this needs (S)
  too.

N1, N2, N5 and N6 lower the number of segments; N3 and N4 keep it and lower the number of hand-offs. So the
process terminates. Lemma 2.1 is preserved, $o$ and $n$ stay injective, and cost and budgets do not increase.
In normal form:

* every $B$ is the $o$ of a hand-off and every $\bar B$ the $n$ of a hand-off;
* every $A$ is *through* ($o(\pi) = n(\pi)$), a *swap* ($o$ of one hand-off and $n$ of another, at its city)
  or *empty*;
* every plane with a $B$ or $\bar B$ has at least one non-empty $A$.

**Selection.** Let $z_k$ be the number of non-empty $A$ segments of plane $k$. Plane $k$ is *active* if
$z_k \ge 1$; the others are *idle* (only empty $A$ and $\bar A$ segments). For an active plane, let $X_k$
consist of the cities of all its $B$, $\bar B$ and non-empty $A$ segments, plus $z_k - 1$ of its $\bar A$
segments (it has $\#A - 1 \ge z_k - 1$ of them). Then $|X_k| = \#B_k + \#\bar B_k + 2z_k - 1 \ge 1$,
$\ell(X_k) \le F_k \le M$, and $X_k$ is a sub-multiset of the plan's landings. Each passenger is carried out
by exactly one segment and delivered by exactly one, so $\sum_k (\#B_k + z_k) = \sum_k (\#\bar B_k + z_k) = t$,
and over the $q$ active planes $\sum_k |X_k| = 2t - q$.

**Admissibility.** Let $\Psi$ be the multigraph on active planes with one edge per hand-off, between the
planes of $o(\pi)$ and $n(\pi)$; a hand-off within one plane is a loop, counted twice in the degree. Then
$\deg_\Psi(k) = \#B_k + \#\bar B_k + 2\cdot\#\text{swaps}_k \equiv |X_k| + 1 \pmod 2$, so the even planes are
exactly the vertices of odd $\Psi$-degree. Both segments of a hand-off are selected, at the same city, so
$\Psi$-adjacent planes are connected in $H$. Each component of $H$ is therefore a union of components of
$\Psi$, each of which contains an even number of odd-degree vertices. By Lemma 2.4(a) the partition is
admissible.

**Idle planes.** Apply Lemma 4.6 once per idle plane, while $q < p \le t$. $\square$
