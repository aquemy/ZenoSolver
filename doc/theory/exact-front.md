# Exact Pareto fronts for MultiZenoTravel: proofs, algorithm, complexity

This note proves the exact Pareto front of MultiZenoTravel, the benchmark of Quemy & Schoenauer
(EvoCOP 2015) and of Quemy, Schoenauer & Dréo (arXiv:2304.14659, 2023), under the hypotheses each
result states. It specifies the exact algorithm and the certificates, and it refutes several claims of
the two papers. Every numbered result is meant to be proved in Lean 4 (`lean/`). Each one names the
declarations that prove it, and each written proof follows the route of its Lean proof. The model of
§1 is the one that Lean encodes.

The only goal is the exact Pareto front: weak dominance is enough throughout, and one plan per front
point is sufficient.

*Revision 3.* This revision keeps a result only if it lies on the proof path of a headline theorem of
§0, justifies a certificate kind or a step of the verified solver, or refutes a claim of the 2015 and
2023 papers. Every statement says exactly what its Lean proof gives. Remarks explain; they assert
nothing that a numbered result does not prove. The results are numbered consecutively, one counter per
section. The last section maps the numbers of revision 2 to the new ones and lists what was removed.

## 0. Status

| | Result | Hypotheses | Lean |
|---|---|---|---|
| H1, symmetric front | Theorem 4.5 | (S), (H), $p \le t$ | `minimal_achievable_iff_multisetPoints_hub`, `minimal_achievable_iff_admissiblePoints_hub`, `minimal_achievableAnywhere_iff_admissiblePoints_hub` |
| H2, verified solver | Theorem 6.9 | (S), (H), $1 \le p \le t$ | `solveFront_isParetoFront_hub` |
| H3, sound checkers | Theorems 8.2 and 8.7 | (H) for `forest` gaps (v1); (A1-NS) when listed (v2) | `Cert.check_sound_hub`, `Cert2.check_sound` |
| H4, non-symmetric front | Corollary 5.6 | (A1-NS), $p \le t$ | `minimal_achievable_iff_schedPoints`, `minimal_achievable_iff_configPoints` |

Every result of this note is meant to be machine-checked: Lean proves every assertion of its
statement, with no `sorry` and no axiom beyond `propext`, `Classical.choice` and `Quot.sound`
(`lean/scripts/CheckAxioms.lean`). Concrete examples are decided by the Lean kernel
(`decide +kernel`), never by `native_decide`. Declarations live in the namespace `ZenoFront`, in
`lean/ZenoFront/`. The names given here are those of the development once pull requests #83, #85, #86,
#88, #89 and #90 are merged. Each name exists in one of them.

* §1 Model: instances, plans, the rounding of rational and real times, the assumptions on central
  flights, fronts.
* §2 Admissible partitions: parity matrices, and their integer, disjoint and link-forest forms.
* §3 Counting and bounds: chains, counting, segment durations, the relaxation $L$ and two lower bounds.
* §4 Symmetric front: achievability, the converse under (S) and (H), the front (H1); an optimal plan
  with extra landings, why (H) is needed, and why the papers' greedies are not exact.
* §5 Non-symmetric front: role and scheduled configurations, schedulable domination, template plans,
  the front (H4); harmful waiting, and two constructions of arXiv:2304.14659 that miss the front.
* §6 Algorithm: the function $E$, the front as its breakpoints, the bracket, dominance, two exact
  dynamic programs, the verified solver (H2).
* §7 Complexity: two reductions to $M(X) \le 2T$ and the step count of the link-forest DP.
* §8 Certificates: formats v1 and v2 and their checkers (H3).

## 1. Model

### 1.1 Instances

**Definition 1.1 (instance).** An instance has two *hubs*, $C_I$ (initial) and $C_G$ (goal), and
central cities $1, \dots, n$. Durations are natural numbers. The flight between $C_I$ and $i$ lasts
$d_i$ in either direction, the flight between $i$ and $C_G$ lasts $\bar d_i$, and for every ordered
pair $(i, j)$ of central cities, $i = j$ included, the central flight from $i$ to $j$ lasts
$d_c(i, j)$. No flight joins the two hubs. $\mathrm{dur}(a, b)$ is the duration of the flight from $a$
to $b$. Landing in central city $i$ costs $c_i \in \mathbb N$; landing in a hub is free. There are
$p$ planes and $t$ passengers, all in $C_I$ at time 0. A plane carries at most one passenger. Results
assume $1 \le p \le t$ where they use it.

*Lean:* `Network`, `Network.duration` (Plan.lean). The costs $c$ and the numbers $t$ and $p$ are
separate arguments of every statement.

The table $d_c$ is complete and directed. An instance without central flights is therefore not an
instance of Definition 1.1: the results that need one quantify over the central tables that satisfy their
hypotheses (Proposition 5.7), or use the flight graphs of Definition 5.8 (Example 5.9).

### 1.2 Plans

**Definition 1.2 (plan).** A *leg* is a tuple (origin, destination, departure, arrival, passenger or
none), with natural-number times. A *plan* gives each plane a list of legs. A list of legs is a
*route from $x$ at time $\tau$* if its first leg leaves $x$ no earlier than $\tau$ and each later leg
leaves where the previous one arrived, no earlier than that arrival. The plan is *feasible* if

1. every leg is a flight: its origin and destination are joined by a flight, and its arrival is its
   departure plus the flight's duration;
2. the legs of each plane form a route from $C_I$ at time 0 whose last leg arrives in $C_G$;
3. for every passenger, the legs that carry it form, in some order, a route from $C_I$ at time 0 whose
   last leg arrives in $C_G$.

The *cost* $C$ of a plan is the sum of the landing costs of all its legs that land in a central city.
Its *makespan* $M$ is the latest end of a route, the arrival of its last leg. The *flight time* $F_k$
of plane $k$ is the sum of the durations of its legs. $\mathcal A$ is the set of points $(C, M)$ of
the feasible plans.

*Planes ending anywhere.* In this variant (PDDL problems without plane goals), item 2 only asks for a
route from $C_I$ at time 0, possibly empty; item 3 is unchanged. The makespan is the latest arrival of
a leg (0 for a plane without legs). $\mathcal A'$ is the set of points of the plans of the variant.

*Lean:* `Leg`, `Plan`, `Flies`, `IsRoute`, `PlaneFeasible`, `Feasible`, `planCost`, `planMakespan`
(Plan.lean); `durSum` (PlanBounds.lean); `achievable` (Checker.lean); `PlaneFeasibleAnywhere`,
`FeasibleAnywhere`, `achievableAnywhere` (Bridge.lean).

Waiting is implicit: a departure may be later than the preceding arrival, for planes and for
passengers. A leg names at most one passenger, which is the capacity constraint. Boarding and
debarking take no time, several planes may be in a city at once, and a passenger may change planes in
any city.

**Lemma 1.3 (rounding times).** Let $\mathbb K$ be an ordered ring with a floor function, such as
$\mathbb Q$ or $\mathbb R$, and let a plan have departures and arrivals in $\mathbb K$ (and the
instance's integer durations) and satisfy items 1–3 of Definition 1.2. Rounding every time down gives
a feasible plan with natural-number times, the same cost and a makespan at most the original one.
Conversely, a feasible plan with natural-number times, read in $\mathbb K$, satisfies items 1–3 with
the same cost and makespan.

*Lean:* `QFeasible`, `QFeasible.floor`, `qPlanCost_eq`, `planMakespan_floor_le`, `Feasible.toRat`
(RationalPlans.lean, for every `FloorRing` $\mathbb K$).

*Proof.* A leg with arrival $a = e + \tau$, $\tau \in \mathbb N$, has $\lfloor a\rfloor = \lfloor e
\rfloor + \tau$, so it stays a flight. Rounding down is monotone, so an inequality $a \le e'$ between
an arrival and the next departure survives it, for planes and for passengers, in the same orders, and
so does $0 \le e$ for the first departure. Locations and passengers do not change, so neither does the
cost, and $\lfloor x\rfloor \le x$ bounds the new makespan by the old one. The converse holds because
$\mathbb N \to \mathbb K$ preserves sums and order. $\square$

### 1.3 PDDL semantics

The domain file `pddl/multi-zeno-travel.pddl` (PDDL 2.1, level 3) has a durative action `fly`, lasting
`(timeTerre ?from ?to)`, whose only condition is that the plane is at `?from` at its start and which
adds `(citythreat ?to)` to `total-cost` at its end; instantaneous actions `board` and `debark`, with
the predicate `libre` for capacity one. The problem writer (`src/zeno/io.cpp`) gives `timeTerre` for
both directions of every hub flight ($d_i$ via $C_I$, $\bar d_i$ via $C_G$) and the instance's central
table for every ordered pair of distinct central cities, gives `citythreat` the landing costs, and writes
goals that put every person and every plane in $C_G$ and the metric that minimises `total-time` and
`total-cost`.

The model of §1.2 abstracts this domain: the `fly` actions of a plane are its legs, the flights a person
takes between a `board` and a `debark` carry it, and `libre` is the capacity constraint. The makespan of
§1.2 ignores the ε-separation of PDDL 2.1 between dependent actions; the header of the domain file states
this convention. Problem files without plane goals are read in the variant of planes ending anywhere.
This note proves nothing about PDDL plans themselves.

### 1.4 Assumptions

**Definition 1.4 (assumptions).** Each is used only where a result states it.

* (S) symmetry: $\bar d_i = d_i$ for all $i$.
* (A1) central flights are useless: $d_i + d_j \le d_c(i, j)$ for all central $i, j$. This is the
  EvoCOP 2015 assumption (stated there with $>$, under (S)).
* (A1-NS) $\min(d_i + d_j,\ \bar d_i + \bar d_j) \le d_c(i, j)$ for all central $i, j$.
* (AΔ) $\mathrm{dur}(a, b) \le \mathrm{dur}(a, x) + \mathrm{dur}(x, b)$ whenever $a \ne b$ and the
  three flights exist.
* (H) the hub triangles: $d_j \le d_i + d_c(i, j)$ and $d_i \le d_c(i, j) + d_j$ for all central $i, j$.

*Lean:* the hypothesis `N.dbar = N.d`; `Network.A1` (Converse.lean); `Network.A1NS`
(NonSymmetric.lean); `Network.ATri`, `Network.ATriHub` (TriSegments.lean).

(H) is (AΔ) on the triangles through $C_I$: $C_I \to i \to j$ against $C_I \to j$, and $i \to j \to
C_I$ against $i \to C_I$. Under (S) these are also the triangles through $C_G$. In (AΔ), the
condition $a \ne b$ leaves the flights $d_c(i, i)$ free.

**Lemma 1.5 (hub triangles).** (A1) implies (H), and (AΔ) implies (H).

*Lean:* `Network.A1.hub`, `Network.ATri.hub` (TriSegments.lean).

*Proof.* Under (A1), $d_j \le d_i + d_j \le d_i + d_c(i, j)$ and $d_i \le d_i + d_j \le d_c(i, j) +
d_j$. Under (AΔ), take $(a, x, b) = (C_I, i, j)$ and $(a, x, b) = (i, j, C_I)$; in both $a \ne b$ and
the three flights exist. $\square$

### 1.5 Fronts

**Definition 1.6 (fronts).** Points (cost, makespan) of $\mathbb N^2$ are ordered componentwise, and
$y$ *weakly dominates* $z$ if $y \le z$. For $\mathcal S \subseteq \mathbb N^2$, $\mathrm{Min}\,\mathcal
S$ is the set of the minimal points of $\mathcal S$: the $z \in \mathcal S$ such that every $y \in
\mathcal S$ with $y \le z$ is $z$. The *front* is $\mathcal F = \mathrm{Min}\,\mathcal A$. A list is the
*Pareto front* of $\mathcal S$ if its points lie in $\mathcal S$, every point of $\mathcal S$ is weakly
dominated by a listed point, and the listed points are pairwise incomparable.

*Lean:* `achievable`, `IsParetoFront` (Checker.lean); `achievableAnywhere` (Bridge.lean); Mathlib's
`Minimal`.

**Lemma 1.7 (dominating sets).** (a) If every point of $\mathcal A$ is weakly dominated by a point of
$\mathcal B$ and every point of $\mathcal B$ by a point of $\mathcal A$, then $\mathrm{Min}\,\mathcal A =
\mathrm{Min}\,\mathcal B$; in particular when $\mathcal B \subseteq \mathcal A$ and every point of
$\mathcal A$ is weakly dominated by a point of $\mathcal B$. (b) A list that is the Pareto front of
$\mathcal S$ lists exactly the points of $\mathrm{Min}\,\mathcal S$.

*Lean:* `minimal_iff_of_dominated` (Achievability.lean); `minimal_iff_of_subset_of_dominated`
(Bridge.lean); `IsParetoFront.mem_iff_minimal` (Checker.lean).

*Proof.* (a) Let $z \in \mathrm{Min}\,\mathcal A$. Some $b \in \mathcal B$ has $b \le z$, and some $a
\in \mathcal A$ has $a \le b$; then $a = z$, so $b = z \in \mathcal B$. If $y \in \mathcal B$ and $y
\le z$, some $a' \in \mathcal A$ has $a' \le y \le z$, so $a' = z$ and $y = z$. Hence $z \in
\mathrm{Min}\,\mathcal B$, and the other inclusion is symmetric. If $\mathcal B \subseteq \mathcal A$,
every point of $\mathcal B$ is dominated by itself in $\mathcal A$. (b) A listed point $x$ lies in
$\mathcal S$; if $y \in \mathcal S$ and $y \le x$, a listed $x' \le y \le x$ exists, so $x' = x$ by
incomparability, and $y = x$. Conversely, for $z \in \mathrm{Min}\,\mathcal S$ some listed $x \le z$ lies
in $\mathcal S$, so $x = z$. $\square$

**Notation.** $s = 2t - p$. For multisets of central cities: $Y(i)$ is the multiplicity of $i$, $|Y|$
the size, $\mathrm{supp}\,Y$ the support, $Y + Z$ the sum and $Z \le Y$ inclusion; $c(Y) = \sum_{w \in
Y} c_w$, $\delta(Y) = \sum_{w\in Y} d_w$, $\bar\delta(Y) = \sum_{w \in Y} \bar d_w$, and with $e_i =
\min(d_i, \bar d_i)$, $e(Y) = \sum_{w \in Y} e_w$. A *partition* of $X$ over the $p$ planes is a
family $X_1, \dots, X_p$ of groups, possibly empty, with $\sum_k X_k = X$; its *loads* are the
$\delta(X_k)$. For a weight $w$ on the cities, $G_w[m][T]$ is the least $c(Y)$ over the multisets $Y$
with $|Y| = m$ and $w(Y) \le T$ ($\infty$ if there is none), and $G = G_d$. $d_{\min}$, $d_{\max}$ and
$c_{\min}$ are the least and largest durations and the least cost.

## 2. Admissible partitions

**Definition 2.1 (admissible partition).** Let $X_1, \dots, X_p$ be a partition of $X$. A *parity
matrix* for it gives every plane $k$ a set $\eta_k$ of central cities such that

* (h1) $\eta_k \subseteq \mathrm{supp}\,X_k$;
* (h2) $|\eta_k| \equiv |X_k| + 1 \pmod 2$;
* (h3) every city lies in an even number of the sets $\eta_k$.

The partition is *admissible* if it has a parity matrix. The matrix *touches* the cities of $Z(\eta) =
\bigcup_k \eta_k$, and its *entries* are the pairs $(k, i)$ with $i \in \eta_k$.

*Lean:* `IsParityWitness`, `Admissible` (Admissible.lean).

In graph terms, the entries of a parity matrix form a $\mathcal T$-join of the bipartite graph joining
plane $k$ to city $i$ when $i \in X_k$, for the set $\mathcal T$ of planes with $|X_k|$ even.

**Lemma 2.2 (integer form).** A partition is admissible iff some $\tilde h \in \mathbb N^{p \times n}$
has $\tilde h_{k,i} \le X_k(i)$ for all $k, i$, $\sum_i \tilde h_{k,i} \equiv |X_k| + 1 \pmod 2$ for every
plane $k$, and $\sum_k \tilde h_{k,i}$ even for every city $i$.

*Lean:* `admissible_iff_exists_natWitness`, `card_filter_odd_mod_two` (Admissible.lean).

*Proof.* The indicator matrix of a parity matrix is such an $\tilde h$, by (h1). Conversely, let
$\eta_k = \{i : \tilde h_{k,i} \text{ odd}\}$. An odd $\tilde h_{k,i}$ is at least 1, so $X_k(i) \ge
1$: (h1). $|\eta_k| \equiv \sum_i \tilde h_{k,i}$ gives (h2), and $\#\{k : i \in \eta_k\} \equiv
\sum_k \tilde h_{k,i}$ gives (h3). $\square$

**Lemma 2.3 (disjoint groups).** If no city lies in two groups, the partition is admissible iff every
group has odd size.

*Lean:* `admissible_iff_odd_of_disjoint` (Complexity.lean).

*Proof.* If every $|X_k|$ is odd, the empty sets $\eta_k = \emptyset$ form a parity matrix. Conversely,
take a parity matrix. A city lies in at most one group, hence by (h1) in at most one $\eta_k$, hence by
(h3) in none. So every $\eta_k$ is empty, and (h2) makes $|X_k|$ odd. $\square$

**Lemma 2.4 (row bound).** For every parity matrix and plane $k$, $|\eta_k| + 1 \le |X_k|$. Hence the
groups of an admissible partition are non-empty, and $|X| \equiv p \pmod 2$.

*Lean:* `IsParityWitness.card_add_one_le`, `Admissible.card_pos` (Admissible.lean);
`IsParityWitness.size_mod_two` (Shrink.lean).

*Proof.* $|\eta_k| \le |\mathrm{supp}\,X_k| \le |X_k|$ by (h1), and $|\eta_k| \ne |X_k|$ by (h2). By
(h2), $|X| = \sum_k |X_k| \equiv \sum_k |\eta_k| + p$, and $\sum_k |\eta_k| = \sum_i \#\{k : i \in
\eta_k\}$ is even by (h3). $\square$

**Definition 2.5 (link forest).** A *rooted link tree* is a plane with a multiset of *free landings*
and a list of *children*, each a rooted link tree hung from the plane by a *link* labelled with a
central city. The group of a plane consists of its free landings, one copy of the label of each of its
child links, and one copy of the label of its parent link (none for a root). (F2): every plane has an
odd number of free landings. A *link forest* of a partition is a list of rooted link trees satisfying
(F2) whose groups are the groups of the partition, up to relabelling the planes.

*Lean:* `LTree`, `LKids`, `LTree.groups`, `LTree.WF`, `forestGroups` (LinkForest.lean).

Each link uses one copy of its label in each of the two groups it joins, so the links at a plane use
distinct landings of its group by construction.

**Lemma 2.6 (link forests).** A partition is admissible iff it has a link forest.

*Lean:* `admissible_iff_exists_linkForest`, `admissible_forestPartition`, `linkWitness`
(TreeExact.lean); `Admissible.exists_linkForest`, `IsParityWitness.exists_card_eq_one_of_minimal`,
`attachForest` (LinkForest.lean); `Admissible.exists_minimal`, `IsParityWitness.exists_edgeCount_lt`
(MinimalWitness.lean).

*Proof.* (If.) Let $\eta_u$ be the set of cities that label an odd number of links at plane $u$ (child
and parent links together). Such a city labels a link at $u$, whose copy lies in $X_u$: (h1). The links
at $u$ number $|X_u|$ minus the free landings of $u$, which is $\equiv |X_u| + 1$ by (F2), and $|\eta_u|$
has the parity of that number: (h2). Every link counts at both its planes, so for every city the
numbers of links at the planes sum to an even number: (h3).

(Only if.) By induction on the number of planes; with none, the empty list works. Let $\eta$ be a
parity matrix with the fewest entries.

*A minimal matrix has no cycle.* View each entry $(k, i)$ as the vector $e_k + e_i$ over $\mathbb Z/2$,
indexed by the planes and the touched cities. If these vectors were linearly dependent, a non-empty set
of entries would meet every plane and every city an even number of times; deleting it would keep
(h1)–(h3) with fewer entries. So they are independent. They lie in the hyperplane of vectors whose
coordinates sum to 0, which does not contain the unit vector of a plane, so
$\#\text{entries} + 1 \le p + |Z(\eta)|$. By (h3) every touched city carries at least two entries, so
$2|Z(\eta)| \le \#\text{entries}$.

*Removing a leaf.* If some $\eta_u = \emptyset$, then $|X_u|$ is odd by (h2). The other planes, with the
same sets $\eta_k$, are admissible; by induction they have a link forest, and $u$ is added as a tree of
its own, with free landings $X_u$. Otherwise some $|\eta_u| = 1$: if every $|\eta_k| \ge 2$, then
$\#\text{entries} \ge 2p$, while the two inequalities above give $\#\text{entries} \le 2p - 2$. Let
$\eta_u = \{i\}$. By (h3) another plane $v$ has $i \in \eta_v$. Remove plane $u$, and remove one copy
of $i$ from $X_v$ and from $\eta_v$. This is a parity matrix of the smaller partition: (h1) holds for
the other cities of $\eta_v$, the size and the row of $v$ both drop by one, and the column of $i$ drops
by two. By induction the smaller partition has a link forest. Hang $u$, with free landings $X_u - \{i\}$,
from the plane whose group is $X_v - \{i\}$, by a link labelled $i$. That plane's group becomes $X_v$, the
group of $u$ is $X_u$, and $|X_u| - 1$ is odd because $|\eta_u| = 1$ and (h2) make $|X_u|$ even.
$\square$

**Lemma 2.7 (few touched cities).** Let $1 \le p \le t$. An admissible partition with $|X| = s$ has a
parity matrix that touches at most $\min(p - 1,\ t - p)$ cities.

*Lean:* `Admissible.exists_card_touched_le`, `IsParityWitness.card_touched_le_of_minimal`
(MinimalWitness.lean); `IsParityWitness.card_touched_le`, `IsParityWitness.edgeCount_le`
(SupportBound.lean).

*Proof.* Take a parity matrix with the fewest entries. By the two inequalities of the proof of Lemma
2.6, $|Z(\eta)| + 1 \le p$. By Lemma 2.4, $\#\text{entries} = \sum_k |\eta_k| \le \sum_k (|X_k| - 1) = s
- p = 2(t - p)$, and $2|Z(\eta)| \le \#\text{entries}$ gives $|Z(\eta)| \le t - p$. $\square$

## 3. Counting and bounds

*Segments.* The *segments* of a route are its parts between consecutive arrivals in a hub, the first
starting at the route's start, so a route that ends in a hub has one segment per hub arrival. By its end
hubs a segment has type $A$ ($C_I$ to $C_G$), $\bar A$ ($C_G$ to $C_I$), $B$ ($C_I$ to $C_I$) or $\bar B$
($C_G$ to $C_G$). On a route without central flights, every segment is a *visit*: a leg into a central
city $x$ followed by the next leg, out of $x$ into a hub. A visit at $x$ is a crossing ($A$ or $\bar A$),
a drop-off ($B$) or a pick-up ($\bar B$), and its *role weight* is $d_x + \bar d_x$, $2d_x$ or $2\bar d_x$
respectively.

*Lean:* `hubArrivals` (PlanBounds.lean); `Visit`, `KLeg` (Visits.lean); `Visit.isA`, `Visit.isAbar`,
`Visit.w` (SchedBuild.lean); `Visit.isB` (DominationAll.lean).

**Lemma 3.1 (crossings outnumber returns).** On a route from $C_I$ to $C_G$ without central flights, the
visits of type $A$ number one more than those of type $\bar A$. On a closed walk of visits, from a hub
back to it, they are equally many.

*Lean:* `TChain.countP_isA`, `TRoute.countP_isA`, `TLoop.countP_isA` (Rewire.lean).

*Proof.* Along a sequence of visits from a hub, $\#A + [\text{it ends in } C_I] = \#\bar A + [\text{it
starts in } C_I]$, by induction on the visits: a visit of type $A$ moves the walk from $C_I$ to $C_G$,
one of type $\bar A$ back, and the others keep its hub. $\square$

**Lemma 3.2 (chains).** (a) In a feasible plan, and in a plan whose planes end anywhere, every passenger
rides a *chain*: legs of the plan that carry it, the first leaving $C_I$, each later one leaving where
the previous one arrived and no earlier, all landing in central cities except the last, which arrives in
$C_G$. (b) If the plan has no central flight, every passenger rides a leg $C_I \to x$ and then a leg $x
\to C_G$ that leaves no earlier than the first one arrives.

*Lean:* `ToGoal`, `exists_chain`, `Feasible.exists_chains` (ConverseTri.lean);
`FeasibleAnywhere.exists_chains`, `ToGoal.dst_ne_ci` (Bridge.lean); `exists_transfer_pw`
(DominationAll.lean).

*Proof.* (a) By item 3 of Definition 1.2, which the variant keeps, the legs carrying the passenger form
a route from $C_I$ that ends in $C_G$. It leaves $C_I$ at least once. Take its last departure from $C_I$
and the legs after it up to the first arrival in $C_G$. None of them arrives in $C_I$, since the route
would then leave $C_I$ again, so all but the last land in central cities. (b) Without central flights,
the leg after the first leg $C_I \to x$ of the chain of (a) leaves $x$ for a hub, which by (a) is
$C_G$. $\square$

**Lemma 3.3 (counting).** In a feasible plan, $2t \le \sum_k h_k + p$, where $h_k$ is the number of hub
arrivals (segments) of plane $k$.

*Lean:* `ciDepartures_add_cgArrivals`, `PlaneFeasible.ciDepartures_add_cgArrivals`,
`Feasible.le_ciDepartures`, `Feasible.le_cgArrivals`, `Feasible.le_sum_hubArrivals` (PlanBounds.lean).

*Proof.* Along a route from $x$, $\#\{\text{departures from } C_I\} + \#\{\text{arrivals in } C_G\} +
[\text{it ends in } C_I] = \#\{\text{hub arrivals}\} + [x = C_I]$, by induction on the legs: a leg from
$a$ to $b$ adds $[a = C_I] + [b = C_G]$ to the left side and changes the indicator by $[b = C_I] - [a =
C_I]$, a total of $[b \text{ is a hub}]$. For a feasible plane this reads $\#\text{dep}_{C_I} +
\#\text{arr}_{C_G} = h_k + 1$. The route of each passenger starts with a departure from $C_I$ and ends
with an arrival in $C_G$, and a leg carries one passenger, so the plan has at least $t$ departures from
$C_I$ and at least $t$ arrivals in $C_G$. Summing over the planes, $2t \le \sum_k (h_k + 1)$. $\square$

**Lemma 3.4 (segment durations).** (a) A feasible plane has a multiset $Z$ of central cities with $|Z|$
equal to its number of hub arrivals, $2e(Z)$ at most its end time, and $c(Z)$ at most its landing cost.

(b) Assume (S) and (H). The route of a feasible plane is the concatenation of its segments, one per hub
arrival; each lands in at least one central city and flies at least $2d_y$ for every central city $y$ it
lands in. A chain (Lemma 3.2(a)) ends at least $d_y$ after any of its legs arrives in a central city
$y$.

(c) On a route without central flights, every visit lasts its role weight, and the visits of a route
from a hub whose legs all arrive by $M$ last at most $M$ in total.

*Lean:* (a) `PlaneFeasible.exists_segments_emin` (PlanBounds.lean); (b) `segment_bound`,
`PlaneFeasible.exists_segments_tri` (TriSegments.lean), `ToGoal.add_d_le_endTime`, `ToGoal.arr_add_d_le`
(Bridge.lean); (c) `Node.w_eq` (SchedBuild.lean), `TChain.sum_w_le` (Rewire.lean).

*Proof.* (a) No flight joins the hubs, so a segment starts with a leg from a hub into a central city $a$
and ends with a leg from a central city $b$ into a hub. These last at least $e_a$ and $e_b$, so the
segment flies at least $e_a + e_b \ge 2\min(e_a, e_b)$. Put into $Z$ the one of $a, b$ with the smaller
$e$, one per segment. Different segments have different legs, so these are distinct landings of the
plane, and $c(Z)$ is at most its landing cost. The legs follow one another from time 0, so their
durations sum to at most the end time.

(b) Cut the route after every hub arrival. Along a segment from a hub, let $w$ be the current central
city. The part flown so far lasts at least $d_w$, and adding $d_w$ to it gives at least $2d_x$ for every
central city $x$ visited so far. Both hold after the first leg, which lasts $d_w$ under (S). A central
leg from $i$ to $j$ keeps them: the first since $d_j \le d_i + d_c(i, j)$, the second since $d_i \le
d_c(i, j) + d_j$, by (H). The last leg, from $w$ to a hub, lasts $d_w$ under (S). For the chain, by
induction from its end: its last leg, from $y$ to $C_G$, lasts $\bar d_y = d_y$; a central leg from $y$ to
$y'$ followed by a part lasting at least $d_{y'}$ lasts at least $d_c(y, y') + d_{y'} \ge d_y$, by (H).
Every leg of the chain departs no earlier than the previous one arrives.

(c) A visit at $x$ flies a hub leg into $x$, of duration $d_x$ from $C_I$ and $\bar d_x$ from $C_G$, and
one out of $x$, of duration $d_x$ to $C_I$ and $\bar d_x$ to $C_G$. The legs of a route follow one
another, so their durations sum to at most the last arrival. $\square$

**Lemma 3.5 (relaxation).** Let $p \le t$. Every feasible plan with cost $C$ and makespan $M$ has
non-empty multisets $Y_1, \dots, Y_p$ with $\sum_k |Y_k| = s$, $c(Y_1 + \dots + Y_p) \le C$ and
$2e(Y_k) \le M$ for every $k$; under (S), $e = d$. Hence $C \ge L_e(\lfloor M/2\rfloor)$, where
$L_e(T)$ is the least $\sum_k G_e[m_k][T]$ over $m_1, \dots, m_p \ge 1$ with $\sum_k m_k = s$ ($\infty$ if
none). Nothing is assumed on central flights.

*Lean:* `Network.emin`, `Network.emin_eq_of_sym`, `exists_trim`, `Feasible.exists_relaxation_emin`,
`Feasible.exists_relaxation` (PlanBounds.lean); `relaxCost`, `relaxCost_oneplane_le_totalCost`,
`Feasible.relaxCost_le_planCost` (Relaxation.lean).

*Proof.* Lemma 3.4(a) gives each plane $k$ a multiset $Z_k$ with $|Z_k| = h_k \ge 1$ (a feasible plane
ends in $C_G$), $2e(Z_k)$ at most its end time, hence at most $M$, and $c(Z_k)$ at most its landing
cost. By Lemma 3.3, $\sum_k |Z_k| \ge s \ge p$. Remove landings from groups with at least two until
$s$ remain; the groups $Y_k \le Z_k$ stay non-empty, $2e(Y_k) \le M$, and $\sum_k c(Y_k) \le \sum_k
c(Z_k) \le C$. The integer $e(Y_k)$ is at most $\lfloor M/2\rfloor$, so $c(Y_k) \ge G_e[|Y_k|][\lfloor
M/2\rfloor]$, and the sizes $|Y_k|$ are among those $L_e$ minimises over. $\square$

**Proposition 3.6 (lower bounds).** Let $p \le t$. Every feasible plan costs at least $s\,c_{\min}$.
Under (S) and $1 \le p$, every feasible plan has makespan at least $2d_{\min}\lceil s/p\rceil$.

*Lean:* `minOf`, `exists_ceil_le_card`, `Feasible.minOf_le_cost_emin`, `Feasible.minOf_le_cost`,
`Feasible.minOf_le_makespan` (Checker.lean).

*Proof.* The groups of Lemma 3.5 have $s$ landings in all, each costing at least $c_{\min}$. Under
(S), some $Y_k$ has at least $\lceil s/p\rceil$ landings, each of duration at least $d_{\min}$, and
$2\delta(Y_k) \le M$. $\square$

## 4. Symmetric front

**Theorem 4.1 (achievability).** Assume (S) and $p \le t$. For every central table, every admissible
partition $X_1, \dots, X_p$ with $|X| = 2t - p$ is flown by a feasible plan whose planes land exactly at
the groups (up to relabelling the planes), of cost $c(X)$ and makespan $2\max_k \delta(X_k)$.

*Lean:* `Admissible.exists_plan`, `admissiblePoints_subset_achievable` (Achievability.lean).

*Proof.* Take a link forest (Lemma 2.6) and label the planes by its trees. A link at $i$ from a parent
$u$ to a child $v$ will carry a passenger: $u$ drops it in $i$ (a visit $B$), and $v$ picks it up (a
visit $\bar B$). Every plane $k$ flies, from time 0:

1. its drop-offs, one per child link: $C_I \to b \to C_I$, carrying a new passenger from $C_I$ and
   leaving it in $b$;
2. its free landings, an odd number by (F2), as crossings $A, \bar A, \dots, A$: each $A$ carries a new
   passenger from $C_I$ to $C_G$, each $\bar A$ flies empty;
3. if it has a parent link at $i$: $C_G \to i \to C_G$, leaving $i$ once the passenger dropped there
   by its parent has arrived, and carrying it to $C_G$.

Every leg departs as soon as the plane arrives, except the last leg of a pick-up. Under (S) every visit
at $x$ lasts $2d_x$ (Lemma 3.4(c)), so plane $k$ flies exactly $2\delta(X_k)$. Plane $u$'s drop-off at
$i$ reaches $i$ by $2\delta(X_u) - d_i$, since it comes before $u$'s crossings. Its child $v$ reaches
$C_G$ after its drop-offs and crossings, at $2\delta(X_v) - 2d_i$, and $i$ at $2\delta(X_v) - d_i$; it
leaves $i$ at the later of that time and the drop-off's arrival, and is back by $\max(2\delta(X_v),
2\delta(X_u))$. So every plane ends by $2\max_k \delta(X_k)$, and the plane of largest load ends exactly
then.

*Passengers.* Let the forest have $N$ links. The free landings number $s - 2N$, and each plane makes one
more $A$ than $\bar A$, so there are $(s - 2N + p)/2 = t - N$ crossings $A$. These and the $N$
drop-offs carry $t$ distinct passengers out of $C_I$, each delivered to $C_G$ by its $A$ or by the
pick-up linked to its drop-off, which leaves no earlier than the drop-off arrives. The plan flies no
central flight, every route ends in $C_G$, and the central landings of plane $k$ are its group. $\square$

**Lemma 4.2 (adding a plane).** An admissible partition of $q$ planes with $2t - q$ landings, $t \ge q +
1$, gives an admissible partition of $q + 1$ planes with $2t - q - 1$ landings, no larger cost, and
loads bounded by every bound on the old loads. Repeating, it gives one of $p$ planes for every $q \le p
\le t$.

*Lean:* `Admissible.addPlane`, `Admissible.addPlane_of_size`, `Admissible.addPlanes` (AddPlane.lean);
`Admissible.addPlanes_le` (Bridge.lean).

*Proof.* Here $|X| = 2t - q \ge q + 2$. Fix a parity matrix. By Lemma 2.4, $f_k := |X_k| - |\eta_k|$
is odd and at least 1. Call *free* the $f_k$ copies in $X_k$ beyond one copy of each city of $\eta_k$.

*Some $f_k \ge 3$.* Remove two free landings $y, y'$ from $X_k$ and give the new plane the group $\{y\}$
with $\eta = \emptyset$. (h1)–(h3) still hold, $|X_k| - 2 \ge |\eta_k| + 1$, $d_y \le \delta(X_k)$, and
the cost drops by $c_{y'}$.

*Every $f_k = 1$.* Then $\sum_k |\eta_k| = |X| - q \ge 2$, so some city $i$ lies in $\eta_u$ and $\eta_v$
for planes $u \ne v$, by (h3). Remove one copy of $i$ from $X_u$ and from $X_v$ and remove $i$ from
$\eta_u$ and $\eta_v$, and give the new plane $\{i\}$ with $\eta = \emptyset$. The rows and the sizes of
$u$ and $v$ drop by one, the column of $i$ by two, $d_i \le \delta(X_u)$, and the cost drops by $c_i$.
$\square$

**Lemma 4.3 (shrinking).** If $X$ is admissible with at least $s$ landings, $p \le s$ and $s \equiv p
\pmod 2$, some admissible $Y$ with $Y_k \le X_k$ for every $k$ has exactly $s$ landings. In particular two
landings can be removed when $|X| \ge p + 2$.

*Lean:* `Admissible.exists_shrink`, `IsParityWitness.exists_shrink_step` (Shrink.lean);
`Admissible.exists_remove_two` (TriSegments.lean).

*Proof.* By Lemma 2.4, $|X| \equiv p \equiv s$. While $|X| > s$, so $|X| \ge p + 2$, remove two
landings as in the two cases of the proof of Lemma 4.2, without creating a plane: two free landings of
a plane with $f_k \ge 3$, or one copy of a city $i$ from two planes whose sets $\eta$ contain it. Both
keep a parity matrix. $\square$

**Theorem 4.4 (converse under (S) and (H)).** Assume (S), (H) and $p \le t$. If every plane flies a
route from $C_I$ at time 0 to $C_G$ (items 1 and 2 of Definition 1.2) and every passenger rides a chain
(Lemma 3.2(a)) of legs of the plan, then some admissible partition $X_1, \dots, X_p$ has $|X| = 2t - p$,
$c(X)$ at most the plan's cost and $2\delta(X_k) \le F_k$ for every plane. In particular every feasible
plan of makespan $M$ gives such a partition, with $2\delta(X_k) \le F_k \le M$.

*Lean:* `exists_admissible_of_chains`, `exists_merge`, `PlaneFeasible.durSum_le_planMakespan`,
`Feasible.exists_admissible_hub` (ConverseTri.lean); `TriCore.exists_tjoin`, `TriCore.exists_init`,
`TriCore.Inv.step`, `TriCore.Inv.exists_final`, `TriCore.exists_selection`, `exists_admissible_of_blocks`
(TriCore.lean). Corollaries: `Feasible.exists_admissible_ATri` under (AΔ) and
`Feasible.exists_admissible_A1_flightTime` under (A1) (ConverseTri.lean).

*Proof.* By Lemma 3.4(b), the route of plane $k$ is the concatenation of its $\sigma_k \ge 1$ segments,
each landing at least once and flying at least $2d_x$ for each central city $x$ it lands in. A *block*
will be a segment, or two segments of one plane merged; $R(\gamma)$ is the largest $d_x$ over the
landings $x$ of block $\gamma$, and $\gamma$ flies at least $2R(\gamma)$. Fix in every block a landing
$z(\gamma)$ in a city of duration $R(\gamma)$.

*Step 1: classes and merges.* Two planes *share* if they land in a common central city; the *classes*
are the classes of the equivalence relation this generates. Assign every passenger to the plane of the
first leg of its chain. The chain stays in the class of that plane: two consecutive legs of the chain
meet in a central city $y$, the plane of the first lands in $y$, and the plane of the second leaves $y$,
so its route, which starts in $C_I$, has landed in $y$ before. Let a class $K$ have $q_K$ planes,
$\sigma_K$ segments and $t_K$ passengers. The first legs of their chains are distinct departures from
$C_I$ of planes of $K$, and their last legs distinct arrivals in $C_G$ of planes of $K$. By the identity
of the proof of Lemma 3.3, a plane has $\sigma_k + 1$ such departures and arrivals in all, so $2t_K \le
\sigma_K + q_K$. In every class with $\sigma_K + q_K$ odd, some plane has $\sigma_k \ge 2$ (otherwise
$\sigma_K + q_K = 2q_K$): merge two of its segments into one block. Let $m_k \ge 1$ be the number of
blocks of plane $k$. In every class, $m_K + q_K$ is now even, and so is the number of planes of $K$ with
$m_k$ even, which has the parity of $\sum_{k \in K} (m_k + 1)$. A class loses a block only if $\sigma_K
+ q_K \ge 2t_K + 1$, so $\sum_k m_k + p \ge 2t$.

*Step 2: ends from a $\mathcal T$-join.* Let $\mathcal T$ be the set of planes with an even number of
blocks; every class contains an even number of them. Pair them up within each class, and join each pair
by a path: a sequence of planes from one to the other, consecutive ones landing in a common city, with
one landing of each taken at that city. Add up these paths over $\mathbb Z/2$: the landings taken an odd
number of times form a set $J$ in which every plane of $\mathcal T$ has an odd number of landings, every
other plane an even number, and every city an even number. Each landing of $J$ *pays an end* of its own
block, at its city. These ends satisfy the invariant:

* (i) every end of a block $\gamma$ is at a city of duration at most $R(\gamma)$;
* (ii) every city has an even number of ends;
* (iii) a plane has an odd number of ends iff it has an even number of blocks;
* (iv) no landing $z(\gamma)$ pays an end of a block other than $\gamma$.

*Step 3: re-pairing.* While some block $\gamma$ has two ends, choose two of them, $e_1$ and $e_2$, with
$e_1 \ne z(\gamma)$ and $d(e_1) \le d(e_2)$ (if one of them is $z(\gamma)$, it is $e_2$, and (i) gives
the inequality). By (ii) the city of $e_2$ has another end $e_3$, of a block $\gamma_3$. If $\gamma_3 =
\gamma$, delete the ends $e_2$ and $e_3$. Otherwise delete $e_2$ and $e_3$, and let $e_1$ pay an end of
$\gamma_3$ instead of $\gamma$, at its own city. (i) holds, as $d(e_1) \le d(e_2) = d(e_3) \le
R(\gamma_3)$. (ii) holds: the city of $e_2$ loses two ends, the city of $e_1$ none. (iii) holds: the
plane of $\gamma$ loses two ends and the plane of $\gamma_3$ trades $e_3$ for $e_1$ (or, if it is the
same plane, loses two). (iv) holds: if $e_1 = z(\gamma')$, then $\gamma' = \gamma$ by (iv), which the
choice of $e_1$ excludes. Each step removes two ends, so eventually every block has at most one end.

*Step 4: selection.* A block with an end takes the city of its end and the end's landing; a block
without one takes the city of $z(\gamma)$ and $z(\gamma)$ itself. These landings are distinct: a
landing pays at most one end, different blocks have different landings, and by (iv) a $z(\gamma)$ taken
by $\gamma$ pays no end of another block. Plane
$k$'s group $X_k$ consists of the cities taken by its blocks, so $|X_k| = m_k$. By (i), $\delta(X_k)
\le \sum_\gamma R(\gamma)$ over the blocks of $k$, hence $2\delta(X_k) \le F_k$. The taken landings are
distinct central landings of the plan, so $c(X)$ is at most its cost. Let $\tilde h_{k,y}$ be the number
of ends of plane $k$ at city $y$. Each such end is the end of a block of $k$ that takes $y$, so $\tilde
h_{k,y} \le X_k(y)$; $\sum_y \tilde h_{k,y} \equiv |X_k| + 1$ by (iii); and $\sum_k \tilde h_{k,y}$ is
even by (ii). By Lemma 2.2 the partition is admissible.

*Step 5: size.* $|X| = \sum_k m_k \ge 2t - p$, and $|X| \equiv p$ by Lemma 2.4. Lemma 4.3 removes
landings down to exactly $2t - p$; the groups shrink, so the cost and load bounds remain. In a feasible
plan, the legs of plane $k$ follow one another from time 0 and end by $M$, so $F_k \le M$. $\square$

By Lemma 1.5 the converse holds under (A1) and under (AΔ). The proof uses no timing: only the
segments, their landings and which planes share which cities.

**Theorem 4.5 (symmetric front, H1).** Assume (S), (H) and $p \le t$. Let $\mathcal P$ be the set of the
points $(c(X), 2\max_k \delta(X_k))$ of the admissible partitions $X$ with $|X| = 2t - p$. For a multiset
$X$, let $M(X)$ be the least $2\max_k \delta(X_k)$ over the admissible partitions of $X$ into $p$ groups
(0 if there is none), and let $\mathcal X$ be the set of the points $(c(X), M(X))$ of the multisets of
$2t - p$ landings that have an admissible partition. Then
$$\mathcal F = \mathrm{Min}\,\mathcal A' = \mathrm{Min}\,\mathcal P = \mathrm{Min}\,\mathcal X.$$

*Lean:* `admissiblePoints`, `multisetPoints`, `minMakespan`, `admissiblePoint_le`,
`minimal_achievable_iff_admissiblePoints_hub`, `minimal_achievableAnywhere_iff_admissiblePoints_hub`,
`minimal_admissiblePoints_iff_multisetPoints`, `minimal_achievable_iff_multisetPoints_hub`,
`FeasibleAnywhere.exists_feasible_le_hub`, `minimal_achievable_iff_anywhere_hub` (Achievability.lean); `FeasibleAnywhere.exists_admissible_hub`,
`cutTri`, `closeTri` (Bridge.lean). Corollaries under (A1) and (AΔ):
`minimal_achievable_iff_multisetPoints`, `minimal_achievable_iff_multisetPoints_ATri`,
`minimal_achievable_iff_anywhere_of_A1`, `minimal_achievable_iff_anywhere_of_ATri` (Achievability.lean).

*Proof.* *$\mathcal F = \mathrm{Min}\,\mathcal P$.* $\mathcal P \subseteq \mathcal A$ by Theorem 4.1,
and every point of $\mathcal A$ is weakly dominated by a point of $\mathcal P$ by Theorem 4.4. Lemma
1.7(a) applies.

*$\mathrm{Min}\,\mathcal A' = \mathcal F$.* A feasible plan is a plan of the variant with the same cost
and makespan, so $\mathcal A \subseteq \mathcal A'$. Take a plan of
the variant, with cost $C$ and makespan $M'$, and a chain for every passenger (Lemma 3.2(a)). Cut every
route after its last leg that belongs to a chain; if that leg lands in a central city $b$ at time $a$,
append an empty leg $b \to C_G$ leaving at $a$. By Lemma 3.4(b) the chain through that leg ends at least
$d_b$ after $a$, by $M'$, so the new leg, which lasts $\bar d_b = d_b$, arrives by $M'$. A route with no
chain leg becomes empty. The chains are kept, the cost does not grow ($C_G$ is free), and the $q \le p
\le t$ planes with a non-empty route now end in $C_G$, with flight times at most $M'$. Theorem 4.4 on
these planes gives an admissible partition over them with $2t - q$ landings, cost at most $C$ and every
$2\delta(X_k) \le M'$, and Lemma 4.2 adds the $p - q$ other planes. Theorem 4.1 flies this partition
with cost at most $C$ and makespan at most $M'$. So every point of $\mathcal A'$ is weakly dominated by a
point of $\mathcal A$, and Lemma 1.7(a) applies.

*$\mathrm{Min}\,\mathcal P = \mathrm{Min}\,\mathcal X$.* A multiset of $\mathcal X$ has finitely many
partitions, so its point is the point of a partition that attains $M(X)$: $\mathcal X \subseteq
\mathcal P$. The point of a partition is weakly dominated by the point of its multiset. Lemma 1.7(a)
applies. $\square$

**Example 4.6 (an optimal plan with extra landings).** Take $n = 1$, $d_1 = \bar d_1 = 1$, $c_1 = 0$,
$t = 5$ and $p = 3$, so $s = 7$, with any central table. The front is $\{(0, 6)\}$, and a feasible plan
with 9 central landings attains $(0, 6)$: every plane flies $C_I \to 1 \to C_G \to 1 \to C_I \to 1 \to
C_G$ from time 0, without waiting; planes 2 and 3 carry a passenger on both crossings $A$, plane 1 on
its first only.

*Lean:* `PropI.cert`, `PropI.cert_check`, `PropI.front`, `PropI.plan9`, `PropI.centralLandings`,
`PropI.plan9_pareto` (Counterexamples.lean).

*Proof.* A certificate of format v1 (§8) lists the single point $(0, 6)$ with a plan and no gap; the
kernel accepts it, so by Theorem 8.2 (all gaps `relaxed`, vacuously) $\{(0, 6)\}$ is the Pareto front for
every central table. The plan above is accepted by the simulator of the checker, hence feasible
(`planOK_feasible`), and the kernel computes its cost 0, its makespan 6 and its 9 central landings.
$\square$

Both papers' Proposition I says that Pareto-optimal plans land exactly $2t - p$ times. By Example 4.6
it holds only in the sense of Theorem 4.5: under (S) and (H), every front point is the point of an
admissible partition of $2t - p$ landings, flown by Theorem 4.1, but other plans may attain it too.

**Example 4.7 ((H) cannot be dropped).** Take $d = \bar d = (2, 3, 9, 11)$, $c = (50, 44, 17, 0)$, $t = 6$
and $p = 3$, so $s = 9$, and the symmetric central table $d_c(1, 2) = 1$, $d_c(1, 3) = 5$, $d_c(1, 4) =
6$, $d_c(2, 3) = 3$, $d_c(2, 4) = 6$, $d_c(3, 4) = 1$, $d_c(i, i) = 0$. (S) holds and (H) fails: $d_4 = 11
> d_3 + d_c(3, 4) = 10$. The following plan is feasible, of cost 260 and makespan 39, for every central
table in which the flight $4 \to 3$ lasts 1 (legs as from → to [departure, arrival]):

* plane 1: $C_I \to 1$ [0, 2] and $1 \to C_G$ [2, 4] carrying passenger 1; $C_G \to 4$ [4, 15]; $4 \to C_G$
  [15, 26] carrying passenger 2, dropped in 4 by plane 3; $C_G \to 2$ [26, 29], $2 \to C_I$ [29, 32];
  $C_I \to 2$ [32, 35] and $2 \to C_G$ [35, 38] carrying passenger 3;
* plane 2: $C_I \to 2$ [0, 3] and $2 \to C_G$ [3, 6] carrying passenger 4; $C_G \to 2$ [6, 9], $2 \to
  C_I$ [9, 12]; $C_I \to 4$ [12, 23] and $4 \to C_G$ [23, 34] carrying passenger 5;
* plane 3: $C_I \to 4$ [0, 11] carrying passenger 2; $4 \to 3$ [11, 12] and $3 \to C_I$ [12, 21];
  $C_I \to 3$ [21, 30] and $3 \to C_G$ [30, 39] carrying passenger 6.

Every admissible partition of 9 landings with every $\delta(X_k) \le 19$ costs at least 264. So no
admissible partition has cost at most 260 and $2\max_k \delta(X_k) \le 39$: the conclusion of Theorem
4.4 fails for this plan, no point of $\mathcal P$ weakly dominates $(260, 39)$, and $\mathrm{Min}\,
\mathcal P$, which `solveFront` lists, is not the Pareto front of the feasible plans.

*Lean:* `Ex413.net`, `Ex413.plan`, `Ex413.usedGraph`, `Ex413.plan_feasible`, `Ex413.plan_cost`,
`Ex413.plan_makespan`, `Ex413.not_ATriHub`, `Ex413.minCost_19`, `Ex413.admissible_cost_ge`,
`Ex413.no_admissible_partition`, `Ex413.not_admissible_le`, `Ex413.not_isParetoFront`
(Counterexamples.lean); `planOKDur`, `gFeasible_of_planOKDur`, `feasible_iff_gFeasible`,
`GFeasible.mono` (Graph.lean).

*Proof.* The plan flies a central leg, which the simulator of format v1 rejects. A second simulator,
for any table of optional durations and proved sound, accepts it in the kernel on the flights it uses;
adding flights keeps a plan feasible, so it is feasible in every network whose flight $4 \to 3$ lasts 1.
The kernel computes its cost and makespan, and $E(19) = 264$ by the link-forest DP (Theorem 6.7). An
admissible partition with cost at most 260 and $2\max_k\delta(X_k) \le 39$ would have every
$\delta(X_k) \le 19$, hence cost at least 264. By the proof of Theorem 6.9 (`mem_solveFront_iff`),
`solveFront` lists $\mathrm{Min}\,\mathcal P$, and none of its points weakly dominates the point $(260,
39)$ of $\mathcal A$. $\square$

Plane 3's first segment, $C_I \to 4 \to 3 \to C_I$, lasts $21 < 2d_4$: it drops a passenger in 4 and
comes back through 3, which is what the segment bound of Lemma 3.4(b) excludes under (H).

### The per-PPP greedy of both papers

Both papers fix a *possibly Pareto-optimal plan* (PPP), a multiset of central landings, and assert that a
greedy that gives the longest durations first to the least-loaded plane schedules it with the least
makespan (EvoCOP 2015, Algorithm 1; arXiv:2304.14659, §3.2). The papers state the greedy in two forms.
For symmetric durations:

* *EvoCOP's greedy* $G_E$, on a PPP $(e, w)$ of $t$ eastbound and $t - p$ westbound landings and a set
  $\beta \le e \cap w$ of P3 patterns. Loop 1: while westbound landings of $w - \beta$ remain, the
  least-loaded plane flies the longest remaining eastbound landing of $e - \beta$ if it is in $C_I$,
  and the longest remaining westbound one otherwise. Loop 2: each remaining eastbound landing, longest
  first, goes to the least-loaded plane in $C_I$. Step 2: each P3 pattern at $i$, longest first, adds
  $2d_i$ to each of the two least-loaded planes. Each landing adds $2d$ to its plane, and the makespan of
  the PPP is the largest load, the least over the sets $\beta$.
* *arXiv's greedy* $G_A$, on a PPP $(a, \bar a, b)$ of $k + p$ crossings $A$, $k$ crossings $\bar A$
  and $t - p - k$ drop-off/pick-up pairs, of cost $c(a) + c(\bar a) + 2c(b)$. Step 1: each pair, longest
  first, adds $2d$ to the least-loaded plane. Step 2: the $p$ largest crossings $A$, in decreasing order,
  each to the least-loaded plane that has none yet. Step 3: while crossings remain, the least-loaded
  plane whose next pattern ($\bar A$ after $A$, $A$ after $\bar A$) is still available takes the longest
  remaining crossing of that type. Step 4: the pairs again, as in Step 1.

The papers do not say how ties of "least-loaded" are broken; the results below hold for every
tie-breaking. The two other open choices (for $p = 1$, both halves of a P3 go to the single plane;
Steps 2 and 3 of $G_A$ as read above) are fixed as stated.

**Proposition 4.8 (the papers' greedies are not exact).** (a) For $d = \bar d = (6, 10)$, $c = (40,
20)$, $t = 5$, $p = 2$ and every central table, $(260, 60) \in \mathcal F$, yet for every PPP of cost at
most 260, $G_E$ (for every set $\beta$ and every tie-breaking) and $G_A$ (for every tie-breaking) give a
makespan above 60. On the landings of $(260, 60)$ ($e = (1, 1, 1, 2, 2)$, $w = (1, 1, 2)$), loop 1 and
loop 2 without P3 patterns end with the loads 52 and 68, and every $\beta$ gives at least 64.

(b) For $d = \bar d = (1, 3)$, $c = (9, 5)$, $t = 4$, $p = 2$ and every central table, $(42, 12) \in
\mathcal F$, and for every PPP of cost at most 42, $G_A$ gives a makespan above 12 for every tie-breaking.
$G_E$ reaches $(42, 12)$: the PPP $e = (1, 1, 2, 2)$, $w = (1, 2)$, of cost 42, with one P3 pattern at
city 2, gets makespan 12 for every tie-breaking.

*Lean:* `Greedy.minIdxs`, `Greedy.evocopLoadsAll`, `Greedy.evocopMakespansAll`, `Greedy.arxivLoadsAll`,
`Greedy.arxivMakespansAll`, `Greedy.evocop_misses_lpt`, `Greedy.arxiv_misses_lpt`,
`Greedy.evocop_lpt_noP3`, `Greedy.evocop_lpt_ppp`, `Greedy.p3First_front`, `Greedy.arxiv_misses_p3First`,
`Greedy.evocop_reaches_p3First` (Counterexamples.lean); `Examples.lptCounterexample_front`
(Examples.lean).

*Proof.* The fronts come from certificates of format v1 whose gaps are all `relaxed`, accepted by the
kernel, so by Theorem 8.2 they hold for every central table: in (a) the front is $(320, 48), (280, 56),
(260, 60), (240, 64), (200, 72), (160, 80)$, and in (b) it is $(54, 6), (50, 8), (46, 10), (42, 12), (38,
14), (30, 18)$. The greedies are defined in Lean as above, each returning the list of its outcomes over
every sequence of tie-breaking choices. The statements about them are finite computations over the PPPs
of the stated cost and their sets $\beta$, decided by the kernel. $\square$

## 5. Non-symmetric front

**Definition 5.1 (role configuration).** A *role configuration* on $p$ planes gives every plane $k$
multisets $\mathrm{Dr}_k$ (drop-offs), $\mathrm{Pk}_k$ (pick-ups) and $\mathrm{Cr}_k$ (crossings) of
central cities, with $|\mathrm{Cr}_k|$ odd and $\sum_k \mathrm{Dr}_k = \sum_k \mathrm{Pk}_k$ (the
*balance*). Its groups are $X_k = \mathrm{Dr}_k + \mathrm{Pk}_k + \mathrm{Cr}_k$, its cost is $c(X)$,
and the *role load* of plane $k$ is
$$\lambda_k = 2\delta(\mathrm{Dr}_k) + 2\bar\delta(\mathrm{Pk}_k) + \delta(\mathrm{Cr}_k) +
\bar\delta(\mathrm{Cr}_k).$$
Passengers are counted through the landings: the configurations for $t$ passengers are those with $|X|
= 2t - p$.

*Lean:* `RoleConfig`, `RoleConfig.groups` (Roles.lean); `RoleConfig.roleLoad` (NonSymmetric.lean).

A drop-off and the pick-up of the same passenger form a *link*; with $N$ links, $|X| = 2N +
\sum_k |\mathrm{Cr}_k|$, and the passengers are the $N$ linked ones and one per crossing $A$, $(|\mathrm
{Cr}_k| + 1)/2$ per plane.

**Definition 5.2 (scheduled configuration, template value).** A *scheduled configuration* $S$ gives
every plane $k$ an ordered list $\mathrm{Dr}_k = (\mathrm{Dr}_k[0], \mathrm{Dr}_k[1], \dots)$ of
drop-offs, an ordered list $\mathrm{Pk}_k$ of pick-ups and a multiset $\mathrm{Cr}_k$ of crossings, and
maps every pick-up slot $(v, l)$ to a drop-off slot $\mathrm{mate}(v, l) = (u, j)$. It is *valid* if
every $|\mathrm{Cr}_k|$ is odd, the drop-off $\mathrm{Dr}_u[j]$ of $\mathrm{mate}(v, l)$ is at the city
of $\mathrm{Pk}_v[l]$, $\mathrm{mate}$ is injective, and there are as many drop-offs as pick-ups in all.
Its size $|S|$, cost $c(S)$ and role loads $\lambda_k$ are those of Definition 5.1, read on the lists. A
*link* $(u, j;\, v, l)$ at $x$ is a pick-up slot $(v, l)$ at $x$ with $\mathrm{mate}(v, l) = (u, j)$.
The *template value* of $S$ is
$$M_{\rm tmpl}(S) = \max\Big(\max_k \lambda_k,\ \max_{(u, j;\, v, l) \text{ at } x}\ \mathrm{Pre}_u(j) +
d_x + \bar d_x + \mathrm{Suf}_v(l)\Big),$$
with $\mathrm{Pre}_u(j) = 2\sum_{j' < j} d(\mathrm{Dr}_u[j'])$ and $\mathrm{Suf}_v(l) = 2\sum_{l' > l}
\bar d(\mathrm{Pk}_v[l'])$. $S$ *schedules* a role configuration if its lists and multisets are that
configuration's drop-offs, pick-ups and crossings.

*Lean:* `Sched`, `Sched.Valid`, `Sched.size`, `Sched.cost`, `Sched.load`, `Sched.pre`, `Sched.suf`,
`Sched.term`, `Sched.tmpl` (SearchGap.lean); `Sched.Schedules` (NSFront.lean).

**Theorem 5.3 (schedulable domination).** Assume (A1-NS) and $p \le t$. Every feasible plan with cost
$C$ and makespan $M$ gives a valid scheduled configuration $S$ with $|S| = 2t - p$, $c(S) \le C$ and
$M_{\rm tmpl}(S) \le M$. The template of $S$ (Lemma 5.5) is then a feasible plan of cost $c(S)$ and
makespan $M_{\rm tmpl}(S) \le M$.

*Lean:* `schedulableDomination_all` (DominationAll.lean); `schedulableDomination_template`
(NSFront.lean); `Feasible.split` (NonSymmetric.lean); `exists_transfer_pw`, `withLoops`,
`planesOK_withLoops` (DominationAll.lean); `tExchange_step`, `tCut_step`, `tSplice_step`,
`ordered_of_stuck`, `exists_rewired` (Rewire.lean); `exists_links` (LinkCount.lean); `toSched`,
`toSched_valid`, `toSched_cost_le`, `toSched_tmpl_le`, `exists_sched_of` (SchedBuild.lean).

*Proof.* *Step 1: no central flights.* Replace every central leg $a \to b$ by $a \to h \to b$ through
the hub $h$ with $\mathrm{dur}(a, h) + \mathrm{dur}(h, b) \le d_c(a, b)$, which (A1-NS) provides, leaving
at the same time. The plane reaches $b$ no later and waits there; a passenger on board stays on board
through $h$. The plan stays feasible, its cost is the same ($h$ is free), and its makespan does not
grow. Every route is now a sequence of visits (§3). By Lemma 3.2(b), every passenger $\pi$ rides a leg
$\alpha_\pi : C_I \to x$ followed by a leg $\beta_\pi : x \to C_G$ that leaves no earlier than
$\alpha_\pi$ arrives. For a visit $\gamma$ at $x$, $a(\gamma)$ is the time its first leg arrives in $x$
and $e(\gamma)$ the time its second leg leaves, so $a(\gamma) \le e(\gamma)$. From now on only the
visits of the planes and the legs $\alpha_\pi$, $\beta_\pi$ are used.

*Step 2: rewiring.* Next to the routes, keep a set of *loops*, empty at first: closed sequences of
visits whose legs all depart and arrive at one time $\tau$, so they last 0. A passenger is *carried
through* if $\alpha_\pi$ and $\beta_\pi$ are the two legs of one visit, of a route or of a loop.
Otherwise it is a *hand-off*, from the visit $\gamma$ of $\alpha_\pi$ to the visit $\gamma'$ of
$\beta_\pi$, both at its city $x$. While one of these moves applies, apply it.

* *Exchange.* $\gamma$ is on the route of $u$, $\gamma'$ on the route of $v \ne u$, and $a(\gamma') \le
  e(\gamma)$. Give $u$ the legs of $v$ from $\beta_\pi$ on, and $v$ the legs of $u$ after $\alpha_\pi$.
  Both routes stay valid: $\beta_\pi$ leaves after $\alpha_\pi$ arrives, and the second leg of $\gamma$
  leaves after the first leg of $\gamma'$ arrives.
* *Cut.* $\gamma$ and $\gamma'$ are on one route, $\gamma'$ before $\gamma$. The route gives
  $e(\gamma') \le a(\gamma)$ and the passenger $a(\gamma) \le e(\gamma')$, so every leg from $\beta_\pi$
  to $\alpha_\pi$ departs and arrives at $\tau = e(\gamma')$. These legs form a closed walk at $x$. Remove
  it from the route, which keeps the first leg of $\gamma'$ and the second leg of $\gamma$, a visit at $x$
  since $a(\gamma') \le \tau \le e(\gamma)$. The walk becomes a loop, made of the visit
  $(\alpha_\pi, \beta_\pi)$ and the visits strictly between $\gamma'$ and $\gamma$.
* *Splice.* One of $\gamma, \gamma'$ is a visit $F$ of a loop at time $\tau$, the other a visit
  $\delta$ of a route, and $e(\gamma) > a(\gamma')$. Then $a(\delta) \le \tau \le e(\delta)$: if $F =
  \gamma$, then $e(\gamma) = \tau > a(\delta)$, and $\tau \le e(\delta)$ by the passenger; if $F =
  \gamma'$, then $a(\delta) \le \tau$ by the passenger, and $e(\delta) > \tau$. Insert the loop into
  the route at $\delta$: the first leg of $\delta$, the second leg of $F$, the loop around to $F$, the
  first leg of $F$, the second leg of $\delta$. The route stays valid, and $\pi$ is carried through by
  the new visit of $\alpha_\pi$ and $\beta_\pi$.

Every move keeps the multiset of legs, so the cost, and keeps every route's last leg or exchanges two of
them, so the makespan bound. It carries one more passenger through and none fewer: the only visits it
breaks are $\gamma$ and $\gamma'$, and a visit that carries another passenger through holds both of its
legs, so it is neither. So the moves stop. Then every hand-off from $\gamma$
to $\gamma'$ has $e(\gamma) \le a(\gamma')$: between two routes since the exchange does not apply; on
one route since the cut does not apply, so $\gamma'$ comes after $\gamma$; between a loop and a route
since the splice does not apply; between two loops at times $\tau$ and $\tau'$, since $e(\gamma) = \tau$
is when $\alpha_\pi$ arrives and $a(\gamma') = \tau'$ when $\beta_\pi$ leaves.

*Step 3: links.* Draw an arrow $\gamma \to \gamma'$ for every passenger, from the visit of $\alpha_\pi$
to the visit of $\beta_\pi$ (an arrow $\gamma \to \gamma$ if it is carried through). A leg carries one
passenger, so a visit has at most one outgoing and one incoming arrow; an arrow leaves a visit entered
from $C_I$ and enters a visit left towards $C_G$; and $e(\gamma) \le a(\gamma')$ when $\gamma \ne
\gamma'$. Then there is a set $\Lambda$ of *links*, pairs of a drop-off visit and a pick-up visit at the
same city with $a(B) \le e(\bar B)$, each visit in at most one link, such that $t \le |\Lambda| +
\#A$. By induction on $\#A$, the number of visits of type $A$: if there is none, an arrow leaves a
visit entered from $C_I$ and not of type $A$, a $B$, and enters a visit left towards $C_G$, a $\bar B$;
so $\gamma \ne \gamma'$, $a(\gamma) \le e(\gamma) \le a(\gamma') \le e(\gamma')$, and the arrows are the
links. Otherwise remove a visit $w$ of type $A$, and replace two arrows $s \to w \to d$ by one arrow $s
\to d$; for $s \ne d$, still $e(s) \le a(w) \le e(w) \le a(d)$. This loses at most one arrow, and
$\#A$ drops by one.

*Step 4: the configuration.* Attach every loop to some plane: its drop-off visits come first, its other
visits last; they last 0. A plane's linked $B$ visits, in this order, are its drop-offs; its linked
$\bar B$ visits, in this order, are its pick-ups; each pick-up is matched to the drop-off of its link;
and its $A$ and $\bar A$ visits are its crossings, $2a_k + 1$ of them, with $a_k$ its number of $\bar A$
visits (Lemma 3.1, on the route and on the loops). The configuration is valid. Distinct visits have
distinct first legs, each a leg of the plan of Step 1 landing in the visit's city, so its cost is at
most $C$.

*Step 5: the template value.* By Lemma 3.4(c), every visit of a route lasts its role weight, a visit of
a loop lasts 0, and the visits of plane $k$ last at most $M$ in all, so $\lambda_k \le M$. Take a link
from the $j$-th drop-off $\gamma$ of $u$ to the $l$-th pick-up $\gamma'$ of $v$, at $x$. If $\gamma$ is
on the route, $u$ flies its earlier drop-offs before it, so $\mathrm{Pre}_u(j) + d_x \le a(\gamma)$; if
$\gamma$ is in a loop, $\mathrm{Pre}_u(j) = d_x = 0$ (a loop's legs last 0, and its drop-offs come
first). If $\gamma'$ is on the route, $v$ flies $\bar d_x$ to $C_G$ after $e(\gamma')$ and then its later
pick-ups, all by $M$, so $e(\gamma') + \bar d_x + \mathrm{Suf}_v(l) \le M$; if $\gamma'$ is in a loop at
time $\tau$, then $\bar d_x = \mathrm{Suf}_v(l) = 0$ and $e(\gamma') = \tau \le M$. As $a(\gamma) \le
e(\gamma')$, the term of the link is at most $M$. So $M_{\rm tmpl} \le M$.

*Step 6: shrinking.* With all of $\Lambda$ and all crossings, the configuration has $|\Lambda| + \sum_k
(a_k + 1) = |\Lambda| + \#A \ge t$ passengers, and $D = |\Lambda| + \#A - t$ too many. If $D \le
|\Lambda|$, keep $|\Lambda| - D$ of the links and all crossings. Otherwise keep no link, and $2(a_k -
b_k) + 1$ of the crossings of plane $k$, with $b_k \le a_k$ and $\sum_k b_k = \#A - t$. Either way the
configuration has $t$ passengers, so $2t - p$ landings. Dropping links and crossings, with the same
orders, keeps it valid and does not raise its cost, its role loads, the $\mathrm{Pre}$ and $\mathrm{Suf}$
or the link terms, so $M_{\rm tmpl} \le M$ still.

By Lemma 5.5, the template of $S$ is a feasible plan of cost $c(S)$ and makespan $M_{\rm tmpl}(S)$.
$\square$

No order of the legs beyond the routes and the passengers' chains is used. The cut and the loops
handle a passenger handed backwards on one plane; by the cut, the legs between its two flights then all
happen at one instant.

**Corollary 5.4 (role-load bound).** Assume (A1-NS) and $p \le t$. Every feasible plan with cost $C$
and makespan $M$ gives a role configuration with $2t - p$ landings, cost at most $C$ and every
$\lambda_k \le M$.

*Lean:* `Feasible.exists_roleConfig_of_domination`, `Sched.load_le_tmpl` (NSFront.lean).

*Proof.* Take the $S$ of Theorem 5.3 and the role configuration it schedules: $\mathrm{mate}$ pairs
every pick-up with a drop-off of the same city, injectively, and there are as many of each, so the
balance holds. Its cost is $c(S) \le C$, and every $\lambda_k$ is one of the terms of the maximum
$M_{\rm tmpl}(S) \le M$. $\square$

**Lemma 5.5 (template plans).** Let $S$ be a valid scheduled configuration with $|S| = 2t - p$. Then $p
\le t$, and for every network with these durations, whatever its central table, the *template* of $S$ is
a feasible plan of cost $c(S)$ and makespan exactly $M_{\rm tmpl}(S)$. In the template every plane $k$,
from time 0,

1. flies its drop-offs in order, $C_I \to x \to C_I$, the first leg carrying a new passenger, which it
   leaves in $x$;
2. flies its crossings, $C_I \to x \to C_G$ carrying a new passenger and $C_G \to x \to C_I$ empty,
   alternately, beginning and ending with the former;
3. flies its pick-ups in order, $C_G \to y \to C_G$, leaving $y$ at the later of its arrival and the
   arrival of the passenger dropped by the matched drop-off, and carrying that passenger to $C_G$.

Every other leg leaves as soon as the plane arrives. Nothing is assumed on the durations; zero
durations are allowed.

*Lean:* `Sched.tmplPlan`, `Sched.tmplPlan_spec`, `Sched.exists_plan`, `Sched.Valid.count_eq`,
`Sched.Valid.slot_bijective`, `Sched.slack_succ`, `Sched.pickTime_length_eq`, `Sched.tmplPlan_chain`
(Template.lean).

*Proof.* *Count.* Let $N$ be the number of drop-offs and $Q = \sum_k (|\mathrm{Cr}_k| + 1)/2$ the number
of crossings $A$. As every $|\mathrm{Cr}_k|$ is odd, $|S| = 2N + 2Q - p$, so $N + Q = t$, and $Q \ge p$
gives $p \le t$. The passengers are numbered by the drop-off slots and the crossings $A$.

*Routes.* Each phase of a route starts where and when the previous one ends: the drop-offs start and
end in $C_I$; an odd number of crossings leads from $C_I$ to $C_G$; the pick-ups start and end in
$C_G$. Every leg is a hub flight of its duration, so every plane flies a route from $C_I$ at time 0 to
$C_G$. Drop-offs never wait, so the $j$-th drop-off of $u$, at $x$, reaches $x$ at $\mathrm{Pre}_u(j) +
d_x$.

*Makespan.* Let $\varphi_k(l)$ be the time plane $k$ leaves $C_G$ for its $l$-th pick-up, so
$\varphi_k(0) = 2\delta(\mathrm{Dr}_k) + \delta(\mathrm{Cr}_k) + \bar\delta(\mathrm{Cr}_k)$. If that
pick-up is at $y$ and its link comes from $(u, j)$, the plane is back in $C_G$ at
$\varphi_k(l+1) = \max(\varphi_k(l) + 2\bar d_y,\ \mathrm{Pre}_u(j) + d_y + \bar d_y)$. Since
$\mathrm{Suf}_k(l-1) = 2\bar d_y + \mathrm{Suf}_k(l)$, this reads $\varphi_k(l+1) + \mathrm{Suf}_k(l) =
\max(\varphi_k(l) + \mathrm{Suf}_k(l-1),\ \text{the term of the link})$, and $\varphi_k(0) +
\mathrm{Suf}_k(-1) = \lambda_k$. Unrolling, plane $k$ ends at the maximum of $\lambda_k$ and of the
terms of the links into it, and the makespan is $M_{\rm tmpl}(S)$.

*Passengers.* $\mathrm{mate}$ is injective and there are as many drop-off slots as pick-up slots, so
it is a bijection, each pick-up slot at the city of its drop-off slot. The passenger of a drop-off slot
rides the drop-off's first leg $C_I \to x$ and then the second leg $x \to C_G$ of the matched pick-up,
which leaves no earlier than the first arrives; the passenger of a crossing rides its two legs. These
are routes from $C_I$ at time 0 to $C_G$, and every other leg is empty, so the legs that carry a
passenger are exactly its two. The central landings are the drop-offs, pick-ups and crossings, so the
cost is $c(S)$. $\square$

**Corollary 5.6 (non-symmetric front, H4).** Assume (A1-NS) and $p \le t$. Let $\mathcal K_S$ be the set
of the points $(c(S), M_{\rm tmpl}(S))$ of the valid scheduled configurations $S$ with $|S| = 2t - p$,
and $\mathcal K$ the set of the points $(c(\mathrm{cfg}), m(\mathrm{cfg}))$ of the role configurations
with $2t - p$ landings, where $m(\mathrm{cfg})$ is the least $M_{\rm tmpl}(S)$ over the valid $S$ that
schedule $\mathrm{cfg}$; every role configuration has one, so $m(\mathrm{cfg})$ is attained. Then
$$\mathcal F = \mathrm{Min}\,\mathcal K_S = \mathrm{Min}\,\mathcal K,$$
and a list is the Pareto front of the feasible plans iff it is the Pareto front of $\mathcal K_S$.

*Lean:* `schedPoints`, `schedPoints_subset_achievable`, `achievable_dominated_schedPoints`,
`minimal_achievable_iff_schedPoints`, `isParetoFront_iff_of_subset_of_dominated`,
`isParetoFront_achievable_iff_schedPoints`, `RoleConfig.exists_sched`, `RoleConfig.leastTmpl`,
`RoleConfig.exists_leastTmpl`, `configPoints`, `minimal_schedPoints_iff_configPoints`,
`minimal_achievable_iff_configPoints` (NSFront.lean).

*Proof.* $\mathcal K_S \subseteq \mathcal A$ by Lemma 5.5, and every point of $\mathcal A$ is weakly
dominated by a point of $\mathcal K_S$ by Theorem 5.3; Lemma 1.7(a) gives $\mathcal F = \mathrm{Min}\,
\mathcal K_S$. A Pareto front of $\mathcal A$ lists points of $\mathrm{Min}\,\mathcal A = \mathrm{Min}\,
\mathcal K_S \subseteq \mathcal K_S$ (Lemma 1.7(b)) and dominates $\mathcal K_S \subseteq \mathcal A$;
a Pareto front of $\mathcal K_S$ lies in $\mathcal A$ and dominates $\mathcal A$ through $\mathcal K_S$;
incomparability is the same condition. Every role configuration is scheduled by a valid $S$: order its
drop-offs and pick-ups in any way and match them city by city, which the balance allows. So
$m(\mathrm{cfg})$ is a least element of a non-empty set of natural numbers, attained by some $S$, and
$\mathcal K \subseteq \mathcal K_S$. The point of a valid $S$ is weakly dominated by the point of the
configuration it schedules, which has the same cost and $m(\mathrm{cfg}) \le M_{\rm tmpl}(S)$. Lemma
1.7(a) gives $\mathrm{Min}\,\mathcal K_S = \mathrm{Min}\,\mathcal K$. $\square$

**Proposition 5.7 (harmful waiting).** Take $n = 2$, $d = (3, 19)$, $\bar d = (3, 11)$, $c = (5, 1)$, $t
= 7$ and $p = 4$, so $s = 10$, with any central table satisfying (A1-NS).

(a) Some role configuration with 10 landings has cost 14 and every $\lambda_k \le 72$, and every role
configuration with 10 landings and every $\lambda_k \le 73$ costs at least 14.

(b) Every valid scheduled configuration with 10 landings and cost below 18 has $M_{\rm tmpl} > 73$.

(c) Every feasible plan of makespan at most 73 costs at least 18.

So some role configuration with 10 landings has cost at most 14 and every $\lambda_k \le 73$, but no
feasible plan has cost at most 14 and makespan at most 73.

*Lean:* `Prop65.cfg14`, `Prop65.cfg14_load`, `Prop65.rolesBound_73`, `Prop65.cheapest_roleConfig`,
`Prop65.search73`, `Prop65.search73_closed`, `Prop65.tmpl_gt_of_cost_lt`,
`Prop65.cost_ge_of_makespan_le`, `Prop65.prop65`, `Prop65.harmful_waiting` (Counterexamples.lean).

*Proof.* (a) Plane 1 crosses at city 1 and picks up three times at city 2: $\lambda_1 = 6 + 3 \cdot 22
= 72$. Planes 2, 3 and 4 cross at city 2 and drop off once at city 2: $\lambda_k = 30 + 38 = 68$. The
cost is $5 + 9 = 14$. The lower bound is the `roles` bound of Proposition 8.3 at level 73, which the
kernel computes to be 14. (b) The exhaustive search of Proposition 8.6 at level 73, for configurations of
cost below 18, is closed; the kernel decides it in eight parts, by the option of the first plane. (c)
Theorem 5.3 turns a plan of cost $C$ and makespan at most 73 into a valid $S$ with 10 landings, $c(S)
\le C$ and $M_{\rm tmpl}(S) \le 73$; by (b), $c(S) \ge 18$. $\square$

arXiv:2304.14659 reads the front off the role loads, which rules out harmful waiting: a pick-up that
must wait for the passenger it collects. By (b) and Lemma 5.5, every template of the configuration of (a)
ends after 73, above its largest role load 72: its pick-up plane waits.

**Definition 5.8 (flight graphs, the reduction).** A *flight graph* $U$ has the hubs $C_I$, $C_G$,
central vertices $1, \dots, n$, an optional duration $\mathrm{dur}_U(a, b) \in \mathbb N$ for every
ordered pair of locations, and landing costs $c_i$. Its plans, feasibility, cost and makespan are those
of Definition 1.2 with the flights of $U$; $\mathcal A_U$ is the set of the points of its feasible plans
and $\mathcal F_U = \mathrm{Min}\,\mathcal A_U$. A network of Definition 1.1 is the flight graph of all
its flights; the *clique instance without central flights* with hub durations $d, \bar d$ is the flight
graph of its hub flights only.

For a walk $x_0, \dots, x_m$ of $U$, $\varphi$ is the sum of its durations and $\omega = \sum_{j \ge 1}
c(x_j)$ the cost of its landings after the first vertex (hubs free). The *reduction* $f(U)$ of
arXiv:2304.14659 §2.4 is the clique instance without central flights, with the same $t$ and $p$, that
has one city $v = (i, w, e)$ for every central vertex $i$, every simple path $w$ from $C_I$ to $i$ and
every simple path $e$ from $i$ to $C_G$ (the paths may pass through a hub), with $d_v = \varphi(w)$,
$\bar d_v = \varphi(e)$ and $c_v = \omega(w) + \omega(e)$. The paper claims $\mathcal F_U = \mathcal
F_{f(U)}$.

*Lean:* `FlightGraph`, `GFlies`, `GFeasible`, `gAchievable`, `Network.toGraph`, `cliqueGraph`,
`simplePaths`, `pathDur`, `pathCost`, `VCity`, `vcities`, `Reduced.graph`, `Reduced.c` (Graph.lean).

**Example 5.9 (the reduction misses the front).** Let $U$ be the path $C_I$–$a$–$b$–$C_G$, with
durations 1, 2 and 1 in both directions and no other flight, $c_a = c_b = 1$, $t = 3$ and $p = 2$. Then
$f(U)$ has the two cities $(a,\ C_I a,\ a b C_G)$ and $(b,\ C_I a b,\ b C_G)$, with $(d, \bar d, c) = (1,
3, 2)$ and $(3, 1, 2)$. Its front is $\{(8, 10)\}$, as a flight graph, and also as an instance of
Definition 1.1 for every central table satisfying (A1-NS). $U$ has a feasible plan of cost 8 and
makespan 8 (legs as from → to [departure, arrival]):

* plane 1: $C_I \to a$ [0, 1] and $a \to b$ [1, 3] carrying passenger 2; $b \to a$ [3, 5]; $a \to b$ [5,
  7] and $b \to C_G$ [7, 8] carrying passenger 3;
* plane 2: $C_I \to a$ [0, 1] carrying passenger 3; $a \to C_I$ [1, 2]; $C_I \to a$ [2, 3], $a \to b$
  [3, 5] and $b \to C_G$ [5, 6] carrying passenger 1; $C_G \to b$ [6, 7]; $b \to C_G$ [7, 8] carrying
  passenger 2.

So $(8, 10) \notin \mathcal F_U$, and $\mathcal F_U \ne \mathcal F_{f(U)}$.

*Lean:* `Ex611.U`, `Ex611.U_undirected`, `Ex611.U_noHubFlight`, `Ex611.vcities_U`,
`Ex611.vcities_data`, `Ex611.reduced_graph`, `Ex611.reduced_c`, `Ex611.reducedCert`,
`Ex611.reducedCert_check`, `Ex611.reduced_front`, `Ex611.reduced_front_network`, `Ex611.plan`,
`Ex611.plan_feasible`, `Ex611.mem_gAchievable_U`, `Ex611.fronts_differ` (Counterexamples.lean);
`feasible_iff_gFeasible`, `GFeasible.feasible_of_clique`, `gFeasible_of_planOKDur` (Graph.lean).

*Proof.* The kernel enumerates the simple paths and computes the two cities. A certificate of format v2
for the two-city instance lists the single point $(8, 10)$, its plan, and the `search` kind for the
fastest point; the kernel accepts it, so by Theorem 8.7 its front is $\{(8, 10)\}$ for every central
table satisfying (A1-NS). A feasible plan of the flight graph $f(U)$ flies hub flights only, so it is a
feasible plan of every network with the same hub durations, for instance the one whose central flights
all last 100, which satisfies (A1-NS); so it is weakly dominated by $(8, 10)$, which the certificate's
plan attains in $f(U)$. The plan of $U$ is accepted in the kernel by the sound simulator for optional
durations. $(8, 8) \le (8, 10)$ and $(8, 8) \ne (8, 10)$, so $(8, 10)$ is not minimal in $\mathcal A_U$.
$\square$

Plane 1 flies the segment $C_I\,a\,b\,a\,b\,C_G$: it drops passenger 2 in $b$ at time 3, flies the central
edge back to $a$ and picks passenger 3 up there at time 5. $f(U)$ has no central flights; between its two
cities a plane passes through a hub, which takes $\bar d_1 + \bar d_2 = d_1 + d_2 = 4$, twice the edge
$a$–$b$.

**Example 5.10 (the shuttle construction misses the front).** Take $n = 2$, $d = (1, 3)$, $\bar d = (3,
1)$, $c = (6, 1)$, $t = 3$, $p = 2$, and the central table $d_c(1, 2) = d_c(2, 1) = 2$, $d_c(1, 1) = d_c(2,
2) = 0$. (AΔ) holds and (A1-NS) fails. The instance has a feasible plan of cost 15 and makespan 8, so
its front has a point that weakly dominates $(15, 8)$; the plan is feasible for every central table in
which the flight $2 \to 1$ lasts 2:

* plane 1: $C_I \to 1$ [0, 1] carrying passenger 1, left in 1; $1 \to C_I$ [1, 2]; $C_I \to 2$ [2, 5]
  and $2 \to C_G$ [5, 6] carrying passenger 2; $C_G \to 2$ [6, 7]; $2 \to C_G$ [7, 8] carrying
  passenger 3;
* plane 2: $C_I \to 2$ [0, 3] carrying passenger 3, left in 2; $2 \to 1$ [3, 5]; $1 \to C_G$ [5, 8]
  carrying passenger 1.

arXiv:2304.14659 §3.3 handles the "$B\bar A\bar B$ situation" (a drop-off at $i$, a shuttle $C_G \to i
\to j \to C_I$ carrying the passenger to $j$, a pick-up at $j$) by an augmented instance without central
flights. Its cities have one duration and one cost per pattern $A$, $\bar A$, $B$, $\bar B$: a central
city $i$ keeps $d_i + \bar d_i$, $d_i + \bar d_i$, $2d_i$, $2\bar d_i$ and the cost $c_i$ for each; every
ordered pair $i \ne j$ adds a virtual city with durations $\min(d_i + \bar d_i,\ d_j + \bar d_j)$, $\bar
d_i + d_c(i, j) + d_j$, $2d_i$, $2d_j$ and costs $c_i + c_j$, $c_i + c_j$, $c_i$, $c_j$ (equations
(3)–(6) and Figure 10, as printed). A configuration of the augmented instance gives every plane a number
of patterns of each type at every city, with one more $A$ than $\bar A$ per plane, as many $B$ as $\bar B$
at every city, and $\#A + \#B = t$ passengers. Its points are its cost, for $2t - p$ landings, with any
makespan at least its loads. The paper's "a $\bar A$ with a null multiplicity" has two readings: the
shuttle is not counted, or every $B$ at a virtual city needs an $\bar A$ there. In both readings, every
configuration has a plane whose patterns last at least 10, whatever its number of landings; so every point
of the construction has makespan at least 10, and $(4, 10)$ is one. So the front of the construction is
not the front of the instance.

*Lean:* `Shuttle.TCity`, `Shuttle.plainCity`, `Shuttle.shuttleCity`, `Shuttle.augment`,
`Shuttle.TConfig`, `Shuttle.TConfig.Valid`, `Shuttle.points`, `Shuttle.net_ATri`,
`Shuttle.not_net_A1NS`, `Shuttle.plan`, `Shuttle.plan_feasible`, `Shuttle.plan_cost`,
`Shuttle.plan_makespan`, `Shuttle.front_le`, `Shuttle.load_ge`, `Shuttle.points_ge`, `Shuttle.mem_points`,
`Shuttle.shuttle_misses` (Counterexamples.lean).

*Proof.* (AΔ) is a finite check, decided by the kernel; (A1-NS) fails as $2 < \min(d_1 + d_2,\ \bar d_1 +
\bar d_2) = 4$. The plan is checked by the sound simulator for optional durations, with cost 15 and
makespan 8. The points of the plans below $(15, 8)$ form a non-empty subset of the well quasi-ordered
$\mathbb N^2$, so it has a minimal point, which is minimal in $\mathcal A$. The augmented instance has
four cities, whose patterns last $(4, 4, 2, 6)$, $(4, 4, 6, 2)$, $(4, 8, 2, 6)$ and $(4, 4, 6, 2)$ (the
two central cities, then the virtual cities of $(1, 2)$ and $(2, 1)$). With 3 passengers on 2 planes,
each plane flies an $A$, which lasts 4, so there is at most one $B\bar B$ pair. Without a pair, some
plane flies $A\bar A A$, at least 12. With a pair at one city, its $B$ and $\bar B$ last $2$ and $6$ or $6$
and $2$, so the plane flying the longer one, or both, reaches at least 10. Both planes crossing at city
2, plane 1 dropping a passenger there and plane 2 picking it up, gives cost 4 and loads 10 and 6, valid
in both readings. Since every point of the construction has makespan at least 10 and the front of the
instance has a point of makespan at most 8, the two fronts differ. $\square$

Plane 2 of the plan flies a *split crossing* $C_I \to 2 \to 1 \to C_G$: it leaves a passenger in 2 and
takes another from 1, a link between two cities, which neither role configurations nor the shuttle
construction contain. The construction is formalised as printed; with the pick-up at the virtual city
lasting $2\bar d_j$ instead of $2d_j$, a correction proposed in revision 2, nothing is proved here.

## 6. Algorithm

The solver and the checkers work at *levels* $T \in \mathbb N$, bounds on the loads $\delta(X_k)$, with
tables computed for the levels $0, \dots, T_{\max}$.

**Lemma 6.1 (one-plane table).** Let $G[0][T] = 0$ and $G[m + 1][T] = \min_{i :\, d_i \le T} (c_i +
G[m][T - d_i])$ ($\infty$ over the empty set). Then $G[m][T]$ is the least cost of a multiset of $m$
cities with $\delta \le T$, and it is $\infty$ iff there is none. The memoised table, with rows $0,
\dots, m_{\max}$ and columns $0, \dots, T_{\max}$, agrees with it.

*Lean:* `oneplane`, `oneplane_le_cost`, `exists_cost_eq_oneplane`, `isLeast_oneplane`,
`oneplane_eq_top_iff`, `oneplaneTable`, `oneplaneTable_getD` (OnePlane.lean).

*Proof.* By induction on $m$. A multiset $Y$ of $m + 1$ cities with $\delta(Y) \le T$ contains some $i$,
with $d_i \le T$, and $Y - \{i\}$ has $m$ cities within $T - d_i$, so $c(Y) \ge c_i + G[m][T - d_i]$.
Adding $i$ to a cheapest $m$-multiset within $T - d_i$ attains the minimum. The memoised table
computes the same recursion row by row. $\square$

Lemma 6.1 holds for any durations $d$; with a weight $w$ in their place it gives $G_w$ (Notation,
§1.5).

**Lemma 6.2 (the function $E$).** Let $E(T)$ be the least cost of an admissible partition of $2t - p$
landings into $p$ groups with every $\delta(X_k) \le T$ ($\infty$ if there is none). $E$ is
non-increasing and attained when finite. With $1 \le p$, $E(T) = \infty$ for $T < d_{\min}\lceil
s/p\rceil$. A level $T$ at which $E$ drops ($E(T) = C$ and $E(T') > C$ for every $T' < T$) has $T \le
(2t - p)\,d_{\max}$.

*Lean:* `minCost`, `minCost_le`, `minCost_attained`, `minCost_antitone` (MinCost.lean);
`minCost_eq_top_of_lt`, `breakpoint_le` (Solver.lean).

*Proof.* A larger level allows more partitions, and there are finitely many partitions of $2t - p$
landings. Some group of every partition has at least $\lceil s/p\rceil$ landings, each of duration at
least $d_{\min}$, so its load is at least $d_{\min}\lceil s/p\rceil$. A partition attaining $E(T)$ has every load at most $(2t - p)\,d_{\max}$, so if $T$ were larger, $E((2t -
p)\,d_{\max}) \le C$. $\square$

**Proposition 6.3 (front = breakpoints of $E$).** Assume (S), (H) and $p \le t$. Then $(C, M) \in
\mathcal F$ iff $M = 2T$ for some $T$ with $E(T) = C$ and $E(T') > C$ for every $T' < T$.

*Lean:* `minimal_admissiblePoints_iff`, `minimal_achievable_iff_minCost_hub` (Solver.lean); corollary
under (AΔ): `minimal_achievable_iff_minCost_ATri` (Solver.lean).

*Proof.* By Theorem 4.5, $\mathcal F = \mathrm{Min}\,\mathcal P$. Let $(C, M) \in \mathrm{Min}\,
\mathcal P$, the point of an admissible $X$ with $T = \max_k \delta(X_k)$, so $M = 2T$ and $E(T) \le C$.
A partition attaining $E(T)$ has a point $\le (C, M)$, so $E(T) = C$; and $E(T') \le C$ for some $T' <
T$ would give a point $\le (C, 2T')$, below $(C, M)$. Conversely, let $E(T) = C < E(T')$ for all $T' <
T$, and let $X$ attain $E(T)$. Then $T' = \max_k \delta(X_k) \le T$ and $E(T') \le C$, so $T' = T$ and
$(C, 2T) \in \mathcal P$. A point $(C', 2T'') \in \mathcal P$ below it has $T'' \le T$ and $E(T'') \le C'
\le C$, so $T'' = T$ and $C' = C$. $\square$

**Proposition 6.4 (bracket).** Let $U_2(T)$ be the least cost of a partition of $2t - p$ landings, with
every load at most $T$, whose link forest has trees of one or two planes: a single plane with an odd
number of landings, or two planes linked at a city $b$ in the image of $\mathrm{domRep}$ (Proposition
6.5), each with one copy of $b$ and an odd number of free landings; the free landings come from the
table of Lemma 6.1. At every level $T \le T_{\max}$,
$L(T) \le E(T) \le U_2(T)$, where $L = L_d$ is the relaxation of Lemma 3.5 computed from the table of
Lemma 6.1, and where $L(T) = U_2(T)$, $E(T) = L(T)$.

*Lean:* `relaxedBoundAt`, `relaxRow_getD`, `relaxedBoundAt_le_totalCost` (Relaxation.lean);
`pairsBoundAt`, `relaxedBoundAt_le_minCost`, `minCost_le_pairsBoundAt`, `minCost_eq_of_bracket`
(PairBound.lean).

*Proof.* The groups of an admissible partition are non-empty (Lemma 2.4), so the partition is among the
groupings over which $L$ minimises: $L \le E$. Every finite value of $U_2$ is the cost of such a forest
with loads at most $T$, whose groups are admissible by Lemma 2.6: $E \le U_2$. $\square$

**Proposition 6.5 (dominance, symmetric).** For every map $\mathrm{rep}$ from cities to cities,
replacing every landing of an admissible partition by its image gives an admissible partition with the
same group sizes. The map $\mathrm{domRep}$, which scans the cities in index order from $i$ and moves to
a city that dominates $i$ whenever its $(d, c)$ is lexicographically smaller than the current one's, has
$d_{\mathrm{domRep}(i)} \le d_i$ and $c_{\mathrm{domRep}(i)} \le c_i$; replacing every landing by its
image under $\mathrm{domRep}$ does not raise the cost or the loads.

*Lean:* `Admissible.map` (Shrink.lean); `domRep`, `domRep_le`, and the replacement inside
`sigmaBoundAt_le_totalCost` (AdmissibleBound.lean) and `treeBoundAt_le_totalCost` (TreeBound.lean).

*Proof.* Let $\eta'_k$ be the set of cities $j$ such that an odd number of cities of $\eta_k$ are sent
to $j$. Such a $j$ is the image of a city of $\eta_k \subseteq \mathrm{supp}\,X_k$: (h1). $|\eta'_k|
\equiv |\eta_k|$: (h2). For every $j$, $\#\{k : j \in \eta'_k\} \equiv \sum_{i : \mathrm{rep}(i) = j}
\#\{k : i \in \eta_k\}$, which is even: (h3). The scan that defines $\mathrm{domRep}(i)$ starts at
$i$ and moves only to cities that dominate $i$. Costs and loads are sums over the landings. $\square$

**Proposition 6.6 (dominance, non-symmetric).** Let $\mathrm{rep}$ satisfy $d_{\mathrm{rep}(i)} \le
d_i$, $\bar d_{\mathrm{rep}(i)} \le \bar d_i$ and $c_{\mathrm{rep}(i)} \le c_i$ for every $i$
($\mathrm{domRep3}$, the first city in the order $(d, \bar d, c, \text{index})$ among those that dominate
$i$, is one). Replacing every city by its image maps a role configuration to one with the same number of
landings, no larger cost and no larger role loads, and a valid scheduled configuration to a valid one
with the same number of landings, no larger cost and no larger $M_{\rm tmpl}$.

*Lean:* `domRep3`, `domRep3_le`, `RoleConfig.map`, `RoleConfig.size_map`, `RoleConfig.totalCost_map_le`,
`RoleConfig.roleLoad_map_le` (LagrangianBound.lean); `Sched.map`, `Sched.Valid.map`, `Sched.size_map`,
`Sched.cost_map_le`, `Sched.tmpl_map_le` (SchedMap.lean).

*Proof.* The image of the balance is a balance, oddness is kept, and a matched drop-off and pick-up at
one city are sent to one city, with the matching unchanged. Costs, role loads, $\mathrm{Pre}$,
$\mathrm{Suf}$ and the link terms are sums of $d$, $\bar d$ and $c$ over the cities, termwise no larger.
$\square$

**Theorem 6.7 (link-forest DP).** Fix $1 \le p$ and a level $T \le T_{\max}$. The *link labels* are the
cities in the image of $\mathrm{domRep}$. The tables, for $\tau \in [0, T]$ and odd $r \ge 1$, are:

* $\mathrm{Ch}_q[\tau][j]$: the least cost of a multiset of *child items*, each a link label $b$, with
  one copy of $b$ in the parent's group, and a subtree hanging from it; the labels' durations sum to
  $\tau$, the subtrees have $q$ planes, and $j$ counts one landing per item plus the subtrees'
  landings. $\mathrm{Ch}_0[0][0] = 0$ and the other entries of $\mathrm{Ch}_0$ are $\infty$; for $q \ge
  1$, $\mathrm{Ch}_q[\tau][j] = \min_{b,\ 1 \le q' \le q,\ j'} \big(\mathrm{Ch}_{q-q'}[\tau - d_b][j - 1
  - j'] + c_b + \mathrm{Sub}_b[q'][j']\big)$;
* $\mathrm{Sub}_b[q][j]$: the least cost of a subtree with $q$ planes and $j$ landings whose root holds
  one copy of $b$ for its parent link, $\mathrm{Sub}_b[q][j] = \min_{\tau,\ j' + 1 + r = j}\big(c_b +
  \mathrm{Ch}_{q-1}[\tau][j'] + G[r][T - d_b - \tau]\big)$;
* $\mathrm{Root}[q][j] = \min_{\tau,\ j' + r = j}\big(\mathrm{Ch}_{q-1}[\tau][j'] + G[r][T - \tau]\big)$,
  the least cost of a tree with $q$ planes and $j$ landings;
* $\mathrm{For}[0][0] = 0$ and $\mathrm{For}[P][J] = \min_{1 \le q \le P,\ j}\big(\mathrm{For}[P -
  q][J - j] + \mathrm{Root}[q][j]\big)$, the least cost of a forest with $P$ planes and $J$ landings.

Then $\mathrm{For}[p][s] = E(T)$.

*Lean:* `TreeData`, `TreeData.chEntry`, `TreeData.subEntry`, `TreeData.rootEntry`, `TreeData.forEntry`,
`TreeData.value`, `repList`, `treeBoundAt`, `treeBoundAt_le_totalCost` (TreeBound.lean);
`TreeData.attained_ch_sub`, `TreeData.attained_root`, `TreeData.attained_for`, `treeBoundAt_eq_minCost`
(TreeExact.lean).

*Proof.* ($\ge$) By induction on the number of planes, every finite entry is the cost of child items, a
subtree, a tree or a forest with these parameters, whose groups have loads at most $T$ and whose free
landings are cheapest multisets of Lemma 6.1. The forest behind $\mathrm{For}[p][s]$ satisfies (F2) and
has $p$ planes and $s$ landings, so its groups form an admissible partition by Lemma 2.6, and
$\mathrm{For}[p][s] \ge E(T)$.

($\le$) Take $X$ attaining $E(T)$. By Proposition 6.5 its image under $\mathrm{domRep}$ is admissible,
with the same sizes, no larger cost and no larger loads. Take a link forest of the image (Lemma 2.6); its
labels are link labels. By induction on the subtrees: the child items of a plane $u$ cost at least
$\mathrm{Ch}_{q}[\tau_u][j']$, with $\tau_u$ the duration of its child labels (remove one item and bound
its subtree by $\mathrm{Sub}_b$); the free landings of $u$, an odd number $r_u$, have duration at most
$T - \tau_u$, less $d_b$ for a hanging root, so they cost at least the matching entry of $G$. So the
forest costs at least $\mathrm{For}[p][s]$. $\square$

**Theorem 6.8 (σ-DP).** Let $1 \le p \le t$, $w = \min(p - 1,\ t - p)$ and $T \le T_{\max}$. Process the
planes in order, with states $(k, j, \sigma)$: $k$ planes processed, $j$ landings used, $\sigma$ a set of
at most $w$ cities in the image of $\mathrm{domRep}$. A plane option $(m, H)$, with $H$ such a set,
$|H| + 1 \le m$, $|H| \equiv m + 1 \pmod 2$ and $\delta(H) \le T$, costs $c(H) + G[m - |H|][T -
\delta(H)]$; it adds $m$ to $j$ and replaces $\sigma$ by $\sigma \triangle H$, which must have at most $w$
cities. The least cost of a path from $(0, 0, \emptyset)$ to $(p, s, \emptyset)$ is $E(T)$.

*Lean:* `groupOption`, `groupOption_le_cost`, `sigmaDP`, `sigmaDP_le`, `sigmaBoundAt`,
`sigmaBoundAt_le_totalCost` (AdmissibleBound.lean); `sigmaDP_attained`, `groupOption_attained`,
`isParityWitness_of_list`, `sigmaBoundAt_eq_minCost` (Solver.lean).

*Proof.* ($\ge$) Along a path, let plane $k$ take its set $H_k$ and a cheapest multiset of $m_k - |H_k|$
cities within $T - \delta(H_k)$. Its group $X_k$ contains $H_k$ and $|H_k| \equiv |X_k| + 1$; the path
ends at $\sigma = H_1 \triangle \dots \triangle H_p = \emptyset$, so every city lies in an even number of
the $H_k$. So the sets $H_k$ form a parity matrix, and the path's cost is that of an admissible partition
with loads at most $T$.

($\le$) Take $X$ attaining $E(T)$ and its image under $\mathrm{domRep}$, admissible with $|X| = s$ and
no larger cost or loads (Proposition 6.5). By Lemma 2.7 it has a parity matrix $\eta$ touching at most
$w$ cities, all in the image of $\mathrm{domRep}$. Every prefix $\eta_1 \triangle \dots \triangle \eta_k$
lies in $Z(\eta)$, and so does every $\eta_k$, so all have at most $w$ cities. By Lemma 2.4, $|\eta_k| +
1 \le |X_k|$, and $X_k - \eta_k$ costs at least $G[|X_k| - |\eta_k|][T - \delta(\eta_k)]$. So the options
$(|X_k|, \eta_k)$ form a path of cost at most $c(X)$. $\square$

**Theorem 6.9 (verified solver, H2).** Assume (S), (H) and $1 \le p \le t$. The list
`solveFront d c t p` is the Pareto front of the feasible plans. The solver lists, by increasing
makespan, the points $(E(T), 2T)$ at which $E$ drops, found by splitting intervals of the levels
$d_{\min}\lceil s/p\rceil, \dots, (2t - p)\,d_{\max}$; at each level it evaluates $E(T)$ as $L(T)$ where
$L(T) = U_2(T)$, and otherwise by the link-forest DP or the σ-DP, whichever its cost estimate prefers.

*Lean:* `solveFront`, `solveFront_eq`, `mem_solveFront_iff`, `solveFront_isParetoFront_hub`, `useTreeDP`
(Solver.lean, TreeBound.lean); `scanFront`, `mem_scanFront`, `scanFront_pairwise`, `splitFront_eq`,
`breakpoints_eq_scanFront` (Breakpoints.lean). Corollaries: `solveFront_isParetoFront` under (A1) and
`solveFront_isParetoFront_ATri` under (AΔ) (Solver.lean).

*Proof.* At every level the value the solver uses is $E(T)$, by Proposition 6.4 and Theorems 6.7 and
6.8. $E$ is non-increasing (Lemma 6.2), so if it takes the same value at the ends of an interval it is
constant on it, and splitting intervals finds the same points as scanning every level from 0 to $(2t -
p)\,d_{\max}$; by Lemma 6.2 no point is lost below $d_{\min}\lceil s/p\rceil$ or above $(2t - p)\,
d_{\max}$. The scan keeps $(E(T), 2T)$ whenever $E(T)$ is below every earlier value, so its points are
those of Proposition 6.3, the points of $\mathrm{Min}\,\mathcal P = \mathcal F$ (Theorem 4.5), and they
increase in makespan and decrease in cost, so they are pairwise incomparable. Every listed point is
achieved (Theorems 4.5 and 4.1). A feasible plan of cost $C$ and makespan $M$ gives, by Theorem 4.4, an
admissible partition with loads at most $T = \lfloor M/2 \rfloor$, so $E(T) \le C$. Let $T_1 \le T$ be
the least level with $E(T_1) \le E(T)$; then $E(T_1) = E(T)$ and $E$ drops at $T_1$, so $(E(T), 2T_1)$
is listed, and it weakly dominates $(C, M)$. $\square$

`lake exe zeno-front` runs this solver. The C++ solver `zeno` is not verified; its fronts are checked
through certificates (§8).

## 7. Complexity

$M(X)$ is the least $2\max_k \delta(X_k)$ over the admissible partitions of $X$ into $p$ groups, as in
Theorem 4.5.

**Theorem 7.1 (3-Partition reduction).** Let $a_1, \dots, a_{3m}$ and $B$ be natural numbers with
$\sum_i a_i = mB$ and $B/4 < a_i < B/2$ for every $i$. In the symmetric instance with one city of
duration $a_i$ for each $i$, $p = m$ planes and $t = 2m$ passengers (so $s = 3m$), the multiset $X$ that
lands once at every city has $M(X) \le 2B$ iff the $a_i$ split into $m$ triples of sum $B$.

*Lean:* `threePartition_iff`, `admissible_iff_odd_of_disjoint` (Complexity.lean); `minMakespan`
(Achievability.lean).

*Proof.* Every city lies in one group, so by Lemma 2.3 a partition of $X$ is admissible iff all its groups
are odd. A split into triples of sum $B$ is a partition into odd groups of load $B$, so $M(X) \le 2B$.
Conversely, $X$ has an admissible partition (any $m$ groups of three cities), so $M(X) \le 2B$ is
attained by an admissible partition with every load at most $B$. The loads
sum to $mB$, so each is $B$. A group of one or two cities has load below $B$, as $a_i < B/2$, and a
group of four or more has load above $B$, as $a_i > B/4$. So every group is a triple of sum $B$.
$\square$

**Proposition 7.2 (Partition reduction, $p = 2$).** Let $a_1, \dots, a_m$ be natural numbers with sum
$2B$, $r \ge m$ odd and $K = B + 1$. In the symmetric instance with $2r$ cities, of durations $a_i + K$
for $i \le m$ and $K$ for the other $2r - m$, $p = 2$ and $t = r + 1$ (so $s = 2r$), the multiset $X$
that lands once at every city has $M(X) \le 2(B + rK)$ iff some sub-multiset of the $a_i$ sums to $B$.
All durations are positive.

*Lean:* `partitionDur`, `partitionDur_pos`, `partition_iff` (Complexity.lean).

*Proof.* By Lemma 2.3, a partition of $X$ is admissible iff both groups are odd. The loads sum to $2B +
2rK$. If the $a_i$ with $i \in S$ sum to $B$, put the cities of $S$ and $r - |S|$ cities of duration $K$
in one group and the other $r$ cities in the other ($|S| \le m \le r$, and there are $2r - m \ge r - |S|$
cities of duration $K$): two odd groups of load $B + rK$. Conversely, an admissible partition with both
loads at most $B + rK$ has both loads equal to $B + rK$. A group of $r + 1$ cities or more has load at
least $(r + 1)K > B + rK$, so both groups have $r$ cities, and the $a_i$ of the first sum to $B$.
$\square$

**Theorem 7.3 (step count).** In the cost model below:

(a) at every level $T$, the link-forest DP of Theorem 6.7 with a step counter returns the value of the
DP, which is $E(T)$ when $1 \le p$, $T \le T_{\max}$ and the table is that of Lemma 6.1, in at most
$P(n, t, p, T) = 30\,(n + 1)^2(p + 1)^2(t + 1)^2(T + 1)$ steps, whatever table it reads;

(b) with $1 \le p \le t$, building the one-plane table once for the levels $0, \dots, T_{\rm top} = (2t -
p)\,d_{\max}$ and running the counted DP at each of them returns `solveFront d c t p`, the list of
Theorem 6.9, in at most $(T_{\rm top} + 1)\,P(n, t, p, T_{\rm top})$ steps, the table included.

A step is one iteration of a minimum loop, one cell of a table, one element scanned by a membership
test, or one level of the scan; computing the $n$ link labels costs $n^2$ steps, and testing them $n^2$
more; constant-time work outside loops is free.

*Lean:* `treeBoundSteps`, `treeBoundSteps_value`, `treeBoundSteps_eq_minCost`,
`treeBoundSteps_le_levelBound`, `treeBoundSteps_le`, `stepBound`, `scanSteps`, `scanSteps_fst`,
`scanSteps_le` (Complexity.lean).

*Proof.* The counted functions are those of Lemma 6.1 and Theorem 6.7 line for line, with every loop
counting its iterations; each returns its value and its number of steps, and the value equals the
uncounted one, by induction on the tables. With $R \le n$ labels, $S$ landings, $P$ planes and level $T$,
one level, the link labels included, takes at most $7\,(P + 1)^2(n + 1)^2(T + 1)(S + 2)^2$ steps, by
counting the cells of $\mathrm{Ch}$, $\mathrm{Sub}$, $\mathrm{Root}$ and $\mathrm{For}$ and the iterations
of their minima; with $S = 2t - p$ this is at most $P(n, t, p, T)$, which gives (a). For (b), the scan returns the breakpoints of $E$ on the levels $0, \dots, T_{\rm top}$, which is
`solveFront d c t p` (proof of Theorem 6.9). The one-plane table takes at most $(s + 1)(T_{\rm top} +
1)(n + 1)$ steps; each level takes at most the per-level bound at $T_{\rm top}$, which grows with $T$,
plus one step; and the sum is at most $(T_{\rm top} + 1)\,P(n, t, p, T_{\rm top})$. $\square$

*Remark (hardness, from the literature).* 3-Partition is strongly NP-complete and Partition is
NP-complete (Garey & Johnson, *Computers and Intractability*, 1979). The instance of Theorem 7.1 has the
numbers $a_i$, $B$ and $m$ of the 3-Partition instance, and both instances are written down in polynomial
time; granted these cited results, deciding $M(X) \le 2T$ is therefore strongly NP-hard when $p$ is part
of the input, by Theorem 7.1, and stays NP-hard for $p = 2$, by Proposition 7.2. By Theorem 7.3, by contrast,
$E(T)$ and the front take a number of steps polynomial in $n$, $t$, $p$ and the largest level $(2t -
p)\,d_{\max}$: pseudo-polynomial in the durations. In particular, unless P = NP, no polynomial algorithm,
such as a greedy, computes $M(X)$ for every multiset $X$. The hardness results are cited, not
formalised.

## 8. Certificates

`zeno --certificate FILE` writes, next to a front, a certificate that a checker verifies without
trusting the solver. The format is `doc/certificate-format.md`. Two checkers read it: `zeno check` (C++,
the reference reader) and the Lean checker `lake exe zeno-check`, whose soundness is proved below. A
certificate lists the assumptions it is claimed under; both checkers reject one that lists an
assumption other than `S`, `A1`, `A1|AD` and `A1-NS` (in Lean in the parser, `Parse.knownAssumptions`,
outside the verified `check`). A central table is not part of a certificate, so no checker tests it: the
soundness theorems quantify over the tables.

**Theorem 8.1 (obligations imply the front).** Let $\mathcal S \subseteq \mathbb N^2$ and $(C_1, M_1),
\dots, (C_r, M_r)$, $r \ge 1$, with $M_1 < \dots < M_r$ and $C_1 > \dots > C_r$. If (1) every listed point
is in $\mathcal S$, (2) every point of $\mathcal S$ has makespan at least $M_1$, (3) for $i < r$ every
point of $\mathcal S$ with makespan below $M_{i+1}$ has cost at least $C_i$, and (4) every point of
$\mathcal S$ has cost at least $C_r$, then the list is the Pareto front of $\mathcal S$.

*Lean:* `isParetoFront_of_obligations`, `exists_le_of_chain` (Checker.lean).

*Proof.* Let $y \in \mathcal S$. By (2), $M_1 \le y_2$. Along the list, if $y_2 < M_{i+1}$ for the first
$i$ such that this holds, then $(C_i, M_i) \le y$ by (3) and since $M_i \le y_2$; if no such $i$ exists,
$(C_r, M_r) \le y$ by (4). The listed points lie in $\mathcal S$ by (1), and the strict monotonicity
makes them pairwise incomparable. $\square$

*Format v1* (symmetric instances). The header gives $n, t, p$, $d$, $\bar d$ and $c$; the checker requires
$1 \le n$, $1 \le p \le t$, $d = \bar d$ and the assumption `S`. The points are strictly increasing in
makespan and strictly decreasing in cost, each with a plan, and each gap $i < r$ names a kind. The checker
verifies:

1. each plan by simulation: every leg a hub flight of the right duration (no central legs), every
   plane's legs a route from $C_I$ at time 0 ending in $C_G$, every passenger followed from $C_I$ along
   the earliest legs that carry it, using all of them and ending in $C_G$; and its cost and makespan;
2. $M_1 = 2d_{\min}\lceil s/p\rceil$;
3. for each gap $i$, a bound at least $C_i$ at the level $T^\star_i = \lfloor\lfloor(M_{i+1} -
   1)/2\rfloor/g\rfloor$ of the instance with durations divided by their gcd $g$: for `relaxed`, the
   relaxation $L(T^\star_i)$; for `forest`, $E(T^\star_i)$ by the link-forest DP or the σ-DP, whichever
   its estimate prefers, only if the assumption `A1` is listed (`zeno check` also accepts `A1|AD`);
4. $C_r = s\,c_{\min}$.

**Theorem 8.2 (v1 checker, H3).** If `Cert.check` accepts a certificate of format v1, its points are the
Pareto front of the feasible plans of its instance for every central table satisfying (H), and for every
central table if all its gaps are `relaxed`. The same holds for the plans with times in any ordered ring
with a floor function, such as $\mathbb Q$ or $\mathbb R$ (Lemma 1.3), and, for every table satisfying
(H), for the plans whose planes end anywhere.

*Lean:* `Cert`, `Cert.check`, `Cert.gapLevel`, `Cert.gapBound_le`, `Cert.forestGapBound_le_hub`,
`Cert.check_sound_hub`, `Cert.check_sound_relaxed` (Checker.lean); `planOK`, `planOK_feasible`
(Simulate.lean); `load_eq_scale_mul` (Relaxation.lean); `forestBoundAt`, `forestBoundAt_le_totalCost`
(TreeBound.lean); `Cert.check_sound_rat_hub` (RationalPlans.lean); `Cert.exists_le_of_admissible`,
`Cert.check_sound_anywhere_hub` (Bridge.lean). Corollaries: `Cert.check_sound`, `Cert.check_sound_A1` under (A1) and
`Cert.check_sound_ATri` under (AΔ) (Checker.lean).

*Proof.* A plan that the simulation accepts is feasible for every central table: it flies hub flights
only, and following each passenger along the earliest legs exhibits the route of item 3 of Definition
1.2. This is obligation (1) of Theorem 8.1 for $\mathcal S = \mathcal A$. Obligations (2) and (4) are
Proposition 3.6. For (3), let a feasible plan have makespan $M < M_{i+1}$. For a `relaxed` gap, Lemma 3.5
(under (S)) gives groups with $2\delta(Y_k) \le M$; for a `forest` gap under (H), Theorem 4.4 gives an
admissible partition with $2\delta(X_k) \le M$. Durations are multiples of $g$, so the loads in units of
$g$ are at most $\lfloor\lfloor (M_{i+1} - 1)/2\rfloor / g\rfloor = T^\star_i$, and the bound at that level
(Lemma 3.5, Proposition 6.4, Theorems 6.7 and 6.8) is at most the plan's cost. Theorem 8.1 concludes;
the Lean proof runs its argument along the gaps (`exists_le_of_gapsOK`). For times in $\mathbb K$:
rounding down maps a plan to an integer plan of the same cost and no larger makespan, and integer plans
are plans with times in $\mathbb K$ (Lemma 1.3). For planes ending anywhere: a feasible plan is a plan
of the variant, and every plan of the variant gives an admissible partition of $s$ landings with cost at
most its cost and loads $2\delta(X_k)$ at most its makespan (proof of Theorem 4.5). The obligations bound
such a partition directly: some group has at least $\lceil s/p\rceil$ landings, its $s$ landings cost at
least $s\,c_{\min}$, and the gap bounds are lower bounds on admissible partitions. So a listed point
weakly dominates the plan's point. $\square$

*Format v2* (non-symmetric instances). The header is `zeno-certificate 2`, and $\bar d$ may differ from
$d$; `S` may be listed only if $d = \bar d$. Levels are full loads in units of the gcd $g$ of the weights:
a plan of makespan below $M$ fits in level $\lfloor (M - 1)/g\rfloor$. A line `fastest <kind>` names the
bound that rules out plans faster than $M_1$: the checker accepts $M_1 = 0$ (whatever the kind), the
closed form of v1 (`closed`, symmetric instances only), or a bound of kind `relaxed`, `roles`, `balanced`
or `search` that is $\infty$ at the level of $M_1$. Obligations 1 and 4 are those of v1. The kinds:

* `relaxed`: the relaxation $L_e$ with the weight $2e_i = 2\min(d_i, \bar d_i)$ per landing (Lemma 3.5),
  under no assumption;
* `roles`, `lagrangian` $\mu_1 \dots \mu_n$, `balanced` and `search`, under (A1-NS), which the
  certificate must list. They are computed on the representatives of $\mathrm{domRep3}$ (Proposition
  6.6), with durations divided by the gcd of their $d$ and $\bar d$; a city that is not a representative
  is given a weight above every budget;
* `forest` is read, but the Lean v2 checker gives it no bound, so it never accepts a `forest` gap.

**Proposition 8.3 (`roles` bound).** At level $T$, the `roles` bound is the larger of (A) the plane-by-plane
relaxation in which a plane's $m$ landings contain an odd number of crossings, of weight $d + \bar d$,
the others weighing $2\min(d, \bar d)$, all within $T$, combined over the planes as in Lemma 3.5, and (B)
$G_{d + \bar d}[s][pT]$, the least cost of $s$ landings of weight $d + \bar d$ within $pT$. It is at most
the cost of every role configuration with $s$ landings and every $\lambda_k \le T$.

*Lean:* `fillW`, `lowW`, `roleM`, `roleM_le`, `rolesBoundAt`, `sum_roleLoad_eq_load_fill`,
`rolesBoundAt_le_totalCost` (RoleBound.lean); `Cert2.exists_repConfig`, `Cert2.rolesWith_le`
(CheckerV2.lean).

*Proof.* (A) In plane $k$'s group, the $|\mathrm{Cr}_k|$ crossings, an odd number, weigh $d + \bar d$
each in $\lambda_k$, and a drop-off or a pick-up weighs $2d$ or $2\bar d$, at least $2\min(d, \bar d)$. So
the group is one of the multisets over which the per-plane table minimises, and the planes combine as in
Lemma 3.5. (B) By the balance, $2\delta(\sum_k \mathrm{Dr}_k) + 2\bar\delta(\sum_k \mathrm{Pk}_k) =
(\delta + \bar\delta)(\sum_k \mathrm{Dr}_k + \sum_k \mathrm{Pk}_k)$, so $\sum_k \lambda_k = (\delta +
\bar\delta)(X) \le pT$, and $c(X) \ge G_{d + \bar d}[s][pT]$. $\square$

**Proposition 8.4 (`lagrangian` bound).** For every integer vector $\mu$, the Lagrangian value at level
$T$ (the plane-by-plane relaxation in which a drop-off at $i$ costs $c_i + \mu_i$, a pick-up $c_i -
\mu_i$, a crossing $c_i$, and every plane has an odd number of crossings and weighs at most $T$, combined
over the planes by a program over group sizes, for a given number $\ell$ of landings) is at most the cost
of every role configuration with $\ell$ landings, all in the allowed cities, whose planes weigh at most $T$, a crossing at $i$ weighing
$\mathrm{fill}_i$, a drop-off $\mathrm{drop}_i$ and a pick-up $\mathrm{pick}_i$ ($d_i + \bar d_i$, $2d_i$
and $2\bar d_i$ in the checker).

*Lean:* `LagData`, `LagData.lagM_le`, `LagData.value_le_totalCost` (LagrangianBound.lean);
`Cert2.lagWith_le` (CheckerV2.lean).

*Proof.* By the balance, $\sum_k \mu(\mathrm{Dr}_k) = \sum_k \mu(\mathrm{Pk}_k)$, so the cost of the
configuration is $\sum_k \big(c(\mathrm{Cr}_k) + \sum_{i \in \mathrm{Dr}_k}(c_i + \mu_i) + \sum_{i \in
\mathrm{Pk}_k}(c_i - \mu_i)\big)$. Each plane's term is at least the per-plane minimum for its number of
landings, and the planes combine as in Lemma 3.5. $\square$

**Proposition 8.5 (`balanced` bound).** At level $T$, the imbalance-vector program (planes in order;
state: the landings used and the imbalance vector $\sum (\mathrm{Dr} - \mathrm{Pk})$ of the planes so
far, of $\ell^1$-norm at most $t - p$; a plane's option is its imbalance and an odd number of crossings,
a drop-off and a pick-up at one city of one plane counting as two crossings there) has value at most the
cost of every role configuration with $s$ landings and every $\lambda_k \le T$, for the weights and the
crossing table that the checker builds.

*Lean:* `BalData`, `RoleConfig.planeOpts`, `BalData.layers_dominate`, `RoleConfig.norm_prefix_le`,
`BalData.value_le_totalCost` (BalancedBound.lean); `Cert2.balWith_le` (CheckerV2.lean).

*Proof.* A drop-off and a pick-up at $x$ on one plane weigh $2d_x + 2\bar d_x$ and cost $2c_x$, as two
crossings at $x$, so a plane's roles are an option of the program with no larger cost; the crossings
stay odd. Let $N$ be the number of remaining links; $2N + p \le s$, so $N \le t - p$. For a prefix of
planes and a city $i$, the imbalance is $D^{\le}(i) - P^{\le}(i) = P^{>}(i) - D^{>}(i)$ by the balance,
so its absolute value is at most the drop-offs at $i$ of the prefix or of the other planes, and the norm
of the prefix's imbalance is at most $N$. So every prefix of the configuration is a state of the
program, and by induction over the planes each layer holds it at a cost no larger than the prefix's.
$\square$

**Proposition 8.6 (`search` bound).** If the exhaustive search over the scheduled configurations of cost
below $C$ (every ordered list of drop-offs, ordered list of pick-ups and multiset of crossings per plane,
with an odd number of crossings and a role load at most $T$, and every matching of the pick-ups to
drop-offs of the same city, self links included) reports the gap closed at level $T$, then every valid
scheduled configuration with $s$ landings and cost below $C$ has $M_{\rm tmpl} > T$.

*Lean:* `SearchData`, `SearchData.opts`, `SearchData.tuples`, `SearchData.assignments`,
`SearchData.closed`, `SearchData.closed_sound` (SearchGap.lean); `Sched.mul_tmpl_map_le` (SchedMap.lean);
`Cert2.searchWith_le` (CheckerV2.lean).

*Proof.* Let $S$ be valid with $s$ landings, cost below $C$ and $M_{\rm tmpl}(S) \le T$. Then every role
load is at most $T$, so every plane of $S$ is one of the enumerated options, the tuple of these options
has $s$ landings and as many drop-offs as pick-ups, and the matching of $S$ is one of the enumerated
assignments. The closed form of that tuple and assignment is $M_{\rm tmpl}(S) \le T$, so the search would
not report the gap closed. $\square$

**Theorem 8.7 (v2 checker, H3).** If `Cert2.check` accepts a certificate of format v2, its points are the
Pareto front of the feasible plans of its instance, for every central table that satisfies (A1-NS) if the
certificate lists `A1-NS`, and for every central table otherwise.

*Lean:* `Cert2`, `Cert2.check`, `Cert2.fastestOK`, `Cert2.relaxedWith_le`, `Cert2.exists_repConfig`,
`Cert2.rolesWith_le`, `Cert2.lagWith_le`, `Cert2.balWith_le`, `Cert2.searchWith_le`,
`Cert2.check_sound` (CheckerV2.lean).

*Proof.* Obligation (1) of Theorem 8.1 is the simulation, as in Theorem 8.2, and (4) is Proposition 3.6,
which needs no assumption. For (2) and (3), let a feasible plan have makespan below $M$ and cost $C'$;
every kind's bound at the level of $M$ is at most $C'$. For `relaxed`, by Lemma 3.5. For the other kinds
(A1-NS) is listed, hence holds for the table. Corollary 5.4 gives a role configuration with $2t - p$
landings, cost at most $C'$ and role loads at most the makespan; by Proposition 6.6 its image on the
representatives keeps these properties, and it fits in the level once the durations are divided by their
gcd; Propositions 8.3, 8.4 and 8.5 bound `roles`, `lagrangian` and `balanced`. For `search`, Theorem 5.3
gives a valid scheduled configuration with cost at most $C'$ and $M_{\rm tmpl}$ at most the makespan,
mapped to the representatives by Proposition 6.6 and to the scaled durations by `Sched.mul_tmpl_map_le`;
by Proposition 8.6 its cost, hence $C'$, is at least the cost of the previous point, which is the bound
of a closed search. A first point with $M_1 = 0$ needs no bound, and `closed` is Proposition 3.6.
Theorem 8.1 concludes. $\square$

The proof covers instances with a city of $d_x = \bar d_x = 0$, as Theorem 5.3 does.

## Changes from revision 2

*Model.* §1 now describes the model that Lean encodes: natural-number durations, times and costs, with
Lemma 1.3 for rational and real times; a complete, directed central table; and the passenger condition
of Definition 1.2, item 3, without the condition that consecutive legs on one plane come later on its
route. The assumption (AΔ-path), event-ordered plans and Statement 1.2 (the PDDL correspondence) are
gone; §1.3 describes the encoding and claims nothing. The hub triangles (H) are new (Definition 1.4,
Lemma 1.5): one converse, Theorem 4.4, replaces the converses under (A1) and under (AΔ).

*Old and new numbers.* Results not listed here were removed (next table).

| Revision 2 | Revision 3 |
|---|---|
| §1.1, §1.2 (Definition (plan)), §1.4, §1.5 | Definitions 1.1, 1.2, 1.4, 1.6 |
| — | Lemma 1.3 (rounding times), Lemma 1.5 (hub triangles) |
| Lemma 1.1 | Lemma 1.7 |
| Definition 2.2 | Definition 2.1 |
| Lemma 2.3 | Lemma 2.2 |
| Lemma 2.4 | Lemma 2.3 (disjoint groups only) |
| Lemma 2.5 | Lemma 2.4 |
| Definition (link forest) | Definition 2.5 |
| Lemma 2.6 | Lemma 2.6 |
| Lemma 2.8 | Lemma 2.7 |
| Lemma 2.1 | Lemma 3.1 (on visits) |
| Lemma 3.1 | Lemma 3.2 (chains) |
| Lemma 3.2 | Lemma 3.3 |
| Lemma 3.3 | Lemma 3.4 |
| Lemma 3.4, and the `relaxed` kind of format v2 | Lemma 3.5 (weight $\min(d, \bar d)$) |
| Proposition 7.10 (a), (b), lower halves | Proposition 3.6 |
| Theorem 4.1 | Theorem 4.1 |
| Lemma 4.6 | Lemma 4.2 |
| Lemma 4.11 | Lemma 4.3 |
| Theorems 4.7 and 4.10, Conjecture 4.10 | Theorem 4.4 (under (H)) |
| Corollaries 4.8 and 4.12, Theorem 4.9 | Theorem 4.5 |
| the remark on Proposition I after Corollary 4.8 | Example 4.6 |
| Example 4.13 | Example 4.7 |
| §5 | Proposition 4.8 |
| Definition 4.2 | Definition 5.1 |
| §6.2 (orders, link matching, the closed form of Lemma 6.3) | Definition 5.2 |
| Theorem 6.9 | Theorem 5.3 |
| Theorem 6.1 | Corollary 5.4 (from Theorem 5.3) |
| Lemma 6.3 | Lemma 5.5 |
| Corollary 6.10 | Corollary 5.6 |
| Proposition 6.5, Conjecture 6.5 | Proposition 5.7 |
| §6.6 (model, reduction) | Definition 5.8 |
| Example 6.11 | Example 5.9 |
| Proposition 6.7, Conjecture 6.7 | Example 5.10 |
| Lemma 7.2 | Lemma 6.1 |
| §7.1, Proposition 7.10 (c), first half | Lemma 6.2 |
| Proposition 7.1 | Proposition 6.3 |
| Proposition 7.3 | Proposition 6.4 (without $U_3$) |
| Proposition 7.9 | Proposition 6.5 |
| the argument of Proposition 6.14 | Proposition 6.6 |
| Theorem 7.5 | Theorem 6.7 |
| Theorem 7.6 | Theorem 6.8 |
| the verified solver | Theorem 6.9 |
| Theorem 8.1 | Theorem 7.1 |
| Proposition 8.2, NP-hard half | Proposition 7.2 |
| Corollary 8.3, and the bounds of Theorem 7.5 | Theorem 7.3 |
| Theorem 9.1 | Theorem 8.1 |
| `Cert.check_sound` | Theorem 8.2 |
| — | Propositions 8.3 (`roles`) and 8.4 (`lagrangian`) |
| Proposition 6.6 | Proposition 8.5 (`balanced`) |
| — | Proposition 8.6 (`search`) |
| the version 2 checker | Theorem 8.7 |

Sections: §4.1–§4.6 and §5 of revision 2 are §4; §4.2, §6.1, §6.2 and §6.6 are §5; §7 is §6; §8 is §7;
§9 is §8.

*Removed.*

| Revision 2 | Reason |
|---|---|
| Statement 1.2 | argued, never proved; no theorem, certificate kind or solver step uses it |
| Corollary 2.7 | the link-forest DP allows trees of up to $p$ planes, so no proof needs the cap $q_{\max}$ |
| Lemma 2.9 | used only by removed parts of Proposition 7.10 and by Theorem 10.1 |
| Lemma 4.3 (direct selection) | Corollary 5.4 now follows from Theorem 5.3; no proof of this note uses it |
| Lemma 4.4 (shrinking role configurations) | the same; Theorem 5.3 shrinks inside its proof |
| Lemma 4.5 | used only by the role-route proof of Theorem 4.7, replaced by Theorem 4.4 |
| Lemma 6.2 ($L_{\rm NS}$) | implemented nowhere (revision 2's §6.5 said otherwise); no kept proof uses it |
| Corollary 6.4 | no code, certificate kind or kept proof uses it |
| Lemma 6.8 | event orders leave the model; Theorem 5.3 covers every plan |
| end of §6.2 (plans without an event order) | superseded: Theorem 5.3 holds for every plan |
| Definition 6.17, Proposition 6.18, its claim (d) | computed by search only; no kept result uses them; Example 5.10 defines what it needs |
| Lemma 6.19 | no code, certificate kind or kept proof uses it |
| Propositions 6.12–6.16 | general graphs are kept only for the refutation of Example 5.9, which needs none of them |
| Proposition 7.4 | $U$ and $U_3$ are optimisations of the C++ solver, checked by certificates; the `gadget` kind was never built |
| Lemma 7.7, Proposition 7.8 | the Pareto-set variant is used by no certificate kind, solver step or kept proof |
| Lemmas 9.2 and 9.3 | the `sigma-potential` kind was never built |
| Theorem 10.1, Conjecture 10.2 | no claims about generator families |
| Appendix A | superseded proof of Theorem 4.7 |
| §4.6, the remark on $d'$ | a remark that claimed an unused bound |
| §7.3, "Pairs are not enough" | an unnumbered claim about $U_3$ |
| §0 tables, §6.4, §6.5, §7.7, §10, §11 (evidence), §12 (next steps) | replaced by §0 above; claims outside numbered results; the experiments belong to the paper |

*Clauses dropped from kept results.* Theorem 4.1 no longer says that a plane picks up at most one
passenger. Lemma 2.3 keeps only disjoint groups, Lemma 2.6 drops "at most one edge of each label at each
plane", and Lemma 2.7 drops its parts (a) and (b). Lemma 3.2 extracts chains instead of cleaning
journeys. Lemma 3.3 drops "hence at least $s$ landings". Lemma 3.4 keeps the per-plane form with weight
$e$ and the forms under (S) and (H). Theorem 5.3 bounds the closed form $M_{\rm tmpl}$; Lemma 5.5 keeps
achievability, now exact, and drops the lower bound for other schedules; Corollary 5.6 drops the
event-ordered plans. Proposition 5.7 drops (AΔ-path) and the list of front points. Example 5.9 drops
$\mathcal F_U = \{(8, 8)\}$. Example 5.10 replaces the class bound on plans with shuttles by the
construction of arXiv:2304.14659 as printed. Proposition 6.4 drops $U_3$, Proposition 6.5 drops the
statements on $L$ and on the front, Theorem 6.7 drops the cap $q_{\max}$ and its time and memory bounds
(Theorem 7.3 now counts steps), Proposition 7.2 drops the algorithm for fixed $p$, Theorem 7.1 drops membership in NP,
and the complexity classes move to the remark after Theorem 7.3.

*Stale passages fixed.* Revision 2 placed the solver on the branch `feat/exact-front-solver` and the PDDL
writer in `src/utils.cpp`; the solver is on `master` and the writer is `src/zeno/io.cpp`. It said that
the σ-DP is a C++ method; it is the Lean solver's (Theorem 6.8). Its §6.5 said that the non-symmetric
algorithm uses $L_{\rm NS}$; no code does. Its §9 listed the kinds `gadget` and `sigma-potential`, which
were never built, and said that the checkers accept `forest` gaps under (A1) only; §8 describes the kinds
that exist, and the Lean checker is proved sound for `forest` gaps under (H), so under (A1) and under
(AΔ) (Theorem 8.2). The
`EO` assumption no longer exists, and an unknown assumption is rejected.
