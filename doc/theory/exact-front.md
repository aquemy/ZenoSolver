# Exact Pareto fronts for MultiZenoTravel: proofs, algorithm, complexity

This note closes the gaps found in the optimality arguments of Quemy & Schoenauer (EvoCOP 2015) and of
Quemy, Schoenauer & Dréo (arXiv:2304.14659, 2023). Where a gap cannot be closed yet, it is reduced to a
precise open statement, and the computational evidence for it is listed. It then specifies an exact
algorithm for the Pareto front and analyses its complexity.

The only goal is the exact Pareto front: weak dominance is enough throughout, and one plan per front point
is sufficient.

## 0. Status

| Result | Symmetric, central flights useless (A1) | Symmetric, triangle inequality only (AΔ) | Non-symmetric |
|---|---|---|---|
| At least $2t-p$ landings (Lemma 3.2) | proved | proved | proved |
| Achievability: admissible partition ⇒ plan with makespan = largest load (Thm 4.1) | proved | proved | open (waiting, §6.2) |
| Converse: every plan is weakly dominated by an admissible partition (Thm 4.3) | **proved** | open: Conjecture 4.6 | false as stated, extended Conjecture 6.4 |
| Front characterisation (Cor. 4.5) | **proved** | holds if Conjecture 4.6 holds | open |
| Exact algorithm (§7) | correct | correct if Conjecture 4.6 holds | conditional (§9) |
| Per-PPP greedy of both papers is optimal | **false** (§5) | false | false |

Evidence for the open statements (exhaustive search over *all* plans, see §10): 516 symmetric instances, 236
of them with the shortest central flights the triangle inequality allows, all matching; 11 of 140
non-symmetric instances with short central flights where the $2t-p$ model is beaten.

## 1. Model

* Cities: $C_I$ (initial), $C_G$ (goal), central cities $1,\dots,n$.
* Flights: $C_I \leftrightarrow i$ of duration $d_i \ge 0$, $i \leftrightarrow C_G$ of duration $\bar d_i \ge 0$,
  $i \leftrightarrow j$ of duration $d_{ij} \ge 0$. There is no flight between $C_I$ and $C_G$.
* Costs: landing in central city $i$ costs $c_i \ge 0$; $C_I$ and $C_G$ are free.
* $p$ planes and $t \ge p$ passengers start in $C_I$. A plane carries at most one passenger. Boarding and
  leaving a plane take no time; planes and passengers may wait anywhere.
* A plan is feasible if every passenger ends in $C_G$ **and every plane ends in $C_G$**.
* Objectives: cost (sum of landing costs) and makespan (time at which the last plane reaches $C_G$ for
  the last time). The front $\mathcal F$ is the set of non-dominated (cost, makespan) pairs.

Assumptions, used only where stated:

* (S) symmetry: $d_i = \bar d_i$ for all $i$.
* (AΔ) triangle inequality over $\{C_I, C_G, 1,\dots,n\}$ for the flights that exist, e.g.
  $d_i \le d_j + d_{ij}$ and $\bar d_i \le \bar d_j + d_{ij}$.
* (A1) central flights are useless: $d_{ij} \ge d_i + d_j$ under (S). This is the EvoCOP 2015 assumption
  (stated there with $>$). Under (A1), (AΔ) is not needed.

Notation: $s = 2t - p$. For a multiset $Y$ of central cities, $c(Y) = \sum_{w \in Y} c_w$,
$\delta(Y) = \sum_{w\in Y} d_w$ and, under (S), the *load* $\ell(Y) = 2\delta(Y)$.

## 2. Segments, patterns and admissible partitions

**Segments.** Split each plane's route at every visit to $C_I$ or $C_G$. Each piece is a *segment*; it
contains at least one central city, since there is no flight $C_I$–$C_G$. A segment is of type

* $A$: $C_I \to \dots \to C_G$, &nbsp; $\bar A$: $C_G \to \dots \to C_I$,
* $B$: $C_I \to \dots \to C_I$, &nbsp; $\bar B$: $C_G \to \dots \to C_G$.

A segment is *simple* if it lands in exactly one central city. Simple segments are the four patterns of the
papers with multiplicity 0.

**Lemma 2.1.** For every plane, $\#A - \#\bar A = 1$.

*Proof.* The plane starts in $C_I$, ends in $C_G$, and only $A$ and $\bar A$ change side. $\square$

**Admissible partition.** A partition of a multiset $X$ into $p$ non-empty groups $X_1,\dots,X_p$ (one per
plane) is *admissible* if, in the bipartite graph $H$ with an edge between plane $k$ and city $i$ whenever
$i \in X_k$, every connected component contains an even number of planes $k$ with $|X_k|$ even. Planes with
$|X_k|$ even are called *even planes*.

**Lemma 2.2 (T-joins).** Let $T$ be the set of even planes. The partition is admissible if and only if $H$
contains a $T$-join: a set $J$ of edges in which every plane of $T$ has odd degree and every other vertex
(plane or city) has even degree. If one exists, one exists inside any spanning forest of $H$.

*Proof.* Standard. On a tree, put the edge between $v$ and its parent in $J$ exactly when the subtree of $v$
contains an odd number of $T$-vertices; this works iff the tree contains an even number of $T$-vertices.
Conversely, the degrees of a $T$-join sum to an even number in every component. $\square$

**Lemma 2.3.** In a forest $T$-join, every plane $k$ has degree $h_k \le |X_k| - 1$, and
$h_k \equiv |X_k| + 1 \pmod 2$.

*Proof.* The parity is the definition. Since $H$ is a simple graph,
$h_k \le |\mathrm{supp}(X_k)| \le |X_k|$, and $h_k = |X_k|$ is excluded by parity. $\square$

## 3. Lemmas valid in every setting

**Lemma 3.1 (cleaning).** Every feasible plan can be modified, without changing any flight, cost or time,
so that each passenger leaves $C_I$ exactly once and reaches $C_G$ exactly once.

*Proof.* Let $\tau_1$ be the last departure of passenger $\pi$ from $C_I$ and $\tau_2$ its first arrival in
$C_G$ after $\tau_1$. Remove $\pi$ from every flight outside $[\tau_1,\tau_2]$: it waits in $C_I$ before and
stays in $C_G$ after. Capacity only gets looser, and flights are unchanged. $\square$

**Lemma 3.2 (counting).** A feasible plan has at least $s = 2t - p$ segments, hence at least $s$ landings.

*Proof.* After cleaning, each passenger leaves $C_I$ on the first flight of an $A$ or $B$ segment, and each
such flight carries at most one passenger, so $\#A + \#B \ge t$. Symmetrically, $\#A + \#\bar B \ge t$. By
Lemma 2.1, summed over planes, $\#A - \#\bar A = p$. Hence
$\#A + \#\bar A + \#B + \#\bar B = (\#A + \#B) + (\#A + \#\bar B) - (\#A - \#\bar A) \ge 2t - p$. $\square$

**Lemma 3.3 (segment duration).** Under (AΔ), a segment that lands in city $w$ lasts at least
$d_w + \bar d_w$ (types $A$, $\bar A$), $2d_w$ (type $B$) or $2\bar d_w$ (type $\bar B$). Under (S), at least
$2d_w$ in every case.

*Proof.* Shortcut the route on both sides of $w$ with the triangle inequality. $\square$

## 4. Symmetric case

### 4.1 Achievability

**Theorem 4.1.** Assume (S). For every multiset $X$ with $|X| = s$ and every admissible partition
$X_1,\dots,X_p$, there is a feasible plan of cost $c(X)$ and makespan $\max_k \ell(X_k)$.

*Proof.* Take a forest $T$-join $J$ of $H$ (Lemma 2.2), with each tree rooted at a plane.

*Links.* At every city $i$, the $J$-degree is even. List the planes joined to $i$ by $J$: first the parent
of $i$ if its edge is in $J$, then the children. Pair them consecutively. Each pair $(u,v)$ is a *link at
$i$*: $u$ will drop a passenger at $i$ (pattern $B$) and $v$ will pick it up (pattern $\bar B$).

A plane is a child of exactly one city, and it is the second element of a pair only at that city, so every
plane picks up at most once. Each link uses one landing of $i$ from $X_u$ and one from $X_v$; these are
distinct because $J$ has at most one edge per (plane, city). By Lemma 2.3, plane $k$ keeps
$c_k = |X_k| - h_k \ge 1$ landings, an odd number.

*Schedule of plane $k$.*

1. All its drop-offs, one after the other from time 0: $C_I \to i \to C_I$, dropping one passenger at $i$.
   These never wait.
2. Its $c_k$ remaining landings as alternating crossings $A, \bar A, A, \dots, A$, each $A$ carrying one
   passenger from $C_I$. These never wait.
3. At most one pick-up: $C_G \to i \to C_G$.

*Timing.* Let $D_u$ be the duration of phase 1 of plane $u$. A drop-off at $i$ by $u$ happens at time
$\le D_u - d_i$. Plane $v$ reaches $C_G$ at $D_v + C_v$ (phase 2 has length $C_v$) and arrives at $i$ at
$D_v + C_v + d_i$. It leaves $i$ at the later of that and the drop-off, and is back at time
$\max(D_v + C_v + d_i,\ \text{drop}) + d_i \le \max(\ell(X_v),\ D_u) \le \max(\ell(X_v), \ell(X_u))$.
A plane without a pick-up finishes at $\ell(X_k)$. Every plane flies for $\ell(X_k)$, so the makespan is
exactly $\max_k \ell(X_k)$.

*Passengers.* With $L$ links, the crossings number $s - 2L$. Each plane makes one more $A$ than $\bar A$, so
$\#A = (s - 2L + p)/2 = t - L$, and $\#A + L = t$ passengers leave $C_I$, all of them delivered. Every plane
ends in $C_G$. The landings are exactly $X$. $\square$

This is the papers' rule ("western parts of P3 early, eastern parts late"), made precise by the forest: the
forest guarantees at most one pick-up per plane, which is what makes the timing argument work.

### 4.2 Converse under (A1)

**Theorem 4.3.** Assume (S) and (A1). For every feasible plan $P$ of cost $C$ and makespan $M$, there is
a multiset $X$ with $|X| = s$ and an admissible partition with $c(X) \le C$ and
$\max_k \ell(X_k) \le M$.

*Proof.* Clean $P$ (Lemma 3.1).

**Step 1: remove central flights.** Replace a flight $a \to b$ between central cities by $a \to C_G \to b$.
This takes $d_a + d_b \le d_{ab}$ by (S) and (A1). The plane then waits at $b$ until its original arrival
time, so every later event is unchanged. A passenger on board is delivered to $C_G$ early, and its later
moves are cancelled. Landings, cost and makespan are unchanged. Repeating this gives a plan whose segments
are all simple; call it $P_1$.

**Step 2: abstraction.** Let $P_1$ have, per plane $k$, segments $\sigma$ with type, city $x(\sigma)$ and
duration $\tau(\sigma) \ge 2d_{x(\sigma)}$. Plane $k$'s flight time is
$F_k = \sum_{\sigma \in k} \tau(\sigma) \le M$.

For each passenger $\pi$, let $o(\pi)$ be the segment carrying it out of $C_I$ (type $A$ or $B$) and
$n(\pi)$ the segment delivering it (type $A$ or $\bar B$). These maps are injective. Either $o(\pi) = n(\pi)$
(an $A$ carrying $\pi$ through), or $x(o(\pi)) = x(n(\pi))$: segments are simple and passengers never return
to $C_I$, so $\pi$ is handed over at that city. Call the latter a *hand-off*.

These data form a *configuration*. Only they are used from now on (no timing), and every rewriting below
keeps $c$ and every $F_k$ from increasing.

**Step 3: normal form.** Apply the following rules while possible:

* N1: delete a $B$ segment that is no $o(\cdot)$.
* N2: delete a $\bar B$ segment that is no $n(\cdot)$.
* N3: if an $A$ segment is $o(\pi)$ with a hand-off but is no $n(\cdot)$, set $n(\pi) :=$ that segment.
* N4: if an $A$ segment is $n(\pi)$ with a hand-off but is no $o(\cdot)$, set $o(\pi) :=$ that segment.
* N5: if plane $k$ has a $B$ segment $\beta = o(\pi)$ and none of its $A$ segments is an $o$ or an $n$:
  delete $\beta$ and one $A$ segment, add an $A$ segment through $x(\beta)$ with duration $\tau(\beta)$, and
  set $o(\pi) = n(\pi) :=$ it.
* N6: the same as N5 with a $\bar B$ segment $= n(\pi)$, the new duration being $\tau(\bar\beta)$; this needs
  (S).

N1, N2, N5 and N6 lower the number of segments; N3 and N4 keep it and lower the number of hand-offs. So the
process terminates. Lemma 2.1 is preserved, $o$ and $n$ stay injective, and cost and budgets do not
increase.

In normal form:

* every $B$ is the $o$ of a hand-off and every $\bar B$ the $n$ of a hand-off;
* every $A$ is *through* ($o(\pi) = n(\pi)$), a *swap* ($o$ of one hand-off and $n$ of another, at its
  city) or *empty*;
* every plane with a $B$ or $\bar B$ has at least one non-empty $A$.

**Step 4: selection.** Let $a_k$ be the number of non-empty $A$ segments of plane $k$. Plane $k$ is
*active* if $a_k \ge 1$; the others are *idle* (only empty $A$ and $\bar A$ segments). For an active plane,
let $X_k$ consist of the cities of all its $B$, $\bar B$ and non-empty $A$ segments, plus $a_k - 1$ of its
$\bar A$ segments. It has $\#A - 1 \ge a_k - 1$ of them. Then:

* $|X_k| = \#B_k + \#\bar B_k + 2a_k - 1 \ge 1$;
* $\ell(X_k) \le F_k \le M$;
* $X_k$ is a sub-multiset of the plan's landings, so the total cost is at most $C$.

Each passenger is carried out by exactly one segment and delivered by exactly one, so
$\sum_k(\#B_k + a_k) = \sum_k(\#\bar B_k + a_k) = t$. Hence, over the $q$ active planes,
$\sum_k |X_k| = 2t - q$.

**Step 5: admissibility.** Let $\Psi$ be the multigraph on active planes with one edge per hand-off, between
the planes of $o(\pi)$ and $n(\pi)$. Then $\deg_\Psi(k) = \#B_k + \#\bar B_k + 2\cdot\#\text{swaps}_k
\equiv |X_k| + 1 \pmod 2$. So the even planes are exactly the vertices of odd $\Psi$-degree.

Both segments of a hand-off are selected, at the same city, so $\Psi$-adjacent planes are connected in $H$.
Each component of $H$ is therefore a union of components of $\Psi$, and each of those contains an even
number of odd-degree vertices. So the partition is admissible.

**Step 6: idle planes.** Apply Lemma 4.4 once per idle plane, while $q < p \le t$. $\square$

**Lemma 4.4 (adding a plane).** Let $X_1,\dots,X_q$ be admissible with $\sum|X_k| = 2t - q$,
$\max\ell \le M$ and $t \ge q+1$. Then there is an admissible $Y_1,\dots,Y_{q+1}$ with
$\sum|Y_k| = 2t - q - 1$, $c(Y) \le c(X)$ and $\max \ell \le M$.

*Proof.* Take a forest $T$-join $J$. For each $J$-edge $(k,i)$, reserve one landing of $i$ in $X_k$. The
other $|X_k| - h_k$ landings of $X_k$ are *free*; there is an odd number $\ge 1$ of them (Lemma 2.3).

*Case (a): some plane has at least 3 free landings $e, e', \dots$.* Set $Y_k = X_k - \{e,e'\}$ and
$Y_{q+1} = \{e\}$. Parities are unchanged, and $J$ is still a $T$-join. Also
$\ell(Y_{q+1}) = 2d_e \le \ell(X_k)$.

*Case (b): every plane has exactly one free landing.* Then $2t - q = \sum (h_k + 1) = 2|J| + q$, so
$|J| = t - q \ge 1$. Some city $i$ therefore has $J$-degree $\ge 2$, with edges to planes $u \ne v$.
Remove the reserved landings of $i$ from $X_u$ and $X_v$, and set $Y_{q+1} = \{i\}$. Then
$J - \{(u,i),(v,i)\}$ is a $T$-join for the new set of even planes ($u$ and $v$ both change parity), and
$\ell(Y_{q+1}) = 2d_i \le \ell(X_u)$. $\square$

**Corollary 4.5 (front characterisation).** Under (S) and (A1),
$$\mathcal F = \min{}_{\text{Pareto}} \big\{ (c(X), M(X)) : |X| = s \big\}, \qquad
M(X) = \min_{\text{admissible } X_1..X_p} \max_k \ell(X_k).$$

*Proof.* Theorem 4.1 shows every such pair is achieved; Theorem 4.3 shows every plan is weakly dominated
by one. $\square$

In particular, both papers' Proposition I (Pareto-optimal plans need exactly $2t-p$ landings) holds for the
front in this setting.

### 4.3 What remains under (AΔ) only

**Conjecture 4.6.** Theorem 4.3 holds under (S) and (AΔ), without (A1).

Steps 2–6 need simple segments only, so the conjecture is equivalent to **Step 1 without (A1)**: every plan
is weakly dominated, in the sense of Theorem 4.3, by a plan without central flights. Splitting $a \to b$
through $C_G$ now costs $d_a + d_b$, which can exceed $d_{ab}$. A segment can then only pay for one of its
landings ($2d_a + 2d_b \le \tau$ is false in general), while the hand-offs at $a$ and at $b$ may involve
different planes.

This is exactly the "Figure 4" case of the arXiv paper. Its pairing argument has two flaws:

* It concludes "lower cost" from set inclusion ("each city in $\phi_0$ appears in $\phi$"). But moving both
  halves of a pairing to $C^* = \arg\min(d_i, d_j)$ costs $2c_{C^*}$, which can exceed $c_i + c_j$.
* It concludes "dominates" from per-pattern durations, which ignores the synchronisation of the new pairs.

**Partial result (one chain).** Consider a passenger handed along segments $\sigma_0, \dots, \sigma_m$ at
cities $x_1, \dots, x_m$. Let $x_{j^*}$ minimise $d$. Give $\sigma_0$ and $\sigma_m$ the city $x_{j^*}$,
charged to the two landings at $x_{j^*}$. For intermediate $\sigma_j$, keep $x_j$ if $j < j^*$ and
$x_{j+1}$ otherwise. This is cost-injective, respects every segment's duration, and connects the two ends.

What is missing is doing this simultaneously for all chains when segments are shared between chains. That is
the proof obligation for Conjecture 4.6. Evidence: §10.

## 5. Why the per-PPP greedy of both papers is not exact

Both papers prove optimality of a greedy that assigns the longest durations first to the least-loaded plane.
The proof (arXiv §3.2) rests on the sentence "the above algorithm gives the optimal distribution of the set
of times into $p$". The no-waiting construction is correct (Theorem 4.1); the optimal distribution is not.

* $d = (6, 10)$, $p = 2$, $t = 5$, PPP $a = (10,10,6,6,6)$, $\bar a = (10,6,6)$: the greedy gives every plane a
  20-crossing first and ends at 52/68. The partition $\{10,10,10\} \mid \{6,6,6,6,6\}$ gives 60/60. The
  front point (260, 60) is missed.
* $d = (1,3)$, $c = (9,5)$, $t = 4$, $p = 2$: the point (42, 12) needs the plane making the drop-off to also take
  the long crossing; the no-duplicate greedy ends at 14.

Deciding $M(X) \le 2T$ is NP-complete (§8), so no polynomial greedy can be exact unless P = NP.

## 6. Non-symmetric case

### 6.1 What carries over

Lemmas 3.1–3.3 hold. Under (A1-NS), $d_{ij} \ge \min(d_i + d_j,\ \bar d_i + \bar d_j)$, Step 1 of Theorem 4.3
works by splitting through $C_I$ or $C_G$, whichever is shorter. Steps 2–6 also go through with
*role-dependent* loads:

* a crossing through $w$ costs $d_w + \bar d_w$;
* a drop-off half costs $2d_w$;
* a pick-up half costs $2\bar d_w$.

N5 and N6 need $\bar d_x \le d_x + d_z + \bar d_z$ and its mirror, which (AΔ) gives.

**Theorem 6.1.** Under (A1-NS) and (AΔ), every plan is weakly dominated by a *role configuration*: multisets
of crossings, drop-off halves and pick-up halves per plane, with an admissible link structure, whose cost is
$\le C$ and whose largest *role load* is $\le M$.

### 6.2 Waiting

In the construction of Theorem 4.1, plane $v$ finishes at most at $\max(\ell_v,\ D_u - d_i + \bar d_i)$, which
exceeds $\max_k \ell_k$ when $\bar d_i > d_i$ and $u$ has long drop-offs. So in general the makespan of a role
configuration is not its largest load.

**Conjecture 6.2 (no harmful waiting).** Every role configuration has a schedule whose makespan equals its
largest role load, possibly after reordering drop-offs and re-orienting links.

If true, Theorem 6.1 gives the exact front under (A1-NS). If false, the max-load front is still a valid
**lower bound**, and the exact makespan of a configuration must be computed by search (§9). Evidence: on 193
non-symmetric instances, ignoring waiting never changed the front.

### 6.3 Short central flights: the shuttle triple

Without (A1-NS), the $2t-p$ model is beaten (11 of 140 random instances). The smallest example found has
$n = 2$, $t = 4$, $p = 3$, $d = (5,3)$, $\bar d = (2,3)$, $c = (1,5)$, and the central flight as short as (AΔ)
allows. Its point (18, 12) needs 6 landings, one more than $s = 5$.

This is the arXiv paper's $B\bar A\bar B$ situation: a drop-off at $i$, a shuttle $C_G \to i \to j \to C_I$,
and a pick-up at $j$.

**Conjecture 6.4 (extended Proposition I).** Under (AΔ), the front equals the front of role configurations
extended with *shuttle triples* (each adding exactly one landing), with exact makespans.

The arXiv construction of §3.3 (virtual cities) encodes the triples. It is sound only if a drop-off or
pick-up at a virtual city is used together with its shuttle. Its equation (4) should read
$d^{\bar B}_k = 2\bar d_j$. The non-symmetric proofs of §2.3 need repairs as well:

* the "finite number of patterns" argument is defeated by 2-cycles;
* "the central pattern cannot be $A$" is unproved;
* the multiplicity "exactly 1" is unproved.

## 7. Exact algorithm (symmetric case)

**Reformulation.** Assume integer durations (scale, and divide by their gcd). For $T \ge 0$ let
$$E(T) = \min\{ c(X) : |X| = s,\ \exists \text{ admissible partition with } \delta(X_k) \le T\ \forall k\}.$$
$E$ is non-increasing. By Corollary 4.5, $\mathcal F = \{(E(T), 2T) : E(T) < E(T')\ \forall T' < T\}$.

**Pairs are not enough.** The upper bound below only links even planes two by two through one city. That is
not always optimal. Example: durations $(4,2,6,7)$ with multiplicities $(2,1,3,1)$, $p = 3$. Admissible
partitions reach 24, with $\{6,6\}$, $\{4,7\}$, $\{4,2,6\}$: the two even planes share no city and are linked
through the odd one. Pairs reach only 26. On 3,000 random multisets, pairs were optimal on 2,989.

**Algorithm.** Let $m_{\max} = s - p + 1$ (largest group) and $T_{\max} = m_{\max} \cdot \max_i d_i$.

1. *One plane.* $G[m][T]$ = cheapest multiset of $m$ cities with $\delta \le T$:
   $G[0][T] = 0$ and $G[m][T] = \min_{i:\, d_i \le T} \big(c_i + G[m-1][T - d_i]\big)$.
2. *Lower bound* (drops admissibility): $L(T)$ = cheapest way to give $p$ planes $m_1, \dots, m_p \ge 1$
   landings with $\sum m_k = s$, paying $\sum_k G[m_k][T]$. Computed by a DP over planes and landings used.
   $L(T) \le E(T)$.
3. *Upper bound* (always admissible): odd groups cost $G[m][T]$ ($m$ odd); two even groups of sizes $a$ and
   $b$ sharing a city cost $\min_i \big(2c_i + G[a-1][T-d_i] + G[b-1][T-d_i]\big)$. Combine by the same DP.
   $U(T) \ge E(T)$, since every combination is admissible.
4. *Exact value.* For $T = 0, 1, \dots, T_{\max}$:
   * if $L(T) = U(T)$, then $E(T)$ is that value;
   * otherwise, find the cheapest partition with cost in $[L(T), \min(U(T), E(T-1)))$ by depth-first search
     over groups in canonical order. Use the cost bound and the remaining-planes bound from step 2, and check
     admissibility (union–find) at the leaves. If nothing is found, $E(T) = \min(U(T), E(T-1))$.
5. *Front and plans.* Emit $(E(T), 2T)$ whenever $E(T) < E(T-1)$. Rebuild the partition from the tables or
   the search, then the plan with the construction of Theorem 4.1.

**Correctness.** Steps 1–3 compute valid bounds by construction, step 4 is exhaustive within the window, and
step 5 follows Corollary 4.5. The algorithm is exact under (S)+(A1), and under (S)+(AΔ) if Conjecture 4.6
holds.

## 8. Complexity

Let $D = \max_i d_i$, so $T_{\max} \le sD$.

| Step | Time | Memory |
|---|---|---|
| 1. One-plane table | $O(n\, s\, T_{\max}) = O(n s^2 D)$ | $O(s\, T_{\max})$ |
| 2. Lower bound, all $T$ | $O(p\, s^2\, T_{\max}) = O(p s^3 D)$ | $O(p\, s)$ per $T$ |
| 3. Upper bound, all $T$ | $O((n s^2 + p s^3)\, T_{\max}) = O((n + ps)\, s^3 D)$ | $O(s^2 + ps)$ per $T$ |
| 4. Exact window search | exponential in the worst case (below) | $O(s + n + p)$ |
| 5. Plan for one point | $O(s + n + p)$ (union–find, forest) | $O(s + n + p)$ |

Steps 1–3 are pseudo-polynomial: polynomial in $n$, $t$, $p$ and in the *magnitude* $D$. Large durations can
be mitigated by the gcd reduction, by sweeping only reachable half-loads instead of every integer, or by a
binary search on $T$ per front point.

**Hardness of the exact step.** Deciding $M(X) \le 2T$ is NP-complete.

*Proof.* Membership: guess the partition and check admissibility with union–find. Hardness, from Partition
($a_1,\dots,a_m$ with sum $2B$, $m$ even after padding with a zero): take one city per item with $d = a_i$,
two extra cities of duration 0, $p = 2$, and $X$ all of them once, so $s = m + 2$. All cities are distinct, so
two even groups can never share a city; only odd/odd partitions are admissible, and the zero cities fix the
parities. So $M(X) \le 2B$ iff the items split into two halves of sum $B$. $\square$

The hardness is weak (pseudo-polynomial in $D$ for fixed $n$). Whether computing the whole front is NP-hard
is not established here.

**Worst case of step 4:** at most $\binom{n+s-1}{s}$ multisets in the window times the number of partitions
into $p$ groups. In practice, the bounds disagreed at 0–3 makespan levels per instance in the symmetric
measurements (§10).

## 9. Non-symmetric algorithm (conditional)

1. Bounds by the same DP over planes, with role items (crossing $d+\bar d$, drop $2d$, pick $2\bar d$) and,
   for the lower bound, only the global balance #drops = #picks. This is valid by Theorem 6.1 under (A1-NS);
   validity with shuttle triples is untested.
2. Exact value where the bounds disagree: search over role configurations (and, if Conjecture 6.4 holds,
   shuttle triples), with each configuration's makespan computed by search over link orientations and orders
   with waiting simulated, until Conjecture 6.2 is settled.

Complexity: steps as in §8 with three item types, plus a search that is exponential in the worst case. The
bounds were loose in the measurements (certified on 18–28% of instances), so the search dominates.

## 10. Evidence and how to reproduce it

All checks compare against exhaustive searches written independently of the solvers. The scripts live in the
development scratchpad for now; they move into `tests/` with the implementation.

| Check | Result |
|---|---|
| Achievability construction (Thm 4.1) simulated with waiting, random admissible partitions | 19,323 / 19,323 makespan = largest load (971 with chains) |
| Characterisation vs brute force over schedules (multisets up to 10 landings, $p \le 5$) | 2,700 / 2,700 |
| Exact prototype (§7) vs search over **all plans**, symmetric, three central-flight regimes | 504 / 504 |
| $2t-p$ front vs all plans, symmetric (incl. 96 hub instances, shortest central flights) | 516 / 516 |
| $2t-p$ front vs all plans, non-symmetric, no useful central flights | 280 / 280 |
| same, shortest central flights | 129 / 140 (the 11 are shuttle triples) |
| Ignoring waiting, non-symmetric | 193 / 193 fronts unchanged |
| Golden fronts | 27 / 27 |

The exhaustive search over plans enforces that planes end in $C_G$ and allows any flight, including central
ones.

## 11. Next steps

1. Prove Conjecture 4.6: simultaneous chain contraction for shared segments.
2. Test Conjecture 6.4 by extending the exhaustive oracle with shuttle triples and comparing on the 11
   instances.
3. Settle Conjecture 6.2 (no harmful waiting), or keep the search.
4. Formalise Lemmas 2.2–2.3, 3.2 and Theorem 4.3 in Lean; they are self-contained combinatorics.
