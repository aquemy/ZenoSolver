# ZenoFront: Lean formalisation of the exact MultiZenoTravel front

`ZenoFront` is a Lean 4 / Mathlib library about the exact Pareto front of symmetric
MultiZenoTravel. The informal proofs are in
[`doc/theory/exact-front.md`](../doc/theory/exact-front.md); the statements follow the IDs of
the proof review (Claim A, PAR, Claim B′, G, R).

It has two parts:

* **the combinatorial core** (no time, no plans): admissibility, role configurations, the
  support bound and the one-plane table;
* **a verified checker for front certificates** (format v1 of
  [`doc/certificate-format.md`](../doc/certificate-format.md)). It covers certificates whose
  gaps are all `relaxed`. The
  soundness theorem `Cert.check_sound` says that if `check` accepts, the listed points are
  exactly the Pareto front of the instance. The front is that of *every* feasible plan, with any
  central flights (format v1 plans fly none of them).

Section [TODO](#todo) lists the rest.

## Build

Toolchain: Lean `v4.36.0`, Mathlib `v4.36.0` (pinned in `lakefile.toml` and `lake-manifest.json`).

```sh
cd lean
lake exe cache get        # download the Mathlib build cache (never build Mathlib from source)
lake build --wfail        # build ZenoFront; warnings, including `sorry`, are errors
lake env lean scripts/CheckAxioms.lean   # axiom audit
lake build zeno-check     # the compiled checker (first build compiles Mathlib's C code, ~1.5 min)
lake exe zeno-check FILE  # check a certificate
bash test/run.sh          # check the test certificates against their expected verdicts
```

The axiom audit fails if any declaration of a `ZenoFront` module uses an axiom other than
`propext`, `Classical.choice` and `Quot.sound`. It rejects `sorryAx` and `native_decide`.
CI (`.github/workflows/lean.yml`) runs all of this on every push and pull request that touches
`lean/**`, plus a `grep` for `sorry` and `admit`.

`zeno-check FILE` prints one of three verdicts:

* `accepted` (exit code 0): `Cert.check` returned `true`;
* `rejected: <reason>` (exit code 1): the file is malformed, or an obligation fails;
* `not supported: <reason>` (exit code 2): every supported obligation holds, but a gap names the
  `forest` bound.

Only `accepted` is backed by the theorem. The reasons are diagnostics, recomputed outside the
verified function. On the largest sample, `relaxed-r101.cert`, the check takes about 0.13 s on
an Apple-silicon laptop: 62 KB, `n = 10`, `t = 14`, `p = 5`, 89 points and 88 gaps.

`test/certificates/` holds three groups:

* `accepted/`: certificates written by the C++ solver whose gaps are all `relaxed`;
* `rejected/`: corrupted copies, each with a comment saying what was broken (wrong cost, wrong
  duration, broken passenger route, asymmetric durations, missing `S`, non-monotone points, a
  missing point, a `forest` gap relabelled `relaxed`, a truncated file);
* `unsupported/`: certificates with a `forest` gap.

## Contents

| File | Content | Main declarations |
|---|---|---|
| `ZenoFront/Model.lean` | Instance (`n` cities, `d c : Fin n → ℕ`, `t` passengers, `p` planes, `1 ≤ p ≤ t`), `s = 2t − p`, groupings `X : Fin p → Multiset (Fin n)`, load `δ`, cost | `Instance`, `Instance.s`, `Groups`, `load`, `cost`, `size`, `totalCost`, `maxLoad` |
| `ZenoFront/Admissible.lean` | Admissibility as Claim A (parity witnesses), decision procedure, Lemma 2.3, examples | `IsParityWitness`, `Admissible`, `witnessCandidates` |
| `ZenoFront/Roles.lean` | Role configurations, PAR and its converse | `RoleConfig`, `RoleConfig.groups`, `RoleConfig.witness` |
| `ZenoFront/SupportBound.lean` | Claim B′, `t − p` part | `touched`, `edgeCount` |
| `ZenoFront/MinimalWitness.lean` | Claim B′, `p − 1` part, and the combined `min(p − 1, t − p)` bound | `edgeVec`, `coordSum` |
| `ZenoFront/OnePlane.lean` | One-plane table `G[m][T]`: specification and memoised table | `oneplane`, `oneplaneTable` |
| `ZenoFront/Plan.lean` | Locations, legs, plans, flight network (with arbitrary central flights `dc`), feasibility, cost, makespan | `Loc`, `Leg`, `Plan`, `Network`, `Flies`, `IsRoute`, `Feasible`, `planCost`, `planMakespan` |
| `ZenoFront/PlanBounds.lean` | Counting, segments, trimming, Lemma R | `hubArrivals`, `ciDepartures`, `cgArrivals` |
| `ZenoFront/Relaxation.lean` | The relaxation `L(T)`, memoised, and gcd scaling | `relaxCost`, `relaxRow`, `relaxedBoundAt`, `durationScale`, `scaledDurations` |
| `ZenoFront/Simulate.lean` | Computable plan check (mirrors `src/zeno/plan.cpp`) | `legOK`, `planeOK`, `pickLeg`, `follow`, `paxOK`, `planOK` |
| `ZenoFront/Checker.lean` | Pareto fronts, certificates, `check`, soundness | `achievable`, `IsParetoFront`, `Cert`, `Cert.check` |
| `ZenoFront/Parse.lean` | Parser for the text format (untrusted) | `parseCert` |
| `ZenoFront/Examples.lean` | Two certificates checked by the kernel alone | `Examples.lptCounterexample_front` |
| `ZenoCheck.lean` | The `zeno-check` executable (untrusted wrapper) | `main` |

### Theorems

All of these are proved without `sorry`, and the kernel checks every one of them.

**Admissibility (`Admissible.lean`)**

* `IsParityWitness.card_add_one_le`: Lemma 2.3, `|h k| + 1 ≤ |X_k|` for every witness (forest
  or not).
* `IsParityWitness.sum_card_add_le`: `Σ_k |h k| + p ≤ Σ_k |X_k|`.
* `Admissible.card_pos`: every group of an admissible grouping is non-empty.
* `Admissible.p_le_size`: an admissible grouping has at least `p` landings.
* `admissible_iff_exists_mem_witnessCandidates`: the decision procedure is correct.
* Examples, checked by `decide`:
  * a lone even plane is inadmissible;
  * two even planes with disjoint supports are inadmissible (the situation of the §8 hardness
    proof), while the same landings split into odd groups are admissible;
  * two even planes sharing a city are admissible;
  * an even plane linked only to an odd plane is inadmissible;
  * an empty group is inadmissible;
  * the §7 "pairs are not enough" partition `{6,6} | {4,7} | {4,2,6}` is admissible.

**Role configurations (`Roles.lean`)**

* `RoleConfig.isParityWitness_witness` (**PAR**): `X_k = D_k + P_k + Cr_k` is admissible, with
  witness `h_{k,i} = (D_k(i) + P_k(i)) mod 2`.
* `RoleConfig.admissible_groups`: PAR, admissibility form.
* `IsParityWitness.exists_roleConfig` (**converse of PAR**): every witness `h` of `X` gives a
  role configuration with grouping `X` and `D_k + P_k = h k`.
* `Admissible.exists_roleConfig`, `admissible_iff_exists_roleConfig`: the admissible groupings
  are exactly the groupings of role configurations.

**Claim B′ (`SupportBound.lean`, `MinimalWitness.lean`)**

* `edgeCount_eq_sum_degree`: double counting, `Σ_k |h k| = Σ_i #{k | i ∈ h k}`.
* `IsParityWitness.two_mul_card_touched_le_edgeCount`: `2 · #touched ≤ #edges`.
* `IsParityWitness.edgeCount_le`: with `Σ_k |X_k| = s`, `#edges ≤ 2(t − p)`.
* `IsParityWitness.card_touched_le` (**Claim B′, `t − p` part**): with `Σ_k |X_k| = s`, every
  witness touches at most `t − p` cities.
* `IsParityWitness.card_le_min`: with `Σ_k |X_k| = s`, `|h k| ≤ min(|X_k| − 1, t − p)`.
* `IsParityWitness.exists_edgeCount_lt`: if the edge vectors `e_k + e_i` are linearly
  dependent over `ZMod 2`, removing an even subgraph gives a witness with fewer edges, contained
  in the original.
* `edgeCount_add_one_le_of_linearIndependent`: independent edge vectors satisfy
  `#edges + 1 ≤ p + #touched`.
* `IsParityWitness.card_touched_le_of_minimal` (**Claim B′, `p − 1` part**): a witness with the
  fewest edges touches at most `p − 1` cities.
* `IsParityWitness.card_touched_le_of_minimal_subset`: the same for a witness that contains no
  other witness.
* `Admissible.exists_minimal`: an admissible grouping has a witness with the fewest edges.
* `Admissible.exists_card_touched_le_sub_one`: an admissible grouping has a witness touching at
  most `p − 1` cities.
* `Admissible.exists_card_touched_le` (**Claim B′**): with `Σ_k |X_k| = s`, an admissible
  grouping has a witness touching at most `min(p − 1, t − p)` cities.

**One-plane table (`OnePlane.lean`)**

* `oneplane_le_cost`: `G[m][T] ≤ c(Y)` for every `m`-multiset `Y` with `δ(Y) ≤ T`.
* `exists_cost_eq_oneplane`: if `G[m][T] < ∞`, some `m`-multiset with `δ ≤ T` costs exactly
  `G[m][T]`.
* `oneplane_eq_top_iff`: `G[m][T] = ∞` iff every `m`-multiset has `δ > T`.
* `isLeast_oneplane`: `G[m][T]` is the least cost of an `m`-multiset with `δ ≤ T`, when one
  exists.
* `oneplaneRow_getD`, `oneplaneTable_getD`: the memoised table (`O(mMax · Tmax · n)`) agrees
  with `G` for `m ≤ mMax`, `T ≤ Tmax`.

**Plans and lower bounds (`PlanBounds.lean`)**

Every statement holds for every feasible plan, for any table `dc` of central flight durations.

* `ciDepartures_add_cgArrivals`: along a route,
  `#departures from C_I + #arrivals at C_G + [ends at C_I] = #hub arrivals + [starts at C_I]`.
* `Feasible.le_ciDepartures`, `Feasible.le_cgArrivals`: every passenger leaves `C_I` and
  reaches `C_G` on its own leg (capacity one), so each count is at least `t`.
* `Feasible.le_sum_hubArrivals` (**counting**, Lemma 3.2): `2t ≤ Σ_k #segments_k + p`.
* `PlaneFeasible.exists_segments`: under (S), one landing per segment gives a multiset `Z` with
  `|Z| = #segments`, `2 δ(Z) ≤` the plane's end time, and `c(Z) ≤` its landing cost.
* `exists_trim`: groups that are all non-empty, with total size at least `s ≥ p`, can be trimmed
  to total size exactly `s` and stay non-empty.
* `Feasible.exists_relaxation` (**Lemma R**): under (S), with `p ≤ t`, a feasible plan yields
  `p` non-empty groups of total size `s = 2t − p`. Each satisfies `2 δ(Y_k) ≤ makespan`, and
  `Σ c(Y_k) ≤ cost`.

**Relaxation (`Relaxation.lean`)**

* `relaxCost_oneplane_le_totalCost`: `L(T) = relaxCost (G[·][T]) p s` is at most `Σ_k c(Y_k)`
  for every grouping into `p` non-empty groups of total size `s` with loads `≤ T`.
* `relaxRow_getD`: the memoised rows agree with `relaxCost`.
* `relaxedBoundAt_le_totalCost`: the bound the checker reads from its tables is a lower bound.
* `load_eq_scale_mul`, `load_scaled_le_of_load_le`: loads in original units are `g ×` loads in
  scaled units, and `δ ≤ h` implies `δ/g ≤ ⌊h/g⌋`.

**Checker (`Simulate.lean`, `Checker.lean`, `Examples.lean`)**

* `planOK_feasible`: a plan accepted by the simulation is feasible, for every `dc`.
* `follow_sound`: the greedy passenger walk, when it uses all the passenger's legs, orders them
  into a route.
* `Feasible.minOf_le_makespan` (**obligation 2**): under (S), every feasible plan has makespan
  `≥ 2 · d_min · ⌈s/p⌉`.
* `Feasible.minOf_le_cost` (**obligation 4**): under (S), every feasible plan costs
  `≥ s · c_min`.
* `Cert.gapBound_le` (**obligation 3**, `relaxed`): a feasible plan with makespan below `M`
  costs at least the relaxed bound at the gap level of `M`.
* `exists_le_of_gapsOK`: the domination argument along the front.
* `Cert.check_sound` (**soundness**): `C.check = true` implies, for every `dc`,
  `IsParetoFront (achievable (C.network dc) C.c C.t C.p) C.front`. That is, every point is
  achieved by a feasible plan, every feasible plan is weakly dominated by a point, and the points
  are pairwise incomparable.
* `IsParetoFront.mem_iff_minimal`, `Cert.check_sound_minimal`: equivalently, a pair is listed
  iff it is a minimal achievable (cost, makespan) pair.
* `Examples.lptCounterexample_front`: checked by the kernel alone (`decide +kernel`, about
  1.5 s). For every `dc`, the Pareto front of `d = (6, 10)`, `c = (40, 20)`, `t = 5`, `p = 2` is
  `(320, 48), (280, 56), (260, 60), (240, 64), (200, 72), (160, 80)`. This includes the point
  the papers' greedy misses.

## Conventions shared with the C++ side

* **Indices.** Cities are `Fin n`, planes `Fin p`, passengers `Fin t`, all numbered from `0`.
  The certificate format numbers them from `1`.
* **Durations and costs.** Durations and costs are natural numbers. `d i` is the *one-way*
  duration between a hub and city `i`.
* **Load and makespan.** The load of a group is `δ(Y) = Σ_{w ∈ Y} d w`. The makespan of the
  plan built from it is `2 δ`. Every `T` in the DP and the table is a **half-makespan** (a bound
  on `δ`), as in §7 of the note.
* **Grouping (partition).** A grouping is one multiset of city indices per plane. Order within a
  group is irrelevant; a group may repeat a city. Groups are not required to be non-empty:
  admissibility implies it (`Admissible.card_pos`). Nothing in the definition ties the grouping
  to `s`; the theorems that need `Σ_k |X_k| = s` take it as a hypothesis (`size X = I.s`).
* **Parity witness `h`.** One *set* of city indices per plane (no repeats), with:
  * `h k ⊆ supp X_k`;
  * `|h k| ≡ |X_k| + 1 (mod 2)`;
  * every city in an even number of the `h k`.

  It is the `T`-join of Lemma 2.2, as a 0/1 matrix. It need not be a forest. A witness found by
  the σ-DP is fine as a certificate of admissibility, but Theorem 4.1's plan construction needs
  a forest. A certificate that wants the `min(p − 1, t − p)` bound on touched cities should send
  an inclusion-minimal witness (`card_touched_le_of_minimal_subset`).
* **Role configuration.** Three multisets per plane: drop-offs `D_k`, pick-ups `P_k` and
  crossings `Cr_k`, with `|Cr_k|` odd and `Σ_k D_k = Σ_k P_k` as multisets (per-city balance).
  The converse of PAR produces `D_k + P_k = h k`, so every city appears at most once in
  `D_k + P_k`.
* **Infinity.** The tables use `WithTop ℕ`, with `⊤ = ∞`. `ℕ∞` is not used because its lattice
  instance is not computable. The C++ table must agree on `G[0][T] = 0` and
  `G[m + 1][T] = min_{i : d_i ≤ T} (c_i + G[m][T − d_i])`, the minimum over no city being `∞`.

### Certificate format v1

`Cert.check` mirrors `checkCertificate` in `src/zeno/certificate.cpp` and `checkPlan` in
`src/zeno/plan.cpp`:

* **Header.** It requires `1 ≤ n`, `1 ≤ p ≤ t`, `d = dbar` (checked, not trusted) and `S` among
  the assumptions.
* **Indices.** The format numbers cities `1..n` (location `0` is `C_I`, `n + 1` is `C_G`) and
  planes and passengers from `1`; passenger `0` means none. `Fin` counts from `0`, so the parser
  subtracts one.
* **Front.** There must be at least one point. Points are strictly increasing in makespan and
  strictly decreasing in cost, with one plan per point and one gap kind per gap.
* **Plans (obligation 1).** The checker simulates each plan:
  * legs must be hub–central flights of exact duration;
  * planes must chain from `C_I` at time `0` and end in `C_G`;
  * passengers are followed greedily, by earliest (departure, arrival) and the first leg on a
    tie, and every leg of a passenger must be used.

  The cost is the sum of `c` over central landings. The makespan is the maximum over planes of
  the last arrival.
* **Closed forms (obligations 2 and 4).** `M_1 = 2 · d_min · ⌈s/p⌉`, with
  `⌈s/p⌉ = (s + p − 1)/p`, and `C_r = s · c_min`.
* **Gaps (obligation 3).** The level below `M_{i+1}` is `⌊⌊(M_{i+1} − 1)/2⌋ / g⌋`, with `g`
  the gcd of `d` (or `1` if `g = 0`), and the durations are divided by `g`. The C++ checker also
  removes dominated cities before computing `L`, which does not change `L`; the Lean checker
  keeps every city. A gap passes iff `C_i ≤ L(level)`, with `L = ∞` when no grouping fits.
* **`forest` gaps.** `check` returns `false` on them for now.

## Trust assumptions

* **Theorems.** Every theorem is checked by the Lean kernel and depends only on `propext`,
  `Classical.choice` and `Quot.sound`. The axiom audit enforces this. The examples use `decide`,
  which the kernel evaluates; `native_decide` is not used anywhere.
* **Statements.** The definitions are the trusted interface: a theorem is only as good as the
  match between them and the intended mathematics. For the checker these are `Feasible`,
  `planCost`, `planMakespan`, `achievable` and `IsParetoFront`. The docstrings tie each
  definition to the note and the format.
* **Plan semantics.** Times are natural numbers, as in format v1. The theorem therefore
  quantifies over every plan with integer times. Rational times are **not covered**, although
  the proof uses no integrality of waiting times: every bound comes from sums of integer
  durations. Plans may fly central–central legs of any duration `dc`, may wait anywhere and may
  hand passengers over anywhere. Planes must end in `C_G` (the format's semantics, not PDDL's;
  see bridge B3 below).
* **Parser.** `parseCert` and `ZenoCheck.lean` are **outside the verified statement**.
  `Cert.check_sound` is about the `Cert` value, so a parser bug could make the checker verify a
  different front than the file's. The parser only translates numbers and `1`-based indices; it
  mirrors `readCertificate` in `src/zeno/certificate.cpp`.
* **Compiled checker.** `lake exe zeno-check` runs `Cert.check` as compiled code. Its verdict
  therefore also trusts the Lean compiler and runtime, not only the kernel. Only the soundness
  theorem is kernel-checked. To avoid that trust, a certificate can be checked by the kernel
  with `decide +kernel`, as `Examples.lean` does. That is practical for small certificates only.

## TODO

Remaining items of the formalisation plan (proof review, §4).

**Next: `forest` gaps.** A `forest` gap bound is `E(T)`, computed by the link-forest DP. Its
soundness needs two things: every feasible plan (under (A1)) is weakly dominated by an
admissible grouping (Theorem 4.3, P3), and the link-forest DP computes a lower bound on `E(T)`
(link-forest lemma, P4). The checker then needs the forest DP as a computable function with that
lower-bound theorem.

**P1, combinatorial core (rest).**

- [ ] SH (shrink): a role configuration with `Σ_k (|D_k| + a_k) > t` can drop one unit, keeping
      loads and cost from increasing.
- [ ] AP (add a plane, Lemma 4.4): an admissible `q`-grouping with `Σ|X_k| = 2t − q`, `t ≥ q + 1`
      gives an admissible `(q + 1)`-grouping with one landing less, no larger cost or load.
- [ ] σ-DP of Claim C: definition over states `(j, σ)` with `|σ| ≤ min(p − 1, t − p)`, plane
      options `(m, H)` with `|H| ≡ m + 1`, `|H| ≤ m − 1`, cost `c(H) + G[m − |H|][T − δ(H)]`.
      Soundness (`DP ≥ E`, from `Admissible`) and completeness (`DP ≤ E`, from Claim B′ and
      `isLeast_oneplane`).
- [ ] `E(T)` as a definition (least cost over admissible groupings with `Σ|X_k| = s` and
      `δ(X_k) ≤ T`) and its monotonicity.
- [ ] Pairs upper bound `U(T)`, with `L ≤ E ≤ U`.
- [ ] Bellman-potential soundness: potentials with `φ(src) ≤ 0` and `φ(v) ≤ φ(u) + w(u, v)` on
      every arc bound `E(T)` from below.
- [ ] Executable admissibility check (union–find on the plane–city graph) proved equal to
      `Admissible`. This needs Lemma 2.2 (component form ⇔ parity witness).

**P2, plan semantics and the relaxation.**

- [x] Route-based plans with `ℕ` times (`Plan.lean`), matching format v1, with arbitrary
      central flights.
- [x] Counting (Lemma 3.2) by leg counting (`Feasible.le_sum_hubArrivals`).
- [x] Segments and the endpoint bound under (S) (`PlaneFeasible.exists_segments`).
- [x] Lemma R (`Feasible.exists_relaxation`), and `L` as a DP proved a lower bound.
- [x] Primal checker (`planOK_feasible`) and the end-to-end checker for all-`relaxed`
      certificates (`Cert.check_sound`), with a parser and `zeno-check`.
- [ ] Rational (or any ordered-semiring) times.
- [ ] Completeness of the simulation: the greedy passenger walk finds a route whenever the
      C++ one does. Only soundness is proved.

**P3, Theorem 4.3 (converse under (S) + (A1)).**

- [ ] Step 1: removing central flights under (A1).
- [ ] Cleaning (Lemma 3.1) as a suffix/prefix operation on passenger routes.
- [ ] Hand-off abstraction (M6): `o` and `n` injective, hand-offs at a common city.
- [ ] DS (direct selection) from a simple plan to a role configuration, then M7 via DS, SH, PAR.
- [ ] Front theorem X3 for `forest` gaps (the `relaxed` case is `Cert.check_sound`).

**P4.**

- [ ] Bridge B3: the PDDL semantics (planes end anywhere, makespan = last action) has the same
      front under (S) + (A1).
- [ ] Theorem 4.1: forest `T`-join, links, schedule with drop-offs first and at most one
      pick-up per plane, makespan = largest load.
- [ ] Link-forest lemma and tree-DP potentials; Pareto-semiring DP (PS); dominance and
      closed-form ends of the front.

**P5, non-symmetric.**

- [ ] Role model with role loads (crossing `d + d̄`, drop `2d`, pick `2d̄`); N1 (converse under
      (A1-NS)); N3 (drops-first template); W1 (a single pick-up never waits harmfully);
      imbalance-vector DP; simulation with waiting; Conjecture 6.2 if it is proved.
