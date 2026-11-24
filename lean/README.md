# ZenoFront: Lean formalisation of the exact MultiZenoTravel front

`ZenoFront` is a Lean 4 / Mathlib library about the exact Pareto front of symmetric
MultiZenoTravel. The informal proofs are in
[`doc/theory/exact-front.md`](../doc/theory/exact-front.md); the statements follow the IDs of
the proof review and of the note (Claim A, PAR, Claim B′, G, R, Theorem 4.7).

It has three parts:

* **the combinatorial core** (no time, no plans): admissibility, role configurations, the
  support bound, the one-plane table, shrinking and merging partitions;
* **the plan theory**: plan semantics with arbitrary central flights, counting, Lemma R, and the
  converse under (S) and (A1) (Theorem 4.7): every feasible plan is weakly dominated by an
  admissible partition;
* **a verified checker for front certificates** (format v1 of
  [`doc/certificate-format.md`](../doc/certificate-format.md)), for `relaxed` and `forest` gaps.
  The soundness theorem `Cert.check_sound` says that if `check` accepts, the listed points are
  exactly the Pareto front of the instance. The front is over *every* feasible plan: with any
  central flights when all gaps are `relaxed`, and with any central flights satisfying (A1)
  otherwise (format v1 plans fly none of them).

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

End to end, from the repository root, with the C++ solver built (`cmake --preset release`):

```sh
bash lean/test/e2e.sh build/release/zeno lean/.lake/build/bin/zeno-check
```

It solves every golden instance (`tests/golden/instances.txt`) and the random instances of
`lean/test/instances/` with the C++ solver, writes their certificates, and requires both
`zeno check` and `zeno-check` to accept every one. Five of the random instances have a `forest`
gap.

The axiom audit fails if any declaration of a `ZenoFront` module uses an axiom other than
`propext`, `Classical.choice` and `Quot.sound`. It rejects `sorryAx` and `native_decide`.
CI (`.github/workflows/lean.yml`) runs all of this, end to end included, on every push and pull
request that touches `lean/**` or the C++ solver, plus a `grep` for `sorry` and `admit`.

`zeno-check FILE` prints one of two verdicts:

* `accepted` (exit code 0): `Cert.check` returned `true`;
* `rejected: <reason>` (exit code 1): the file is malformed, or an obligation fails.

Only `accepted` is backed by the theorem. The reasons are diagnostics, recomputed outside the
verified function.

Timings on an Apple-silicon laptop (M4 Max), for the compiled checker
(`bench/baselines/lean/apple-m4-max/`):
* The certificates of `test/certificates/`: about 24 ms at the median, 0.22 s at most
  (`tree12.cert`, whose two forest gaps use the tree DP).
* Version 2 certificates of small random non-symmetric instances (`n ≤ 4`, `t ≤ 6`): 23 ms at
  the median over 152 certificates, 0.2 s at most, and 2.3 s for `v2-balanced-e1w2.cert`
  (19 `balanced` gaps).
* The 66 certificates the C++ solver writes for the benchmark suite (`bench/instances/*.txt`):
  5.7 s in total, 33 ms at the median. The largest, `regimes/r5` (`n = 100`, `t = 60`, `p = 10`,
  3.9 MB, 240,000 legs), takes 2.3 s and 135 MiB. Before this phase's changes the same
  certificates took 478 s, 295 s of them for `r5`.
* The end-to-end run, 35 certificates: about 1.3 s, solver included.
* **Many non-dominated cities.** The σ-DP is exponential in the number of cities that survive
  the dominance merge, and the tree DP is pseudo-polynomial in the level `T`. The checker runs
  whichever `useTreeDP` estimates cheaper. Every suite certificate keeps the σ-DP. Three
  certificates of `zeno <args> -C 2 -D 2 -r 100` took more than 120 s with the σ-DP alone. With
  the tree DP they take:

  | `<args>` | cities after the merge | forest gaps | `zeno-check` |
  |---|---|---|---|
  | `-n 20 -t 12 -p 6` | 20 | 6 | 5 s |
  | `-n 20 -t 16 -p 4` | 20 | 5 | 7 s |
  | `-n 40 -t 20 -p 8` | 40 | 2 | 13 s |

  The C++ checker, whose tree DP uses Pareto staircases over `τ`, takes 0.04 s at most.

`test/certificates/` holds two groups:

* `accepted/`: certificates written by the C++ solver, with `relaxed` and `forest` gaps;
* `rejected/`: corrupted copies, each with a comment saying what was broken:
  * a wrong cost, a wrong duration, a broken passenger route;
  * asymmetric durations, a missing `S`, non-monotone points;
  * a missing point closed by neither bound;
  * a `forest` gap relabelled `relaxed`, a `forest` gap without `A1`;
  * a missing point on `tree12`, rejected by the tree DP with the C++ checker's bound (5230);
  * a truncated file;
  * version 2: `roles` gaps without `A1-NS`, `S` listed for non-symmetric durations, a missing
    point closed by no `roles` bound, `lagrangian` multipliers at which the bound is too weak.

The `v2-*` certificates are version 2 certificates of non-symmetric instances (`relaxed`,
`roles` and `lagrangian` bounds). The C++ checker agrees with every verdict.

## Contents

| File | Content | Main declarations |
|---|---|---|
| `ZenoFront/Model.lean` | Instance (`n` cities, `d c : Fin n → ℕ`, `t` passengers, `p` planes, `1 ≤ p ≤ t`), `s = 2t − p`, groupings `X : Fin p → Multiset (Fin n)`, load `δ`, cost | `Instance`, `Instance.s`, `Groups`, `load`, `cost`, `size`, `totalCost`, `maxLoad` |
| `ZenoFront/Admissible.lean` | Admissibility as Claim A (parity witnesses), decision procedure, Lemma 2.5, examples | `IsParityWitness`, `Admissible`, `witnessCandidates` |
| `ZenoFront/Roles.lean` | Role configurations, PAR and its converse | `RoleConfig`, `RoleConfig.groups`, `RoleConfig.witness` |
| `ZenoFront/SupportBound.lean` | Claim B′, `t − p` part | `touched`, `edgeCount` |
| `ZenoFront/MinimalWitness.lean` | Claim B′, `p − 1` part, and the combined `min(p − 1, t − p)` bound | `edgeVec`, `coordSum` |
| `ZenoFront/OnePlane.lean` | One-plane table `G[m][T]`: specification and memoised table | `oneplane`, `oneplaneTable` |
| `ZenoFront/Plan.lean` | Locations, legs, plans, flight network (with arbitrary central flights `dc`), feasibility, cost, makespan | `Loc`, `Leg`, `Plan`, `Network`, `Flies`, `IsRoute`, `Feasible`, `planCost`, `planMakespan` |
| `ZenoFront/PlanBounds.lean` | Counting, segments, trimming, Lemma R | `hubArrivals`, `ciDepartures`, `cgArrivals` |
| `ZenoFront/Relaxation.lean` | The relaxation `L(T)`, memoised, and gcd scaling | `relaxCost`, `relaxRow`, `relaxedBoundAt`, `durationScale`, `scaledDurations` |
| `ZenoFront/Shrink.lean` | Shrinking an admissible partition to `s` landings (SH, partition form); merging cities | `Admissible.exists_shrink`, `Admissible.map` |
| `ZenoFront/AddPlane.lean` | Adding a plane (Lemma 4.6, AP) | `Admissible.addPlane`, `Admissible.addPlanes` |
| `ZenoFront/Converse.lean` | (A1), central landings, segment types after Step 1, transfers (cleaning), Theorem 4.7 | `Network.A1`, `routeLandings`, `landingRecs`, `Feasible.exists_admissible` |
| `ZenoFront/Bridge.lean` | Planes ending anywhere (bridge B3, Theorem 4.9): the variant's plans, cutting routes, the converse, the checker's soundness for the variant | `FeasibleAnywhere`, `cutRoute`, `FeasibleAnywhere.exists_admissible`, `Cert.check_sound_anywhere` |
| `ZenoFront/Achievability.lean` | Theorem 4.1 (achievability): the plan of an admissible partition, built on a rooted link forest; the fronts (Theorem 4.9, Corollary 4.8) | `Admissible.exists_plan`, `admissibleAchievable`, `minimal_achievable_iff_anywhere_of_A1`, `minimal_achievable_iff_multisetPoints` |
| `ZenoFront/AdmissibleBound.lean` | The σ-DP lower bound on admissible partitions, memoised, with dominance merging and states of size `≤ min(p − 1, t − p)` | `groupOption`, `sigmaDP`, `domRep`, `smallSubsetList`, `sigmaLayer`, `sigmaBoundAt` |
| `ZenoFront/LinkForest.lean` | Rooted link trees, Lemma 2.6 ("only if") by leaf removal | `LTree`, `LKids`, `LTree.groups`, `LTree.WF`, `Admissible.exists_linkForest` |
| `ZenoFront/TreeBound.lean` | The link-forest DP (Theorem 7.5, lower-bound direction), memoised by layers; the checker's `forest` gap bound, choosing it or the σ-DP | `buildLayers`, `TreeData`, `TreeData.value`, `treeBoundAt`, `useTreeDP`, `forestBoundAt` |
| `ZenoFront/Simulate.lean` | Computable plan check (mirrors `src/zeno/plan.cpp`) | `legOK`, `planeOK`, `pickLeg`, `follow`, `paxOK`, `planOK` |
| `ZenoFront/Checker.lean` | Pareto fronts, certificates, `check`, soundness | `achievable`, `IsParetoFront`, `Cert`, `Cert.check` |
| `ZenoFront/RationalPlans.lean` | Plans with rational times, rounding down, soundness against them | `QPlan`, `QFeasible`, `floorPlan`, `Cert.check_sound_rat` |
| `ZenoFront/CheckerV2.lean` | Format v2 (non-symmetric): certificates, `check`, soundness | `Kind2`, `Cert2`, `Cert2.check`, `Cert2.check_sound` |
| `ZenoFront/NonSymmetric.lean` | (A1-NS), splitting central flights, role weights of landing records, role shrinking (Lemma 4.4), Theorem 6.1 | `Network.A1NS`, `Feasible.split`, `RoleConfig.roleLoad`, `RoleConfig.exists_shrink`, `Feasible.exists_roleConfig_ns` |
| `ZenoFront/RoleBound.lean` | The `roles` bound (role relaxation), memoised | `roleLayers`, `rolesBoundAt`, `rolesBoundAt_le_totalCost` |
| `ZenoFront/LagrangianBound.lean` | The `lagrangian` bound at given multipliers; representatives of cities | `LagData`, `LagData.value_le_totalCost`, `domRep3`, `RoleConfig.map` |
| `ZenoFront/BalancedBound.lean` | The `balanced` program (DP over planes on the imbalance vector), lower-bound direction | `BalData`, `BalData.layers_dominate`, `BalData.value_le_totalCost` |
| `ZenoFront/Parse.lean` | Parser for both versions of the text format (untrusted) | `parseAnyCert`, `parseCert` |
| `ZenoFront/Examples.lean` | Two certificates checked by the kernel alone | `Examples.lptCounterexample_front` |
| `ZenoCheck.lean` | The `zeno-check` executable (untrusted wrapper) | `main` |

### Theorems

All of these are proved without `sorry`, and the kernel checks every one of them.

**Admissibility (`Admissible.lean`)**

* `IsParityWitness.card_add_one_le`: Lemma 2.5, `|h k| + 1 ≤ |X_k|` for every witness (forest
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

**Shrinking and merging (`Shrink.lean`)**

* `Admissible.exists_shrink` (SH, partition form): an admissible grouping with at least
  `s ≥ p` landings and `s ≡ p (mod 2)` contains an admissible grouping with exactly `s`
  landings.
* `IsParityWitness.size_mod_two`: an admissible grouping has `Σ_k |X_k| ≡ p (mod 2)`.
* `Admissible.map`: relabelling the cities by any map keeps a grouping admissible.

**Adding a plane (`AddPlane.lean`)**

* `Admissible.addPlane`, `Admissible.addPlane_of_size` (**Lemma 4.6, AP**): an admissible
  grouping of `q` planes with `2t − q` landings, `t ≥ q + 1`, gives an admissible grouping of
  `q + 1` planes with `2t − q − 1` landings, no larger cost, and loads within every bound on the
  old ones. One shrinking step removes two landings, and one of them becomes the new plane's
  group.
* `Admissible.addPlanes`: AP applied `m` times, from `q` to `q + m ≤ t` planes (step 4 of
  bridge B3).

**Converse (`Converse.lean`)**

* `PlaneFeasible.two_mul_load_landings_le` (**Step 1**): under (S) and (A1), a plane's flight
  time is at least `2 δ` of all its central landings.
* `countP_landingRecs_entry`, `countP_landingRecs_exit`, `PlaneFeasible.cntA_eq`: the segment
  types of the plan after Step 1, read off the routes. Landings entered from `C_I` are the legs
  `C_I → x`, landings exited towards `C_G` are the legs leaving `x` not towards `C_I`, and
  `#A = #Ā + 1` per plane (Lemma 2.1).
* `exists_transfer` (**cleaning**): every passenger route has a leg `C_I → x` followed by a leg
  leaving `x` not towards `C_I`.
* `Feasible.exists_admissible` (**Theorem 4.7**): under (S) and (A1), with `p ≤ t`, every
  feasible plan with cost `C` and makespan `M` yields an admissible partition with
  `Σ_k |X_k| = 2t − p`, `2 δ(X_k) ≤ M` for every plane, and `Σ_k c(X_k) ≤ C`.

The proof does Step 1, cleaning, DS, SH and PAR of the note without changing the plan.
* **Step 1:** a central leg counts as passing through `C_G`, and under (A1) it lasts at least
  the weights of its two endpoints.
* **Cleaning:** each passenger uses its last departure from `C_I` and the next leg.
* **DS:** all `A` and `Ā` landings are kept as crossings, and each city gets
  `min(#B, #B̄)` drop-off/pick-up pairs. This is at least as many passengers as DS selects. The
  count `passengers at x ≤ #A_x + min(#B_x, #B̄_x)` comes from two injections: passengers into
  landings entered from `C_I`, and passengers into landings exited towards `C_G`.
* **PAR**, then **SH** in partition form (`Admissible.exists_shrink`).

**Planes ending anywhere (`Bridge.lean`)**

* `Feasible.anywhere`, `achievable_subset_achievableAnywhere`: a feasible plan is a plan of the
  variant (`FeasibleAnywhere`: planes may end anywhere, the makespan is the last arrival), with
  the same cost and makespan.
* `exists_admissible_of_transfers` (`Converse.lean`): Theorem 4.7 for planes that all end in
  `C_G` and passengers that each have a transfer. The passengers' routes are not needed.
* `FeasibleAnywhere.exists_admissible` (**Theorem 4.9, B3**): under (S) and (A1), with `p ≤ t`,
  every plan of the variant with cost `C` and makespan `M′` yields an admissible partition with
  `Σ_k |X_k| = 2t − p`, `2 δ(X_k) ≤ M′` for every plane, and `Σ_k c(X_k) ≤ C`. Every route is
  cut after its last transfer leg and closed in `C_G` (`cutRoute`): after a final `C_I → x`, the
  flight `x → C_G` leaving on arrival is appended. Theorem 4.7 from transfers then applies to the
  planes that are not idle, and AP to the idle ones (`Admissible.addPlanes_le`).
* `Cert.check_sound_anywhere`: if `check` accepts, the listed points are the Pareto front of the
  variant, for every `dc` satisfying (A1). So the two fronts are equal on every certified
  instance (`Cert.minimal_achievable_iff_anywhere`).
* `minimal_achievable_iff_anywhere`: on every instance, the two fronts are equal under (S), (A1)
  and Theorem 4.1, taken as a hypothesis (`AdmissibleAchievable`). `Achievability.lean` proves
  it (`minimal_achievable_iff_anywhere_of_A1`).

**Achievability (`Achievability.lean`)**

* `Admissible.exists_plan` (**Theorem 4.1**): under (S), with `p ≤ t`, every admissible
  partition of `2t − p` landings is achieved by a feasible plan. Its planes land exactly at the
  groups (up to relabelling the planes), so it costs `c(X)`, and its makespan is
  `max_k 2 δ(X_k)`. On a rooted link forest, each plane drops off its children's passengers,
  crosses its free landings, then picks up its parent's passenger (`LTree.routes`).
* `admissibleAchievable`: Theorem 4.1 as `AdmissibleAchievable`.
* `minimal_achievable_iff_anywhere_of_A1` (**Theorem 4.9**): under (S) and (A1), the two fronts
  are equal on every instance.
* `minimal_achievable_iff_admissiblePoints`, `minimal_achievable_iff_multisetPoints`
  (**Corollary 4.8**): under (S) and (A1), the front is `Min 𝒳`, with `𝒳` the points
  `(c(X), M(X))` of the multisets of `2t − p` landings that have an admissible partition.
  `minimal_achievableAnywhere_iff_admissiblePoints` is the same for planes ending anywhere.

**Forest bound (`AdmissibleBound.lean`)**

* `groupOption_le_cost`: a group with witness set `H` costs at least
  `c(H) + G[m − |H|][T − δ(H)]`.
* `sigmaDP_le_totalCost`: the σ-DP over planes, with state the odd-degree city set `σ`, is at
  most the cost of every admissible grouping whose witness lies in `R`.
* `domRep_le`: cities are merged into non-dominated representatives (no slower, no more
  expensive). This keeps the bound valid and makes the city set small: at most 4 cities on the
  samples.
* `mem_smallSubsetList`: the σ-DP's states are the subsets of the non-dominated cities of size
  `≤ min(p − 1, t − p)`. Claim B′ (`Admissible.exists_card_touched_le`) gives every admissible
  grouping a witness whose odd-degree sets all stay in that family.
* `sigmaLayer_getD`, `sigmaValue_eq`: the memoised σ-DP agrees with `sigmaDP`.
* `sigmaBoundAt_le_totalCost`: the σ-DP bound is at most the cost of every admissible partition
  into `p` groups of total size `s` with loads `≤ T`.

**Link forests (`LinkForest.lean`)**

* `Admissible.exists_linkForest` (**Lemma 2.6, "only if"**): the groups of an admissible
  grouping are, as a multiset, the groups of a list of rooted link trees in which every plane
  keeps an odd number of free landings. The proof removes a leaf and recurses on the planes:
  * a plane with an empty witness set is an isolated vertex;
  * otherwise a witness with the fewest edges has a plane with exactly one city
    (`IsParityWitness.exists_card_eq_one_of_minimal`, from the rank bound of
    `MinimalWitness.lean`);
  * that plane is hung back by a link (`attachForest`).

**Tree DP (`TreeBound.lean`)**

* `buildLayers_getD`: a table built layer by layer, each layer read from the earlier ones,
  unfolds to its defining formula.
* `TreeData.chM_le`, `subM_le`, `rootM_le`, `forM_le`: one step of each table `Ch`, `Sub`,
  `Root`, `For` (§7.4).
* `LKids.chM_le`, `LTree.subM_le`, `LTree.rootM_le`, `forM_le_forest`: by induction on the
  rooted link trees, child items, subtrees, trees and forests cost at least their table entry.
  The free landings of a plane, of odd size, cost at least the one-plane entry for the budget
  the links leave.
* `TreeData.value_le_totalCost`, `treeBoundAt_le_totalCost` (**Theorem 7.5, `For ≤ E`**): the
  tree DP is at most the cost of every admissible partition into `p` groups of total size `s`
  with loads `≤ T`. The converse (`For ≥ E`) is not needed.
* `forestBoundAt_le_totalCost`: the bound the checker computes (tree DP or σ-DP, chosen by
  `useTreeDP`) is such a lower bound.

**Checker (`Simulate.lean`, `Checker.lean`, `Examples.lean`)**

* `planOK_feasible`: a plan accepted by the simulation is feasible, for every `dc`.
* `follow_sound`: the greedy passenger walk, when it uses all the passenger's legs, orders them
  into a route.
* `Feasible.minOf_le_makespan` (**obligation 2**): under (S), every feasible plan has makespan
  `≥ 2 · d_min · ⌈s/p⌉`.
* `Feasible.minOf_le_cost` (**obligation 4**): under (S), every feasible plan costs
  `≥ s · c_min`.
* `Cert.gapBound_le` (**obligation 3**, `relaxed`): a feasible plan with makespan below `M`
  costs at least the relaxed bound at the gap level of `M`, for every `dc`.
* `Cert.forestGapBound_le` (**obligation 3**, `forest`): under (A1), a feasible plan with
  makespan below `M` costs at least the forest bound at the gap level of `M`. The proof chains
  Theorem 4.7 and `forestBoundAt_le_totalCost`.
* `exists_le_of_gapsOK`: the domination argument along the front.
* `Cert.check_sound` (**soundness**): `C.check = true` implies
  `IsParetoFront (achievable (C.network dc) C.c C.t C.p) C.front`. That is, every point is
  achieved by a feasible plan, every feasible plan is weakly dominated by a point, and the points
  are pairwise incomparable. It holds for every `dc` satisfying (A1), or for every `dc` if all
  gaps are `relaxed`.
* `Cert.check_sound_A1`, `Cert.check_sound_relaxed`: the two cases of `check_sound`.
* `IsParetoFront.mem_iff_minimal`, `Cert.check_sound_minimal`: equivalently, a pair is listed
  iff it is a minimal achievable (cost, makespan) pair.

**Non-symmetric instances (`PlanBounds.lean`, `NonSymmetric.lean`, `RoleBound.lean`,
`LagrangianBound.lean`, `CheckerV2.lean`)**

* `Feasible.exists_relaxation_emin` (**Lemma R, any durations**): a segment starts and ends with
  hub flights, so its kept landing weighs `2 min(d, d̄)`. No assumption.
* `Feasible.split`: under (A1-NS), splitting every central flight `a → b` into `a → h → b`
  (`h` the hub of the shorter detour) keeps a plan feasible, with the same cost, no larger
  makespan and no central flight.
* `roleW_landingRecs_le`: on a route without central flights, each landing's two legs last
  exactly its role weight (crossing `d + d̄`, drop-off `2d`, pick-up `2d̄`).
* `Feasible.exists_roleConfig_records`: direct selection (Lemma 4.3(b)), shared by Theorems 4.7
  and 6.1. `RoleConfig.exists_shrink`: Lemma 4.4 in role form.
* `Feasible.exists_roleConfig_ns` (**Theorem 6.1**): under (A1-NS), every feasible plan gives a
  role configuration on the `p` planes with passenger count `t`, cost at most the plan's and
  every role load at most its makespan.
* `rolesBoundAt_le_totalCost`: the role relaxation is a lower bound on such configurations. It
  takes the larger of two bounds. Per plane: an odd number of crossings, other landings at
  `2 min(d, d̄)`. All planes: the role loads add up to the crossing weight of all landings, by the
  balance (`sum_roleLoad_eq_load_fill`).
* `LagData.value_le_totalCost`: for every integer multiplier, the decoupled per-plane bound
  (drop-off `c + μ`, pick-up `c − μ`) is a lower bound on every balanced configuration.
* `domRep3`, `RoleConfig.map`: configurations are mapped to representatives no slower to either
  hub and no more expensive. These are cities the C++ reduction keeps, and the level scale is
  their gcd, as in the C++ checker.
* `Cert2.check_sound` (**soundness, format v2**): if `Cert2.check` accepts, the listed points
  are exactly the Pareto front. This holds for every table of central flights satisfying
  (A1-NS) when the certificate lists it (`Cert2.check_sound_A1NS`), and for every table
  otherwise (`Cert2.check_sound_of_not_A1NS`). The kinds it verifies:
  * gaps: `relaxed`, `roles`, `lagrangian` and `balanced`;
  * fastest point: `closed`, `relaxed`, `roles` and `balanced`.

  It rejects `search` and `forest`.
* `BalData.value_le_totalCost` (**`balanced`**): the program of `BalancedRoles` (a DP over the
  planes, on states made of the imbalance vector and the landings so far) is at most the cost of
  every balanced configuration with `s` landings and role loads `≤ T`. A drop-off and a pick-up
  at the same city of one plane count as two crossings. Every plane's imbalance and every
  prefix's then have norm at most `t − p` (`norm_delta_le`, `norm_prefix_le`), so the program's
  restriction to such options and states loses nothing.

**Rational times (`RationalPlans.lean`)**

* `QFeasible.floor`: a feasible plan with rational departure and arrival times, every time
  rounded down, is a feasible plan with integer times. Durations are integers, so
  `arr = dep + d` gives `⌊arr⌋ = ⌊dep⌋ + d`, and every `arrival ≤ next departure` survives.
* `planMakespan_floor_le`, `qPlanCost_eq`: the rounded plan has the same cost and no larger
  makespan. `Feasible.toRat`: an integer plan is a rational one, with the same cost and
  makespan.
* `Cert.check_sound_rat`: if `check` accepts, the listed points are exactly the Pareto front of
  the (cost, makespan) pairs of the feasible plans **with rational times**, under the same
  hypotheses on `dc` as `check_sound`.
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

  It is the `T`-join of Lemma 2.4, as a 0/1 matrix. It need not be a forest. A witness found by
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
  keeps every city. A `relaxed` gap passes iff `C_i ≤ L(level)`, with `L = ∞` when no grouping
  fits.
* **`forest` gaps.** These need `A1` among the assumptions. A gap passes iff `C_i ≤ E(level)`,
  where `E` is the least cost of an admissible partition. The C++ solver computes `E` with the
  link-forest DP. The Lean checker computes it with the σ-DP over the non-dominated cities.
  Both are exact, and they agree on every sample. The Lean side proves only the lower-bound
  direction, which is all soundness needs.

## Trust assumptions

* **Theorems.** Every theorem is checked by the Lean kernel and depends only on `propext`,
  `Classical.choice` and `Quot.sound`. The axiom audit enforces this. The examples use `decide`,
  which the kernel evaluates; `native_decide` is not used anywhere.
* **Statements.** The definitions are the trusted interface: a theorem is only as good as the
  match between them and the intended mathematics. For the checker these are `Feasible`,
  `planCost`, `planMakespan`, `achievable` and `IsParetoFront`. The docstrings tie each
  definition to the note and the format.
* **Plan semantics.** The certificate's plans have natural-number times, as in format v1.
  `Cert.check_sound` quantifies over every plan with integer times, and `Cert.check_sound_rat`
  over every plan with rational times; the fronts coincide. Durations are the instance's
  integers in both.
  * Plans may fly central–central legs of any duration `dc`, may wait anywhere and may hand
    passengers over anywhere.
  * Planes must end in `C_G` in `Cert.check_sound` (the format's semantics).
    `Cert.check_sound_anywhere` lets them end anywhere, with the last arrival as makespan (PDDL
    without plane goals), for every `dc` satisfying (A1) (bridge B3).
  * With `forest` gaps, the theorem assumes (A1) on `dc` (`dc i j ≥ d i + d j`, including
    `i = j`). Every PDDL file the generator emits satisfies it.
  * Version 2: with `roles` or `lagrangian` bounds, which need `A1-NS` listed,
    `Cert2.check_sound` assumes (A1-NS) on `dc` (`dc i j ≥ min(d_i + d_j, d̄_i + d̄_j)`).
    Otherwise it holds for every `dc`. Plans must end in `C_G` here: bridge B3 is done for format v1 only.
* **Parser.** `parseAnyCert` and `ZenoCheck.lean` are **outside the verified statement**.
  `Cert.check_sound` and `Cert2.check_sound` are about the parsed values, so a parser bug could make the checker verify a
  different front than the file's. The parser only translates numbers and `1`-based indices; it
  mirrors `readCertificate` in `src/zeno/certificate.cpp`.
* **Compiled checker.** `lake exe zeno-check` runs `Cert.check` as compiled code. Its verdict
  therefore also trusts the Lean compiler and runtime, not only the kernel. Only the soundness
  theorem is kernel-checked. To avoid that trust, a certificate can be checked by the kernel
  with `decide +kernel`, as `Examples.lean` does. That is practical for small certificates only.

## TODO

Remaining items of the formalisation plan (proof review, §4). Theorem 4.1 (achievability) is not
needed for soundness: the plan of every listed point is checked by simulation.

**P1, combinatorial core (rest).**

- [x] SH in partition form (`Admissible.exists_shrink`); the role-configuration form is not
      needed.
- [x] AP (add a plane, Lemma 4.6; `Admissible.addPlane`, `Admissible.addPlanes`).
- [x] The σ-DP as a lower bound on `E(T)` (`sigmaBoundAt_le_totalCost`).
- [x] The σ-DP's state bound `|σ| ≤ min(p − 1, t − p)` from Claim B′ (`smallSubsetList`).
- [ ] The σ-DP's other direction (`DP ≥ E`, so the DP is exact). Not needed for soundness.
- [ ] `E(T)` as a definition and its monotonicity; pairs upper bound `U(T)` with `L ≤ E ≤ U`.
- [ ] Bellman-potential soundness: potentials with `φ(src) ≤ 0` and `φ(v) ≤ φ(u) + w(u, v)` on
      every arc bound `E(T)` from below (sparse certificates).
- [ ] Executable admissibility check (union–find on the plane–city graph) proved equal to
      `Admissible`. This needs Lemma 2.4 (component form ⇔ parity witness).

**P2, plan semantics and the relaxation.**

- [x] Route-based plans with `ℕ` times (`Plan.lean`), matching format v1, with arbitrary
      central flights.
- [x] Counting (Lemma 3.2) by leg counting (`Feasible.le_sum_hubArrivals`).
- [x] Segments and the endpoint bound under (S) (`PlaneFeasible.exists_segments`).
- [x] Lemma R (`Feasible.exists_relaxation`), and `L` as a DP proved a lower bound.
- [x] Primal checker (`planOK_feasible`) and the end-to-end checker, with a parser and
      `zeno-check`.
- [x] Rational times for the competitor plans (`Cert.check_sound_rat`).
- [ ] Completeness of the simulation: the greedy passenger walk finds a route whenever the
      C++ one does. Only soundness is proved.

**P3, Theorem 4.7 (converse under (S) + (A1)).**

- [x] Step 1, cleaning, DS, SH and PAR, done directly on the routes
      (`Feasible.exists_admissible`).
- [x] Front theorem X3 for `forest` gaps (`Cert.check_sound`, `Cert.check_sound_A1`).

**P4.**

- [x] Checker performance at suite scale: the 66 suite certificates in 5.7 s (478 s before).
- [x] Bridge B3: the PDDL semantics (planes end anywhere, makespan = last action) has the same
      front under (S) + (A1) (`FeasibleAnywhere.exists_admissible`, `Cert.check_sound_anywhere`).
      On every instance, with Theorem 4.1: `minimal_achievable_iff_anywhere_of_A1`.
- [x] Theorem 4.1: links, schedule with drop-offs first and at most one pick-up per plane,
      makespan = largest load (`Admissible.exists_plan`), and Corollary 4.8. Not needed by the
      checker.
- [x] Link-forest lemma (2.6, only if; `Admissible.exists_linkForest`) and the tree DP
      (Theorem 7.5) as a lower bound (`treeBoundAt_le_totalCost`).
- [ ] Pareto staircases over `τ` in the tree DP, as in `src/zeno/forest.cpp`. The dense tables
      take seconds when many cities survive the merge (table above); the C++ checker takes
      milliseconds.
- [ ] Pareto-semiring DP (PS); closed-form ends of the front.

**P5, non-symmetric.**

- [x] Format v2: parser, non-symmetric Lemma R (`relaxed`), and soundness for every table of
      central flights (`Cert2.check_sound`).
- [x] Role model with role loads; N1 (Theorem 6.1, `Feasible.exists_roleConfig_ns`); the
      `roles` and `lagrangian` bounds.
- [x] `balanced` (`BalData.value_le_totalCost`). The Lean checker accepts all 150
      certificates of random small non-symmetric instances, with the C++ checker's verdicts and
      bound values.
- [ ] `search`: Lemma 6.3 (the template schedule), Theorem 6.9 and Corollary 6.10, and an
      exhaustive search over role configurations with exact schedules.
- [ ] W1 (a single pick-up never waits harmfully); simulation with waiting; Conjecture 6.2 if it
      is proved.
