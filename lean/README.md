# ZenoFront: Lean formalisation of the exact MultiZenoTravel front

`ZenoFront` is a Lean 4 / Mathlib library that formalises the combinatorial core of the exact
Pareto-front solver for symmetric MultiZenoTravel. The informal proofs are in
[`doc/theory/exact-front.md`](../doc/theory/exact-front.md); the statements follow the IDs of
the proof review (Claim A, PAR, Claim B′, G).

This first part covers the combinatorial core, with no time and no plans: admissibility, role
configurations, the support bound and the one-plane table. Section [TODO](#todo) lists the rest.

## Build

Toolchain: Lean `v4.36.0`, Mathlib `v4.36.0` (pinned in `lakefile.toml` and `lake-manifest.json`).

```sh
cd lean
lake exe cache get        # download the Mathlib build cache (never build Mathlib from source)
lake build --wfail        # build ZenoFront; warnings, including `sorry`, are errors
lake env lean scripts/CheckAxioms.lean   # axiom audit
```

The axiom audit fails if any declaration of a `ZenoFront` module uses an axiom other than
`propext`, `Classical.choice` and `Quot.sound`. It rejects `sorryAx` and `native_decide`.
CI (`.github/workflows/lean.yml`) runs these three steps, plus a `grep` for `sorry` and `admit`,
on every push and pull request that touches `lean/**`.

## Contents

| File | Content | Main declarations |
|---|---|---|
| `ZenoFront/Model.lean` | Instance (`n` cities, `d c : Fin n → ℕ`, `t` passengers, `p` planes, `1 ≤ p ≤ t`), `s = 2t − p`, groupings `X : Fin p → Multiset (Fin n)`, load `δ`, cost | `Instance`, `Instance.s`, `Groups`, `load`, `cost`, `size`, `totalCost`, `maxLoad` |
| `ZenoFront/Admissible.lean` | Admissibility as Claim A (parity witnesses), decision procedure, Lemma 2.3, examples | `IsParityWitness`, `Admissible`, `witnessCandidates` |
| `ZenoFront/Roles.lean` | Role configurations, PAR and its converse | `RoleConfig`, `RoleConfig.groups`, `RoleConfig.witness` |
| `ZenoFront/SupportBound.lean` | Claim B′, `t − p` part | `touched`, `edgeCount` |
| `ZenoFront/MinimalWitness.lean` | Claim B′, `p − 1` part, and the combined `min(p − 1, t − p)` bound | `edgeVec`, `coordSum` |
| `ZenoFront/OnePlane.lean` | One-plane table `G[m][T]`: specification and memoised table | `oneplane`, `oneplaneTable` |

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

## Conventions the C++ side must match

The future certificate format and checker will build on these definitions.

* **Indices.** Cities are `Fin n` and planes are `Fin p`, both numbered from `0`.
* **Durations and costs.** Durations and costs are natural numbers: `d i` is the *one-way*
  duration between a hub and city `i`, after any gcd scaling.
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
* **Infinity.** The one-plane table uses `WithTop ℕ`, with `⊤ = ∞`. `ℕ∞` is not used because
  its lattice instance is not computable. The C++ table must agree on
  `G[0][T] = 0` and `G[m + 1][T] = min_{i : d_i ≤ T} (c_i + G[m][T − d_i])`, the minimum over
  no city being `∞`.

### Certificate format v1

The solver writes certificates in the format of `doc/certificate-format.md`, on branch
`feat/exact-front-solver` (not yet on `master`). A Lean checker of that format would reuse the
following:

* **Header.** `Instance` holds the header (`instance n t p`, `d`, `c`; under `assume S`,
  `dbar = d`), and `Instance.s` is the `s = 2t − p` of obligations 2 to 4. The format numbers
  cities `1..n` (locations `0` = `C_I`, `n + 1` = `C_G`) and planes and passengers from `1`.
  `Fin n` and `Fin p` count from `0`, so the parser subtracts one.
* **Gap levels.** The table and the DPs work on the scaled instance: durations divided by their
  gcd `g`, at the format's level `T = ⌊⌊(M_{i+1} − 1)/2⌋ / g⌋`. Its `d` is that scaled `d`.
* **`relaxed` gaps.** `L(T)` is a DP over planes whose entries are the one-plane table, so it
  reuses `oneplane` / `oneplaneTable` and their specification `isLeast_oneplane`. Its soundness,
  Lemma R, needs plan semantics (P2), but not admissibility.
* **`forest` gaps.** `E(T)` is a minimum over admissible groupings: `Groups`, `size`, `load`,
  `cost` and `Admissible`. Its soundness goes through the converse theorem. That is DS, then PAR
  (`RoleConfig.isParityWitness_witness`), then the link-forest lemma (P3, P4), and the forest DP
  also reuses `oneplane`.
* **Claim B′.** Claim B′ (`Admissible.exists_card_touched_le`) bounds the σ-DP, which v1 does not
  emit. It becomes relevant if a `sigma` bound kind is added.
* **Plans (obligation 1).** Plans are full leg lists with integer times, so P2 can use `ℕ` times
  for v1.

## Trust assumptions

* **Theorems.** Every theorem is checked by the Lean kernel and depends only on `propext`,
  `Classical.choice` and `Quot.sound`. The axiom audit enforces this. The examples use `decide`,
  which the kernel evaluates; `native_decide` is not used anywhere.
* **Statements.** The definitions above are the trusted interface: a theorem is only as good as
  the match between `Admissible`, `RoleConfig` and `oneplane` and the intended mathematics. The
  docstrings tie each definition to the note.
* **Future compiled checker (not written yet).** The checker will run on benchmark certificates
  as a compiled Lean executable, or through `native_decide`. It will then also trust the Lean
  compiler and runtime (`Lean.ofReduceBool`), not only the kernel. Its soundness theorem will be
  kernel-checked; only its execution on large inputs will rely on the compiler.

## TODO

Remaining items of the formalisation plan (proof review, §4). The P1 items have no time and no
plans; P2 and later need plan semantics.

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
- [ ] Lower bound `L(T)` (drops admissibility) and pairs upper bound `U(T)`, with `L ≤ E ≤ U`.
- [ ] Bellman-potential soundness: potentials with `φ(src) ≤ 0` and `φ(v) ≤ φ(u) + w(u, v)` on
      every arc bound `E(T)` from below.
- [ ] Executable dual checker over a certificate format, with a soundness proof.
- [ ] Executable admissibility check (union–find on the plane–city graph) proved equal to
      `Admissible`. This needs Lemma 2.2 (component form ⇔ parity witness).

**P2, plan semantics and the relaxation.**

- [ ] Route-based plans: per plane a list of legs (source, destination, departure and arrival
      times; integers suffice for certificate format v1, `ℚ` in general); per passenger an
      explicit list of legs; feasibility (chaining, capacity one, planes end in `C_G`), cost and
      makespan, matching the plan semantics of `doc/certificate-format.md`.
- [ ] Lemma 2.1 and counting (Lemma 3.2): at least `2t − p` landings, by leg counting.
- [ ] Segments and the endpoint bound (Lemma 3.3 under (S)).
- [ ] Lemma R: under (S) alone every plan `(C, M)` has `C ≥ L(⌊M/2⌋)`.
- [ ] Decidable primal checker (a plan is feasible with the claimed cost and makespan).
- [ ] First end-to-end verified fronts, wherever `L`-certificates close.

**P3, Theorem 4.3 (converse under (S) + (A1)).**

- [ ] Step 1: removing central flights under (A1).
- [ ] Cleaning (Lemma 3.1) as a suffix/prefix operation on passenger routes.
- [ ] Hand-off abstraction (M6): `o` and `n` injective, hand-offs at a common city.
- [ ] DS (direct selection) from a simple plan to a role configuration, then M7 via DS, SH, PAR.
- [ ] Front theorem X3: the checker accepts ⇒ the listed points are achieved, weakly dominate
      every plan and are strictly monotone.

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
