# Contributing

## Commits and pull requests

Code, build, tests and prose use [Conventional Commits](https://www.conventionalcommits.org/)
(`feat`, `fix`, `perf`, `docs`, ...). Commits that assert a mathematical claim or an empirical
finding use Conventional Knowledge Commits (CKC), a strict superset of Conventional Commits for
proofs and scientific findings. Spec: https://conventional-knowledge-commits.org/

- The profiles `proof` and `science` are active (`.ckc.toml`).
- Pull request titles are checked by `ckc-lint` (`.github/workflows/pr-title.yml`), so both
  `fix: keep the best plan` and `formalize(lean): prove Lemma 2.6` pass.
- Pull requests are merged with merge commits, never squashed: the ClaimGraph is rebuilt from the
  individual commits.

## Conventional Knowledge Commits

### The rules we follow

- One claim per commit. A commit asserts a single definition, lemma, theorem, conjecture,
  refutation, experiment or result.
- Grammar: `<type>[~][(scope)][!]: <description>`, then a body, then footers (git trailers).
- Pick the type from the right profile:
  - proof: `state`, `proof`, `formalize`, `axiomatize`, `strengthen`, `generalize`, `weaken` (`!`),
    `port`;
  - science: `experiment`, `result`, `replicate`, `null`, `data`, `protocol`, `method`,
    `analysis`, `repro-fix`;
  - shared: `conjecture`, `lit`, `review`, `refute` (`!`), `retract` (`!`), `expose`, `meta`.
- Set the epistemic `Status:` footer:
  - `math.machine-checked`: a clean Lean kernel proof, whose `Axioms:` line shows only
    `propext`, `Classical.choice` and `Quot.sound`;
  - `math.proved-informal`: a complete written proof in the note, no complete Lean proof;
  - `math.conjectured`: open, or only sketched;
  - `math.open`: a Lean statement whose proof still has a `sorry`;
  - `math.disproved`: refuted;
  - science: `sci.hypothesis`, `sci.measured`, `sci.supported`, `sci.falsified`, ...
- Build the ClaimGraph with relation footers: `Depends-On`, `Assumes`, `Proves`, `Closes`,
  `Refutes`, `Disproves`, `Supersedes`. Reference a claim by its `claims.toml` slug
  (`claim:<slug>`, `conjecture:<slug>`) or by a Lean fully qualified name, never by a commit hash.
- When the status is not clean, add `~` to the type and an uppercase marker footer: `AXIOM:`,
  `OPEN:`, `ASSUMES:`, `UNREPLICATED:`.
- Honesty: never claim `math.machine-checked` while a `sorry`, `sorryAx` or a non-standard axiom
  is present. A status changes only by a new commit, never by editing an old one. A
  counterexample is a `refute` commit, never a `fix`.

### The claim ledger

`claims.toml` lists every claim of the theory note `doc/theory/exact-front.md`, the two claims of
the papers it corrects, and the experiments. Slugs are `<kind>-<number with dots as dashes>`,
with the kind read from the note's own label: `def`, `lem`, `thm`, `prop`, `cor`, `conj`, or
`claim` for a Statement or a statement located by its section. Theorem 4.7 is `thm-4-7` and the
end of §6.2 is `claim-6-2-end`. A statement the note does not number gets a descriptive slug, as
`claim-converse-s-only`. Experiments are `exp-<id>`. The file's header gives the fields.

How each kind of record is written here:

- **Kernel-checked**: `formalize(lean): ...` with `Lean: <declaration>`,
  `Status: math.machine-checked`, `Axioms: <the literal #print axioms output>` and
  `Closes: claim:<slug>`. Its `Depends-On:` lists only claims that are themselves kernel-checked.
  Steps that the note proves in writing and the Lean proof does another way are named in the
  body. A claim is kernel-checked only if its Lean declarations prove every assertion of the
  note's statement, up to the Lean model's encoding: natural-number data and times, (S) as
  d̄ = d, (A1) as `Network.A1`, the standing assumption p ≤ t, passenger counts as landing counts.
  The body and the entry's `statement` give that encoding as the "Lean form". A missing clause, a
  weaker bound or a different object (another graph, the makespan for a flight time) makes it a
  written proof with `lean_partial`, however routine the gap looks.
- **Written proof**: `proof(theory): ...` with `Claim-ID: <slug>` and
  `Status: math.proved-informal`. If Lean proves only part of it, the entry's `lean_partial`
  names those declarations.
- **Open or sketched**: `conjecture(theory): ...` with `Status: math.conjectured`; a sketch also
  carries `~` and an `OPEN:` footer that says what is missing.
- **Refutation**: `refute(<topic>)!: ...` with `Disproves: conjecture:<slug>`,
  `Status: math.disproved` and a `BREAKING-CHANGE:` footer. Spell it with the hyphen: git does not
  read `BREAKING CHANGE` as a trailer, and then ignores the whole footer block.
- **Experiment**: `experiment(<id>): ...` with a `sci.*` status, `Verified-By:` and
  `Closes: claim:exp-<id>`.
- **Status correction**: `review(<scope>): ...` with `Claim-ID: <slug>` and the corrected
  `Status:`, the body saying what was wrong. The statement itself is unchanged, so it takes no
  `!`. A review that confirms a status carries no `Status:` footer.

When a claim changes status, the same pull request updates the note, its entry in `claims.toml`
(the `status` cache) and records the change in a new commit.

### Validate before committing

```bash
# The message: header, types, Status vocabulary, markers.
uvx --from git+https://github.com/hotherio/ckc-tools ckc-lint .git/COMMIT_EDITMSG

# For a formalize commit, the Axioms: line is the output of #print axioms on the declaration,
# run with `lake env lean` (from lean/, after `lake build`) on a file that imports ZenoFront.
# The audit of the whole library:
(cd lean && lake env lean scripts/CheckAxioms.lean)
```

`ckc-axiom-check .git/COMMIT_EDITMSG`, from the same package, cross-checks a `machine-checked`
message against the kernel when `axiom-report` is installed.

### The ClaimGraph

The graph is rebuilt from the history and `claims.toml`:

```bash
CG="uvx --from git+https://github.com/hotherio/claimgraph claimgraph"
$CG status . --claims claims.toml           # claims grouped by effective status
$CG effective thm-4-7 . --claims claims.toml # asserted vs effective status, weakest dependency
$CG affected lem-4-4 . --claims claims.toml  # what a refutation would put in question
$CG export . --claims claims.toml -o claimgraph.html  # HTML viewer with the timeline
```

A claim's effective status is the weakest status over its `Depends-On` closure. The commits that
predate the ledger are plain Conventional Commits; their scopes (`lean`, `theory`, ...) show up as
nodes without a status and carry no claim.

### Example commits

A kernel-checked theorem:

```
formalize(lean): Theorem 4.10, every plan is dominated by an admissible partition

Lean form: under the triangles through a hub (Network.ATriHub), which (AΔ) and (A1) imply.

Lean: ZenoFront.Feasible.exists_admissible_hub
Status: math.machine-checked
Axioms: 'ZenoFront.Feasible.exists_admissible_hub' depends on axioms: [propext, Classical.choice, Quot.sound]
Closes: claim:thm-4-10
Depends-On: claim:lem-4-11
```

A written proof:

```
proof(theory): Lemma 3.1, every plan can be cleaned

Claim-ID: lem-3-1
Status: math.proved-informal
```

A refutation:

```
refute(greedy)!: the per-PPP greedy of both papers is not optimal

Disproves: conjecture:paper-greedy-optimal
Status: math.disproved
Depends-On: claim:claim-5
BREAKING-CHANGE: conjecture:paper-greedy-optimal is withdrawn.
```
