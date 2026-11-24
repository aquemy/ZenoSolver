# Front certificates, format versions 1 and 2

`zeno --certificate FILE` writes, next to the front, a certificate that a checker can verify without trusting the solver. The reference checker is `zeno check FILE`; the Lean checker in `lean/` (`lake exe zeno-check FILE`), whose soundness is proved in Lean, reads the same format. This page defines the format and what a checker must verify. The proofs behind each obligation are in `doc/theory/exact-front.md`.

## What a certificate proves

For an instance with symmetric durations and a front $(C_1, M_1), \dots, (C_r, M_r)$ with $M_1 < \dots < M_r$ and $C_1 > \dots > C_r$, the certificate shows that this list is exactly the Pareto front:

1. **Achieved.** For every $i$, the plan given for point $i$ is feasible and has cost $C_i$ and makespan $M_i$. The checker simulates it.
2. **Nothing is faster than $M_1$.** $M_1 = 2\, d_{\min} \lceil s/p \rceil$, where $s = 2t - p$. Every plan has at least $s$ segments (counting lemma), some plane flies at least $\lceil s/p \rceil$ of them, and under (S) each lasts at least $2 d_{\min}$.
3. **Nothing in a gap is cheaper.** For every $i < r$, every plan with makespan $< M_{i+1}$ costs at least $C_i$. Such a plan has $\lfloor M/2 \rfloor \le h = \lfloor (M_{i+1} - 1)/2 \rfloor$; with $g$ the gcd of the durations, its groups fit in level $T = \lfloor h / g \rfloor$ of the instance with durations divided by $g$ (for a front point $M_{i+1} = 2gT_{i+1}$, so $T = T_{i+1} - 1$). As $E$ and $L$ are non-increasing, it suffices that the bound at level $T$ is at least $C_i$. The certificate names how the checker establishes this bound:
   - `relaxed`: recompute the relaxation $L(T)$ (no admissibility). Lemma R gives $\text{cost} \ge L(\lfloor M/2 \rfloor)$ for every plan under (S) alone, whatever the central flights.
   - `forest`: recompute $E(T)$ with the link-forest dynamic program (trees of at most $\min(p, t-p+1)$ planes). This relies on the converse theorem, hence on (A1).
4. **Nothing is cheaper than $C_r$.** $C_r = s \cdot c_{\min}$: every plan lands at least $s$ times.

Then every plan $(C, M)$ is weakly dominated by a listed point: $M \ge M_1$ by 2; if $M_i \le M < M_{i+1}$ then $C \ge C_i$ by 3; if $M \ge M_r$ then $C \ge C_r$ by 4. Together with 1, the list is the front.

A certificate whose gap bounds are all `relaxed` is valid for every symmetric instance, without assumption (A1).

## Syntax

A text file of lines. Blank lines and lines starting with `#` are ignored. Tokens are separated by spaces. All numbers are non-negative integers.

```
zeno-certificate 1
instance <n> <t> <p>
d <d_1> ... <d_n>
dbar <dbar_1> ... <dbar_n>
c <c_1> ... <c_n>
assume <assumption>...
front <r>
<C_1> <M_1>
...
<C_r> <M_r>
plan <i> <p>
plane <k> <m>
<from> <to> <depart> <arrive> <passenger>
...
lower-bounds <r - 1>
<i> <kind>
...
end
```

- `d`: durations between $C_I$ and each central city; `dbar`: between $C_G$ and each central city; `c`: landing costs.
- `assume`: the assumptions the solver used. Version 1 knows `S` (symmetric durations, i.e. `d` = `dbar`) and `A1` (central flights at least as long as through a hub). A checker refuses an obligation that needs an assumption the certificate does not list.
- `front`: the points by increasing makespan.
- `plan <i> <p>`: the plan of point $i$ (1-based), for the $p$ planes, in order $i = 1..r$. Each `plane <k> <m>` (k = 1..p, in order) is followed by its $m$ legs, in flight order.
- A leg: locations are `0` for $C_I$, `1`..`n` for the central cities, `n+1` for $C_G$; times are integers; `passenger` is `1`..`t`, or `0` when the plane flies empty.
- `lower-bounds`: one line per gap $i = 1..r-1$, in order, with its kind, `relaxed` or `forest`.
- Limits of the reference reader: every number at most $2^{36}$, $n, t, p \le 10^5$, at most $10^7$ legs in all.

## Plan semantics (obligation 1)

A plan is feasible when:

- every plane starts in $C_I$ at time $\ge 0$; each leg leaves the location where the previous one arrived, no earlier than that arrival; each leg is a flight between a hub ($C_I$ or $C_G$) and a central city, lasting `d` (via $C_I$) or `dbar` (via $C_G$) — there is no $C_I$–$C_G$ flight, and version 1 has no central-to-central legs; every plane ends in $C_G$;
- every passenger $1..t$ starts in $C_I$ at time 0 and rides a chain of legs, each leaving where the previous one arrived and no earlier, ending in $C_G$;
- a leg carries at most one passenger (by construction of the format).

Boarding and debarking take no time. The cost is the sum of `c` over the legs that land in a central city; the makespan is the last arrival.

## Example

`zeno -n 2 -t 5 -p 2 -d tests/golden/data/lpt-counterexample.dat --certificate lpt.cert` writes a certificate for the instance $d = (6, 10)$, $c = (40, 20)$, $t = 5$, $p = 2$, whose front has six points; `zeno check lpt.cert` verifies it.

## Version 2: non-symmetric instances

`zeno --certificate FILE` on a non-symmetric instance writes a version 2 certificate when its bracket is exact (every gap closed). Version 2 differs from version 1 in four places.

- The header is `zeno-certificate 2`, and `dbar` may differ from `d`. `assume` lists `S` only for symmetric durations, and `A1-NS` when a bound below needs it (Theorem 6.1 of the theory note: every plan is weakly dominated by a role configuration with the same cost and loads at most its makespan, if central flights are useless).
- Levels are in units of the gcd g of all durations, and are full loads: a crossing $C_I \to i \to C_G$ or back weighs $d_i + \bar d_i$, a drop-off $2 d_i$, a pick-up $2 \bar d_i$. A plan of makespan $< M_{i+1}$ fits in level $T = \lfloor (M_{i+1} - 1)/g \rfloor$. (For symmetric durations, version 1's half-loads and level $\lfloor (M_{i+1}-1)/(2g) \rfloor$ are kept.)
- A line `fastest <kind>` after the front names the bound that rules out plans faster than $M_1$: the bound at level $\lfloor (M_1 - 1)/g \rfloor$ must be infinite. Kinds: `closed` (symmetric only, as in version 1), `relaxed`, `roles`, `balanced`, `search`.
- Gap kinds, in addition to `relaxed` (lemma R with weight $\min(2d_i, 2\bar d_i)$ per landing, no assumption) and `forest` (symmetric, A1):
  - `roles` (A1-NS): each plane flies an odd number $\ge 1$ of crossings and its other landings weigh at least $\min(2d, 2\bar d)$; all loads add up to the crossing weight of the landings, so the largest is at least that over $p$.
  - `lagrangian mu_1 ... mu_n` (A1-NS): with one signed integer multiplier per city, a drop-off in $i$ costs $c_i + \mu_i$ and a pick-up $c_i - \mu_i$; the balance of drop-offs and pick-ups city by city drops out and the planes decouple. Every $\mu$ gives a lower bound, so the checker only evaluates the bound at the listed $\mu$.
  - `balanced` (A1-NS): the checker reruns the exact program over balanced role configurations (a branch and bound against the cost $C_i$) and requires that it finishes.
  - `search` (A1-NS): the checker reruns the exhaustive search over role configurations of cost below $C_i$ with exact schedules (every order of drop-offs, matching and pick-up order) and requires that none finishes before $M_{i+1}$. By Corollary 6.10 (schedulable domination, Theorem 6.9) this rules out every feasible plan, also on instances with a city of $d = \bar d = 0$. Older certificates may list the assumption `EO` (event-ordered plans) for such instances. Both checkers still read it, but it is no longer needed. This is the only kind that closes gaps opened by harmful waiting (Proposition 6.5). It is also a valid `fastest` kind.

Obligations 1 and 4 are unchanged. The reference checker (`zeno check`) reads both versions. The Lean checker (`lean/`) verifies version 1. Of version 2 it verifies the `relaxed`, `roles`, `lagrangian`, `balanced` and `search` gaps, and `fastest closed`, `relaxed`, `roles`, `balanced` and `search`. Its soundness theorem `Cert2.check_sound` is about every feasible plan, with or without a city of $d = \bar d = 0$ (`schedulableDomination_all`, `lean/README.md`). When a certificate lists `EO`, the Lean checker also tests that every listed plan is event-ordered, and the points are then also the front of the event-ordered plans (`Cert2.check_sound_EO`).
