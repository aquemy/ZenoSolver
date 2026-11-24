**From the original paper** (Quemy & Schoenauer, EvoCOP 2015, §2.2–2.3, HAL preprint hal-01109777v1, pp. 4–5).

> **PPPs and Admissible PPPs**: According to the above proposition, a Possibly Pareto-optimal Plan
> (PPP) is defined by 2 tuples, namely $e \in [0, n]^t$ for cities involved in eastbound flights, and
> $w \in [0, n]^{t-p}$ for westbound flights. Nevertheless, $e$ and $w$ do not hold any information
> about which plane will land in a particular city. This is the reason why there exists many feasible
> schedules, i.e., schedules that actually are feasible plans for $p$ planes using the corresponding
> $4t-2p$ edges. […]
>
> **Makespan of a PPP**: The makespan of a PPP is thus that of the shortest schedule that uses its
> $4t - 2p$ edges in a feasible way. […]
>
> **Flight patterns** Clearly, within a PPP, all possible plane moves can be categorized into only 3
> patterns:\
> **P1**: plane leaves $C_I$ (non empty), flies eastward to city $C_i$, and goes on to $C_G$.\
> **P2**: plane leaves $C_G$ (empty), flies westward to city $C_i$, and goes on to $C_G$.\
> **P3**: two planes are involved here; first plane leaves $C_I$ (with a passenger), flies to city
> $C_i$, and goes back empty to $C_I$; second plane leaves $C_G$ empty, flies to $C_i$, and flies back
> with the passenger to $C_G$. Note that there can be some delay between the drop-off of the person at
> the central city, and the arrival of the second plane.
