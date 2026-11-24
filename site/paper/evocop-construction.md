**From the original paper** (Quemy & Schoenauer, EvoCOP 2015, §2.3, HAL preprint hal-01109777v1, pp. 6–7).

> **Proposition**: It is always possible to construct a feasible plan with the makespan returned by the
> two-steps method described above.
>
> **Proof by construction**: Considering a P3 pattern performed by planes $p_1$ in $C_G$ and $p_2$ in
> $C_I$ through city $C_i$. […] Let $\blacklozenge$ denote the time $t_1$ when plane $p_1$ arrives in
> $C_i$ and $\lozenge$ the time $t_2$ when plane $p_2$ (with the person) arrives in $C_i$. If
> $t_2 > t_1$ then plane $p_1$ will have to wait $t_2 - t_1$ in $C_i$ before flying back to $C_G$ with
> the person. But the duration vector $(D^2_k)$ returned by the two steps algorithm is computed assuming
> no waiting point. Consequently, the proposition is equivalent to assert that we can always build a
> plan without any waiting point.
>
> In order to do so, for each P3, the idea is to perform the westward part as early as possible, and
> on the opposite, to perform the eastward part as late as possible, thus ensuring that there is no
> waiting time.
>
> In order to construct such an optimal plan, we will remember the cities of every plane and every
> pattern during both previous steps of the algorithm. From there on, let us consider now only planes
> that have to perform at least one P3 pattern.
>
> 1. For each plane, select the one with the maximum number of P3 patterns to be performed. In case of
>    tie, select the plane with longest P3 duration, or the plane with the largest current 'private'
>    makespan.
> 2. Construct a partial schedule with only P1 and P2 patterns (Step 1 above).
> 3. For every 'not already started' P3 pattern, add its eastward part at the end of the schedule by
>    descending order of durations.
> 4. For every 'already started' P3 pattern, add its westward part at the beginning of the schedule by
>    ascending order of durations. $\square$
