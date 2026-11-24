**From the original paper** (Quemy, Schoenauer & Dreo, arXiv:2304.14659v1, §3.2 *Computing the Shortest Makespan and Constructing the Plan*).

> If a non-symmetric instance is highly imbalanced in durations, while performing a $B\bar{B}$, there
> is a chance that the plane performing $\bar{B}$ will have to wait. It implies that its makespan is not
> the sum of the durations of its patterns but the moment the passenger arrives in the central city,
> plus the remaining duration of its track. For this reason, we denote by $T_{i}$ the moment passenger
> $i$ arrives in the central city she goes through.
>
> […]
>
> 4. For each city $i$ in $b$, greedily distribute by descending order of ${d}_{i}+{\bar{d}}_{i}$ the
>    duration $2\min~({d}_{i},{\bar{d}}_{i})$ among the planes. The rules to add the sub-sequences are
>    the same as in the first step. If ${d}_{i}<{\bar{d}}_{i}$, assign to the plane the makespace
>    $max(D(p)+\bar{d}_{i}),T_{i})+\bar{d}_{i}$ where $D(p)$ is the duration of the partial track up to
>    the moment the plane arrives in $C_{i}$.
>
> The optimal makespan for the given PPP is the longest duration among the $p$ planes.
>
> **Proposition:** For a given PPP $\psi_{0}$ and $\beta_{\text{set}}$, the algorithm returns the
> optimal makespan.
>
> **Proof for the symmetric case:** The incompressible time to transport all passengers, according to
> a given PPP is
> $T(\psi_{0})=2\sum_{i\in b}(d_{i}+\bar{d}_{i})+\sum_{i\in\{a,\bar{a}\}}(d_{i}+\bar{d}_{i})$. A
> theoretical optimal plan with this pattern repartition is a plan without any waiting point for any
> plane. The above algorithm gives the optimal distribution of the set of times into $p$. Then, if a
> plan can be constructed with such a makespan, it is optimal for the PPP. As it constructs such plan,
> we can conclude that the algorithm is optimal for the PPP, thus proving Proposition I. $\square$
>
> **Proof for the non-symmetric case:** The above algorithm gives the optimal distribution of the set of
> times into $p$ and provides a plan that minimizes the waiting time by starting the plan by the
> patterns that could lead to a waiting time. $\square$
