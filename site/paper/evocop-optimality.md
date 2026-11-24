**From the original paper** (Quemy & Schoenauer, EvoCOP 2015, §2.3, HAL preprint hal-01109777v1, p. 7).

> **Proposition**: For a given PPP $C$ and $\beta_{\rm set}$, the algorithm returns the optimal
> makespan.
>
> **Proof**: The incompressible time to transport all passengers, according to a given
> $\beta_{\rm set}$ is $T = 4\sum_{i\in\beta_{\rm set}} d_i + 2\sum_{i\in\{e',w'\}} d_i$. A theoretical
> optimal plan with this pattern repartition is a plan without any waiting point for any plane. The
> above algorithm gives the optimal distribution of the set of times into $p$. Then, if a plan can be
> constructed with such a makespan, it is optimal for the PPP and the repartition of patterns. As it
> exists a method to construct such a plan, we can conclude that the algorithm is optimal for the PPP
> $C$ and $\beta_{\rm set}$. $\square$
