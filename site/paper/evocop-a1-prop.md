**From the original paper** (Quemy & Schoenauer, EvoCOP 2015, §2.2 *Pareto Optimal Plans*, HAL preprint hal-01109777v1, pp. 3–4).

> Let us make another simplifying assumption:\
> **Assumption A1**: $\forall (i, j) \in [1, n]^2, d_i + d_j < d_{ij}$. Then the following holds.
>
> **Proposition**: Pareto-optimal plans are plans where exactly $2t - p$ (possibly identical) central
> cities are used by a flight.
>
> **Proof**: Consider a plan where a person flies from $C_i$ to $C_j$. Using the same plane, the same
> person could fly instead from $C_i$ to $C_G$, and the plane would return empty to $C_j$. The plan
> could continue unchanged from thereon: because of the hypothesis on makespans, the needed resource
> would be in $C_j$ on time. Moreover, the total cost is unchanged, and the total makespan is lower or
> equal to the original one: the new plan thus Pareto-dominates the original one.
>
> Iterating the same reasoning for each person, and each empty plane, we conclude that there are no
> flights between central cities in Pareto-optimal plans. Thus bringing the $t$ persons from $C_I$ to
> $C_G$ will amount to carry each person through one central city: $t$ flights will be needed from
> $C_I$ to one $C_i$, then $t$ flights from $C_i$ to $C_G$. Finally, because planes do not need to come
> back from $C_G$ in the end, only $t - p$ flights back empty will be needed, possibly through some
> different central cities – hence the result. $\square$
>
> *Footnote 3 (on Assumption A1):* This might look unrealistic in real-world logistic domain. However,
> we hypothesize that the proposition still holds with the weaker condition that for any cities
> $C_i, C_j, C_k$ (if we state the cost of $C_I$ and $C_G$ are respectively $C_0$ and $C_{n+1}$),
> $d_{ik} \le d_{ij} + d_{jk}$ (triangle inequality).
