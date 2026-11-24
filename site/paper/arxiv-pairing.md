**From the original paper** (Quemy, Schoenauer & Dreo, arXiv:2304.14659v1, §2.2).

> **Definition:** (($B\bar{B}$)-pairing) Consider a pattern $B$ and $\bar{B}$ in a list of patterns,
> both of multiplicity $0$ and using respectively the central city $C_{i}$ and $C_{j}$. Pairing them
> consists in using the central city $C^{*}=\text{argmin}~(d_{i}+\bar{d}_{i},d_{j}+\bar{d}_{j})$.
>
> In the symmetric case, the condition becomes $C^{*}=\text{argmin}~(d_{i},d_{j})$. Under
> Assumption $(S)$, the duration of both patterns involved in the pairing is lower or equal to its
> duration before the pairing.
>
> […] Those steps transform any $(k,\phi)$ into a $(k,\phi_{0})$. Indeed, the cardinality of each type
> of patterns defined by $k$ is conserved but for each single pattern, its multiplicity is now zero. On
> top of that, each city that appeared in $\phi_{0}$ also appears in $\phi$ which implies a lower cost
> of all feasible plans on $(k,\phi_{0})$. The set $\mathcal{P}(k,\phi_{0})$ is not empty since we
> constructed a valid plan. The duration of each pattern remains the same or is lower than in the
> original plan due to the reduction. The ($B\bar{B}$)-pairing also let unchanged the duration for one
> of the pattern and lower it for the second one involved in the couple due to the symmetric
> assumption (S). As a result, the transformed plan dominates the original one while using only $2t-p$
> cities, thus proving Proposition I under Assumption (A$\Delta$) and Assumption (S). $\square$
