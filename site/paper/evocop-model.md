**From the original paper** (Quemy & Schoenauer, EvoCOP 2015, §2.1 *Instances*, HAL preprint hal-01109777v1, pp. 2–3).

> Let us introduce some notations related to the planning problem briefly presented in the
> introduction: a MultiZenoTravel instance (Figure 1) is defined by the following elements:
>
> – $n$ central cities, organized as a clique in which every node is connected to $C_I$ and $C_G$, respectively the initial city and the goal city.\
> – $c \in (\mathbb R^+)^n$, where $c_i$ is the cost for landing in $C_i$.\
> – $D \in (\mathbb R^+)^{n\times n}$, where $D_{ij}$ is the flying time between $C_i$ and $C_j$.\
> – $d^I \in (\mathbb R^+)^n$, where $d^I_i$ is the flying time between $C_I$ and $C_i$.\
> – $d^G \in (\mathbb R^+)^n$, where $d^G_i$ is the flying time between $C_i$ and $C_G$.\
> – $p$ planes, initially in $C_I$, that have a capacity of an unique person.\
> – $t$ persons, initially in $C_I$.
>
> As said, the goal is to carry all $t$ persons, initially in $c_I$, to $c_G$ using $p$ planes,
> minimizing both the makespan and the cost of the plan. In order to ease the identification of the
> true Pareto Front, a symmetry constraint is added: $\forall i \in [1, n], d^I_i = d^G_i$ and from
> thereon we will refer to a unique vector $d$.
