**From the original paper** (Quemy & Schoenauer, EvoCOP 2015, §2.3 *Computing the Shortest Makespan*, HAL preprint hal-01109777v1, pp. 5–6).

> **Step 1: Handling P3-free PPPs** […] For a PPP with $\beta = 0$, greedy Algorithm 1 dispatches the
> longest flight durations first, assigning them to the available planes with shortest 'private'
> makespan (who have yet flown the less), ending with the one-way last flights from $C_I$ to $C_G$
> (planes end in $C_G$). The algorithm returns the flight durations $(D^1_k)$ for all planes $k$ (to be
> used in the second step), and the optimal makespan for the subproblem is obviously
> $\max_k(D^1_k)$.
>
> **Step 2: Tackling Patterns P3** The second step consists in dispatching the durations of P3
> patterns among the planes according to their previous flight durations $(D^1_k)_{k=1,\dots,p}$, by
> sequentially assigning the longest P3 flight to the two planes with the smallest current flight
> durations. This can be performed greedily again, with a slightly modified version of the
> Algorithm 1, if we only consider the flight durations.

```
Algorithm 1  Computing the optimal makespan of PPP (e, w) when β = 0
i ← 1 ; j ← 1               {Indices of cities in e and w resp., longest durations first}
D_k ← 0, k = 1, ..., p                             {'Private' makespan for plane k}
S_k ← EAST, k = 1, ..., p                     {All planes are in C_I, going eastward}
while j ≤ t − p do
  k ← ArgMin_i(D_i)                 {Plane with shortest private makespan, in C_I or C_G}
  if S_k = EAST then
    D_k ← D_k + 2d_{e_i}                          {From C_I to C_G through city C_{e_i}}
    S_k ← WEST ; i ← i + 1
  else
    D_k ← D_k + 2d_{w_j}                          {From C_G to C_I through city C_{w_j}}
    S_k ← EAST ; j ← j + 1
  end if
end while                                     {Are there persons and planes left in C_I?}
while i ≤ t do
  k ← ArgMin_{i; S_i=EAST} (D_i)              {Plane in C_I with shortest private makespan}
  D_k ← D_k + 2d_{e_i}                            {From C_I to C_G through city C_{e_i}}
  S_k ← WEST ; i ← i + 1
end while
return (D_k)_{k=1,...,p}          {All private makespans are needed for the second step}
Makespan (e, w) = max_{k=1,...,p} {D_k}
```
