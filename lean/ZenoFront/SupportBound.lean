/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Admissible

/-!
# Support bound for parity witnesses (Claim B′, `t − p` part)

The cities *touched* by a parity witness `h` are the cities of the `T`-join, `⋃_k h k`. They are
the only cities whose parity must be tracked by the σ-DP of the exact algorithm (Claim C), so a
bound on their number bounds the DP state.

**Claim B′, `t − p` part.** If `h` is any parity witness of a grouping with `Σ_k |X_k| = s`, then
`h` touches at most `t − p` cities. Proof: by Lemma 2.3 the number of edges is
`Σ_k |h k| ≤ Σ_k (|X_k| − 1) = s − p = 2(t − p)`; every touched city has even, hence at least
`2`, incident edges; so `2 · #touched ≤ 2(t − p)`.

## Main definitions

* `ZenoFront.touched h`: the cities lying in some `h k`.
* `ZenoFront.edgeCount h`: the number of edges `Σ_k |h k|` of the `T`-join.

## Main results

* `ZenoFront.edgeCount_eq_sum_degree`: double counting, `Σ_k |h k| = Σ_i #{k | i ∈ h k}`.
* `ZenoFront.IsParityWitness.two_mul_card_touched_le_edgeCount`: `2 · #touched ≤ Σ_k |h k|`.
* `ZenoFront.IsParityWitness.edgeCount_add_le_size`: `Σ_k |h k| + p ≤ Σ_k |X_k|`.
* `ZenoFront.IsParityWitness.edgeCount_le`: with `Σ_k |X_k| = s`, `Σ_k |h k| ≤ 2(t − p)`.
* `ZenoFront.IsParityWitness.card_touched_le`: with `Σ_k |X_k| = s`, `#touched ≤ t − p`.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n p : ℕ}

/-- The cities touched by a parity witness: those lying in some `h k`. -/
def touched (h : Fin p → Finset (Fin n)) : Finset (Fin n) := univ.biUnion h

theorem mem_touched {h : Fin p → Finset (Fin n)} {i : Fin n} :
    i ∈ touched h ↔ ∃ k, i ∈ h k := by
  simp [touched]

theorem mem_touched_of_mem {h : Fin p → Finset (Fin n)} {k : Fin p} {i : Fin n} (hi : i ∈ h k) :
    i ∈ touched h :=
  mem_touched.mpr ⟨k, hi⟩

/-- The number of edges of the `T`-join described by `h`, `Σ_k |h k|`. -/
def edgeCount (h : Fin p → Finset (Fin n)) : ℕ := ∑ k, (h k).card

/-- Double counting the edges of the `T`-join: by planes and by cities. -/
theorem edgeCount_eq_sum_degree (h : Fin p → Finset (Fin n)) :
    edgeCount h = ∑ i, #{k | i ∈ h k} := by
  have hk : ∀ k, (h k).card = ∑ i, if i ∈ h k then 1 else 0 := fun k => by
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  simp only [edgeCount, hk, Finset.card_filter]
  exact Finset.sum_comm

namespace IsParityWitness

variable {X : Groups n p} {h : Fin p → Finset (Fin n)}

/-- Every touched city has even degree, hence degree at least `2`; so a parity witness has at
least twice as many edges as touched cities. -/
theorem two_mul_card_touched_le_edgeCount (hw : IsParityWitness X h) :
    2 * (touched h).card ≤ edgeCount h := by
  rw [edgeCount_eq_sum_degree, mul_comm, ← Finset.sum_const_nat fun _ _ => rfl]
  calc ∑ _i ∈ touched h, 2
      ≤ ∑ i ∈ touched h, #{k | i ∈ h k} := by
        refine Finset.sum_le_sum fun i hi => ?_
        obtain ⟨k, hk⟩ := mem_touched.mp hi
        have hpos : 0 < #{k | i ∈ h k} := Finset.card_pos.mpr ⟨k, by simpa using hk⟩
        obtain ⟨r, hr⟩ := hw.col i
        omega
    _ ≤ ∑ i, #{k | i ∈ h k} := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- Summing Lemma 2.3 over the planes: `Σ_k |h k| + p ≤ Σ_k |X_k|`. -/
theorem edgeCount_add_le_size (hw : IsParityWitness X h) : edgeCount h + p ≤ size X :=
  hw.sum_card_add_le

/-- `2 · #touched + p ≤ Σ_k |X_k|`. -/
theorem two_mul_card_touched_add_le_size (hw : IsParityWitness X h) :
    2 * (touched h).card + p ≤ size X :=
  (Nat.add_le_add_right hw.two_mul_card_touched_le_edgeCount p).trans hw.edgeCount_add_le_size

/-- With `Σ_k |X_k| = s = 2t − p`, a parity witness has at most `2(t − p)` edges. -/
theorem edgeCount_le (I : Instance) {X : Groups I.n I.p} {h : Fin I.p → Finset (Fin I.n)}
    (hw : IsParityWitness X h) (hs : size X = I.s) : edgeCount h ≤ 2 * (I.t - I.p) := by
  have := hw.edgeCount_add_le_size
  have := I.s_add_p
  have := I.p_le_t
  omega

/-- **Claim B′, `t − p` part.** With `Σ_k |X_k| = s = 2t − p`, every parity witness touches at
most `t − p` cities. -/
theorem card_touched_le (I : Instance) {X : Groups I.n I.p} {h : Fin I.p → Finset (Fin I.n)}
    (hw : IsParityWitness X h) (hs : size X = I.s) : (touched h).card ≤ I.t - I.p := by
  have := hw.two_mul_card_touched_le_edgeCount
  have := hw.edgeCount_le I hs
  omega

/-- A plane of a parity witness touches at most `min(|X_k| − 1, 2(t − p))` cities; together with
`card_touched_le` this bounds the sets `H` the σ-DP has to enumerate per plane. -/
theorem card_le_min (I : Instance) {X : Groups I.n I.p} {h : Fin I.p → Finset (Fin I.n)}
    (hw : IsParityWitness X h) (hs : size X = I.s) (k : Fin I.p) :
    (h k).card ≤ min ((X k).card - 1) (I.t - I.p) := by
  refine le_min ?_ ?_
  · have := hw.card_add_one_le k
    omega
  · exact (Finset.card_le_card fun i hi => mem_touched_of_mem hi).trans (hw.card_touched_le I hs)

end IsParityWitness

end ZenoFront
