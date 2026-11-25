/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Partitions of unity subordinate to balls

Let `ρ` be a partition of unity on a pseudometric space `X`, indexed by the points of `X`, with
`ρ x` supported in the ball `B(x, r x)`. Suppose that each ball `B(x, 2 * r x)` lies in a member
of a family of sets `S`. If finitely many functions `ρ i`, `i ∈ t`, are nonzero at a point `z`,
then choosing `j ∈ t` with the largest radius, the triangle inequality puts `z` and every `i ∈ t`
in `B(j, 2 * r j)`, so in one member of `S`.

## Main results

* `PartitionOfUnity.IsSubordinate.exists_mem_forall_mem_of_ne_zero`: under these hypotheses, `z`
  and the points of `t` lie in one member of `S`.
-/

public section

open Metric

namespace PartitionOfUnity.IsSubordinate

variable {X ι : Type*} [PseudoMetricSpace X] {s : Set X} {ρ : PartitionOfUnity X X s}
  {r : X → ℝ}

/-- Let `ρ`, indexed by the points of `X`, be subordinate to the balls `B(x, r x)`, and let each
ball `B(x, 2 * r x)` lie in some `S k`. If the functions `ρ i`, `i ∈ t`, for a nonempty finite set
`t`, are all nonzero at `z`, then `z` and every point of `t` lie in one set `S k`. -/
theorem exists_mem_forall_mem_of_ne_zero (hρ : ρ.IsSubordinate fun x => ball x (r x))
    {S : ι → Set X} (hS : ∀ x, ∃ k, ball x (2 * r x) ⊆ S k) {z : X} {t : Finset X}
    (ht : t.Nonempty) (hz : ∀ i ∈ t, ρ i z ≠ 0) : ∃ k, z ∈ S k ∧ ∀ i ∈ t, i ∈ S k := by
  have hd (i) (hi : i ∈ t) : dist z i < r i :=
    mem_ball.1 (hρ i (subset_tsupport _ (hz i hi)))
  obtain ⟨j, hj, hjmax⟩ := t.exists_max_image r ht
  obtain ⟨k, hk⟩ := hS j
  have hj0 : 0 ≤ r j := dist_nonneg.trans (hd j hj).le
  refine ⟨k, hk (mem_ball.2 (by linarith [hd j hj])), fun i hi => hk (mem_ball.2 ?_)⟩
  calc dist i j ≤ dist i z + dist z j := dist_triangle _ _ _
    _ < r i + r j := by rw [dist_comm i z]; linarith [hd j hj, hd i hi]
    _ ≤ 2 * r j := by linarith [hjmax i hi]

end PartitionOfUnity.IsSubordinate

end
