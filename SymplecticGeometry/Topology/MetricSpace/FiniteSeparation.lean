/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.MetricSpace.Defs
import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# Finite families of distinct points are uniformly separated

In a metric space, the values of an injective map on a finite type are uniformly separated:
some `δ > 0` is at most the distance between the values at any two distinct indices.

## Main results

* `Function.Injective.exists_pos_pairwise_le_dist`: such a `δ` exists.

## Implementation notes

The proof is the separation step of Tau Ceti's
`TauCeti.nonempty_fundamentalGroup_compl_mulEquiv_freeGroup`
(`TauCeti/AlgebraicTopology/FundamentalGroup/PlaneMinusPoints.lean`, at Tau Ceti's commit
`994bb2246b869d826bb90a6298bd0f9423b83104`), stated here for any metric space: it takes the
radius given by `TauCeti.exists_pos_closedBall_subset_and_lt_dist` and doubles it.
-/

public section

namespace Function.Injective

variable {ι X : Type*} [MetricSpace X]

/-- The values of an injective map from a finite type to a metric space are uniformly separated:
some `δ > 0` is at most the distance between the values at any two distinct indices. -/
theorem exists_pos_pairwise_le_dist [Finite ι] {f : ι → X} (hf : Function.Injective f) :
    ∃ δ, 0 < δ ∧ Pairwise fun i j ↦ δ ≤ dist (f i) (f j) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨r, hr, -, hrf⟩ := TauCeti.exists_pos_closedBall_subset_and_lt_dist
    (T := Finset.univ.image f) (U := fun _ ↦ Set.univ) fun _ _ ↦ Filter.univ_mem
  exact ⟨2 * r, by positivity, fun i j hij ↦ (hrf _ (Finset.mem_image_of_mem f
    (Finset.mem_univ i)) _ (Finset.mem_image_of_mem f (Finset.mem_univ j)) (hf.ne hij)).le⟩

end Function.Injective

end
