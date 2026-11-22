/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyFinite

/-!
# Disjoint open covers of compact spaces

A family of pairwise disjoint, nonempty open sets that covers a compact space has finite index
(`finite_of_compactSpace_of_pairwise_disjoint`): the family is locally finite, since each point
has a member of the family as a neighbourhood, which meets no other member, so Mathlib's
`LocallyFinite.finite_of_compact` applies.

## Main results

* `finite_of_compactSpace_of_pairwise_disjoint`: a disjoint open cover of a compact space by
  nonempty sets is finite.
-/

public section

open Set Function

variable {ι X : Type*} [TopologicalSpace X]

/-- A family of pairwise disjoint, nonempty open sets that covers a compact space is indexed by a
finite type. -/
theorem finite_of_compactSpace_of_pairwise_disjoint [CompactSpace X] {s : ι → Set X}
    (hs : ∀ i, IsOpen (s i)) (hne : ∀ i, (s i).Nonempty) (hd : Pairwise (Disjoint on s))
    (hU : ⋃ i, s i = univ) : Finite ι := by
  have hlf : LocallyFinite s := fun x ↦ by
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hU.symm ▸ mem_univ x)
    refine ⟨s j, (hs j).mem_nhds hj, (finite_singleton j).subset fun i hi ↦ ?_⟩
    exact not_not.1 fun hij ↦ not_disjoint_iff_nonempty_inter.2 hi (hd hij)
  exact finite_univ_iff.1 (hlf.finite_of_compact hne)

end
