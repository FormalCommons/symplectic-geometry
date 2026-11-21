/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Connected.Clopen

/-!
# Preconnectedness of dense subsets

A dense subset `s` of a preconnected space is preconnected as soon as every point of the space
has a neighbourhood `t` such that `t ∩ s` is preconnected. Applied to the interior of a manifold
with boundary, this shows that the interior of a connected manifold is connected.

## Main results

* `Dense.isPreconnected_of_forall_exists_mem_nhds`: the criterion above.
-/

public section

open Set Topology Relation

variable {X : Type*} [TopologicalSpace X]

/-- A dense subset `s` of a preconnected space is preconnected if every point `x` has a
neighbourhood `t` with `t ∩ s` preconnected. The point `x` need not lie in `s`. -/
theorem Dense.isPreconnected_of_forall_exists_mem_nhds [PreconnectedSpace X] {s : Set X}
    (hs : Dense s) (h : ∀ x, ∃ t ∈ 𝓝 x, IsPreconnected (t ∩ s)) : IsPreconnected s := by
  choose t ht hpre using h
  have hU : (⋃ x, t x ∩ s) = s :=
    Subset.antisymm (iUnion_subset fun _ ↦ inter_subset_right)
      fun a ha ↦ mem_iUnion.2 ⟨a, mem_of_mem_nhds (ht a), ha⟩
  -- Two points whose neighbourhoods `t` meet near each other give sets that meet in `s`.
  have hmeet : ∀ x, ∀ᶠ y in 𝓝 x, (t x ∩ s ∩ (t y ∩ s)).Nonempty := fun x ↦ by
    filter_upwards [interior_mem_nhds.2 (ht x)] with y hy
    obtain ⟨z, ⟨hzx, hzy⟩, hz⟩ := hs.inter_open_nonempty (interior (t x) ∩ interior (t y))
      (isOpen_interior.inter isOpen_interior) ⟨y, hy, mem_interior_iff_mem_nhds.2 (ht y)⟩
    exact ⟨z, ⟨interior_subset hzx, hz⟩, interior_subset hzy, hz⟩
  rw [← hU]
  refine IsPreconnected.iUnion_of_reflTransGen hpre fun x y ↦ ?_
  refine PreconnectedSpace.induction₂' _ (fun x ↦ ?_) ⟨fun _ _ _ ↦ ReflTransGen.trans⟩ x y
  filter_upwards [hmeet x] with y hy
  exact ⟨ReflTransGen.single hy, ReflTransGen.single (by rwa [inter_comm])⟩

end
