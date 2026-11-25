/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Connected.Clopen

/-!
# Preconnected sets and clopen sets

A dense subset `s` of a preconnected space is preconnected as soon as every point of the space
has a neighbourhood `t` such that `t ∩ s` is preconnected. Applied to the interior of a manifold
with boundary, this shows that the interior of a connected manifold is connected.

## Main results

* `Dense.isPreconnected_of_forall_exists_mem_nhds`: the criterion above.
* `IsPreconnected.inter_of_isClopen_preimage_val`: cutting a preconnected set `s` by a set whose
  trace on some `u ⊇ s` is open and closed in `u` leaves a preconnected set.
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

/-- If `s ⊆ u` is preconnected and the trace of `t` on `u` is open and closed in `u`, then
`s ∩ t` is preconnected: it is either empty or all of `s`. -/
theorem IsPreconnected.inter_of_isClopen_preimage_val {s t u : Set X} (hs : IsPreconnected s)
    (hsu : s ⊆ u) (ht : IsClopen ((↑) ⁻¹' t : Set u)) : IsPreconnected (s ∩ t) := by
  rcases (s ∩ t).eq_empty_or_nonempty with h | ⟨x, hxs, hxt⟩
  · rw [h]
    exact isPreconnected_empty
  have hs' : IsPreconnected ((↑) ⁻¹' s : Set u) := by
    rwa [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      inter_eq_right.2 hsu]
  have hst := hs'.subset_isClopen ht ⟨⟨x, hsu hxs⟩, hxs, hxt⟩
  have hst' : s ⊆ t := fun y hy ↦ hst (show (⟨y, hsu hy⟩ : u) ∈ (↑) ⁻¹' s from hy)
  rwa [inter_eq_left.2 hst']

end
