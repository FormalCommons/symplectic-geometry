/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Connected.Basic

/-!
# Connected components in a product

The connected component of a point `(x, y)` in a product set `s ×ˢ t` is the product of the
connected components of `x` in `s` and of `y` in `t`. This is the relative version of Mathlib's
`connectedComponent_prod`, whose proof it follows.

## Main results

* `connectedComponentIn_prod`: `connectedComponentIn (s ×ˢ t) (x, y)` is
  `connectedComponentIn s x ×ˢ connectedComponentIn t y`.
-/

public section

open Set

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- The connected component of `(x, y)` in `s ×ˢ t` is the product of the connected components of
`x` in `s` and of `y` in `t`. -/
theorem connectedComponentIn_prod (s : Set α) (t : Set β) (x : α) (y : β) :
    connectedComponentIn (s ×ˢ t) (x, y) =
      connectedComponentIn s x ×ˢ connectedComponentIn t y := by
  by_cases hxy : x ∈ s ∧ y ∈ t
  · obtain ⟨hx, hy⟩ := hxy
    have hmem : (x, y) ∈ s ×ˢ t := ⟨hx, hy⟩
    have hC := isPreconnected_connectedComponentIn (F := s ×ˢ t) (x := (x, y))
    have hCs := connectedComponentIn_subset (s ×ˢ t) (x, y)
    refine subset_antisymm ?_ ?_
    · intro p hp
      exact ⟨(hC.image _ continuous_fst.continuousOn).subset_connectedComponentIn
          ⟨_, mem_connectedComponentIn hmem, rfl⟩ (image_subset_iff.2 fun q hq ↦ (hCs hq).1)
          (mem_image_of_mem Prod.fst hp),
        (hC.image _ continuous_snd.continuousOn).subset_connectedComponentIn
          ⟨_, mem_connectedComponentIn hmem, rfl⟩ (image_subset_iff.2 fun q hq ↦ (hCs hq).2)
          (mem_image_of_mem Prod.snd hp)⟩
    · exact (isPreconnected_connectedComponentIn.prod isPreconnected_connectedComponentIn)
        |>.subset_connectedComponentIn
          (show (x, y) ∈ connectedComponentIn s x ×ˢ connectedComponentIn t y from
            ⟨mem_connectedComponentIn hx, mem_connectedComponentIn hy⟩)
          (prod_mono (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _))
  · rw [connectedComponentIn_eq_empty fun h ↦ hxy h]
    rcases not_and_or.1 hxy with h | h
    · rw [connectedComponentIn_eq_empty h, empty_prod]
    · rw [connectedComponentIn_eq_empty h, prod_empty]

end
