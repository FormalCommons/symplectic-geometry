/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Closure

/-!
# Closures and relatively closed sets

A set `A` is closed in a set `V` when `closure A ∩ V ⊆ A`. This file shows that removing finitely
many such sets from an open set `V` leaves an open set.

## Main results

* `IsOpen.sdiff_iUnion_of_closure_inter_subset`: removing from an open set `V` finitely many sets,
  each closed in `V`, leaves an open set.
-/

public section

open Set

/-- Removing from an open set `V` finitely many sets `A i`, each closed in `V` in the sense that
`closure (A i) ∩ V ⊆ A i`, leaves an open set. -/
theorem IsOpen.sdiff_iUnion_of_closure_inter_subset {X ι : Type*} [TopologicalSpace X]
    [Finite ι] {V : Set X} (hV : IsOpen V) {A : ι → Set X}
    (hA : ∀ i, closure (A i) ∩ V ⊆ A i) : IsOpen (V \ ⋃ i, A i) := by
  have heq : V \ ⋃ i, A i = V \ ⋃ i, closure (A i) := by
    refine Subset.antisymm (fun x hx ↦ ⟨hx.1, fun h ↦ ?_⟩)
      (sdiff_subset_sdiff_right (iUnion_mono fun _ ↦ subset_closure))
    obtain ⟨i, hi⟩ := mem_iUnion.1 h
    exact hx.2 (mem_iUnion.2 ⟨i, hA i ⟨hi, hx.1⟩⟩)
  rw [heq]
  exact hV.sdiff (isClosed_iUnion_of_finite fun _ ↦ isClosed_closure)

end
