/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Order.Compact

/-!
# Sublevel sets of proper maps bounded below

A proper map `f` into an order in which closed intervals are compact, such as `ℝ`, has compact
sublevel sets `f ⁻¹' Iic c` once its range is bounded below
(`IsProperMap.isCompact_preimage_Iic`): such a sublevel set is the preimage of a closed interval.
This is the step that makes a proper function bounded below an exhaustion function, as in Tau
Ceti's `TauCeti.IsMorse.finite_criticalPoints_inter_preimage_Iic`, from whose proof it is taken.
-/

public section

open Set

variable {X α : Type*} [TopologicalSpace X] [TopologicalSpace α] [Preorder α] [CompactIccSpace α]
  {f : X → α}

/-- A proper map whose range is bounded below has compact sublevel sets. -/
theorem IsProperMap.isCompact_preimage_Iic (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (c : α) : IsCompact (f ⁻¹' Iic c) := by
  obtain ⟨a, ha⟩ := hbdd
  have hsub : f ⁻¹' Iic c = f ⁻¹' Icc a c := by
    ext y
    simp [ha (mem_range_self y)]
  rw [hsub]
  exact hp.isCompact_preimage isCompact_Icc

end
