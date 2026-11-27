/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Compactness.CompactlyCoherentSpace
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import TauCeti.Topology.Maps.Proper.CompactlyGenerated

/-!
# Proper maps into orders, and closed images of half-lines

This file collects two facts about proper maps and maps tending to infinity.

## Sublevel sets of proper maps bounded below

A proper map `f` into an order in which closed intervals are compact, such as `ℝ`, has compact
sublevel sets `f ⁻¹' Iic c` once its range is bounded below
(`IsProperMap.isCompact_preimage_Iic`): such a sublevel set is the preimage of a closed interval.
This is the step that makes a proper function bounded below an exhaustion function, as in Tau
Ceti's `TauCeti.IsMorse.finite_criticalPoints_inter_preimage_Iic`, from whose proof it is taken.
It follows that a continuous function into a linear order that lies above a proper function
bounded below is proper (`IsProperMap.of_le`).

## Closed images of half-lines

A map `f` from a linear order with compact closed intervals into a Hausdorff compactly coherent
space, continuous on `[a, ∞)` and tending to the cocompact filter at `+∞`, maps `[a, ∞)` onto a
closed set (`Filter.Tendsto.isClosed_image_Ici`). The proof uses Tau Ceti's
`IsClosed.image_of_isCompact_inter_preimage`.
-/

public section

open Set

variable {X α : Type*} [TopologicalSpace X] [TopologicalSpace α]

section Preorder

variable [Preorder α] [CompactIccSpace α] {f : X → α}

/-- A proper map whose range is bounded below has compact sublevel sets. -/
theorem IsProperMap.isCompact_preimage_Iic (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (c : α) : IsCompact (f ⁻¹' Iic c) := by
  obtain ⟨a, ha⟩ := hbdd
  have hsub : f ⁻¹' Iic c = f ⁻¹' Icc a c := by
    ext y
    simp [ha (mem_range_self y)]
  rw [hsub]
  exact hp.isCompact_preimage isCompact_Icc

end Preorder

variable [LinearOrder α] [OrderTopology α] [CompactIccSpace α]

/-- A continuous function into a linear order with compact closed intervals that lies above a
proper function bounded below is proper. -/
theorem IsProperMap.of_le [CompactlyCoherentSpace α] {f g : X → α} (hf : IsProperMap f)
    (hbdd : BddBelow (range f)) (hg : Continuous g) (hfg : ∀ x, f x ≤ g x) : IsProperMap g := by
  refine isProperMap_iff_isCompact_preimage.2 ⟨hg, fun K hK ↦ ?_⟩
  rcases K.eq_empty_or_nonempty with rfl | ⟨k, -⟩
  · simp
  have : Nonempty α := ⟨k⟩
  obtain ⟨b, hb⟩ := hK.bddAbove
  exact (hf.isCompact_preimage_Iic hbdd b).of_isClosed_subset (hK.isClosed.preimage hg)
    fun x hx ↦ (hfg x).trans (hb hx)

/-- A map `f` from a linear order with compact closed intervals into a Hausdorff compactly
coherent space, continuous on the half-line `[a, ∞)` and tending to the cocompact filter at `+∞`,
maps `[a, ∞)` onto a closed set. -/
theorem Filter.Tendsto.isClosed_image_Ici [T2Space X] [CompactlyCoherentSpace X] {f : α → X}
    (h : Filter.Tendsto f Filter.atTop (Filter.cocompact X)) (a : α)
    (hf : ContinuousOn f (Ici a)) : IsClosed (f '' Ici a) := by
  have : Nonempty α := ⟨a⟩
  refine isClosed_Ici.image_of_isCompact_inter_preimage hf subset_rfl fun K hK ↦ ?_
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (h hK.compl_mem_cocompact)
  exact isCompact_Icc.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_Ici hK.isClosed)
    fun t ht ↦ ⟨ht.1, le_of_not_gt fun hTt ↦ hT t hTt.le ht.2⟩

end
