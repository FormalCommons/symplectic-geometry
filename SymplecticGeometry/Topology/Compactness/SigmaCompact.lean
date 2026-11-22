/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# σ-compact open neighbourhoods of compact sets

In a locally compact space, a compact set `K` contained in an open set `U` has an open
neighbourhood inside `U` that is σ-compact
(`IsCompact.exists_isOpen_isSigmaCompact_subset`). Applying Mathlib's `exists_compact_between`
repeatedly gives compact sets `K = L₀ ⊆ interior L₁ ⊆ L₁ ⊆ interior L₂ ⊆ ⋯` inside `U`, and their
union is open and σ-compact. No separation axiom is needed.

## Main results

* `IsCompact.exists_isOpen_isSigmaCompact_subset`: in a locally compact space, a compact set has
  σ-compact open neighbourhoods inside any open set that contains it.
-/

public section

open Set

variable {X : Type*} [TopologicalSpace X]

/-- In a locally compact space, a compact set `K` inside an open set `U` has an open
neighbourhood `V ⊆ U` that is σ-compact. -/
theorem IsCompact.exists_isOpen_isSigmaCompact_subset [LocallyCompactSpace X] {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ IsSigmaCompact V := by
  -- A compact `L ⊆ U` lies in the interior of a larger compact subset of `U`.
  have step (L : {L : Set X // IsCompact L ∧ L ⊆ U}) :
      ∃ L' : {L : Set X // IsCompact L ∧ L ⊆ U}, L.val ⊆ interior L'.val := by
    obtain ⟨L', hL', hLL', hL'U⟩ := exists_compact_between L.property.1 hU L.property.2
    exact ⟨⟨L', hL', hL'U⟩, hLL'⟩
  choose next hnext using step
  let L : ℕ → {L : Set X // IsCompact L ∧ L ⊆ U} := fun n ↦ next^[n] ⟨K, hK, hKU⟩
  have hL (n : ℕ) : (L n).val ⊆ interior (L (n + 1)).val := by
    simp only [L, Function.iterate_succ_apply']
    exact hnext _
  refine ⟨⋃ n, (L n).val, ?_, subset_iUnion (fun n ↦ (L n).val) 0,
    iUnion_subset fun n ↦ (L n).property.2,
    isSigmaCompact_iUnion_of_isCompact _ fun n ↦ (L n).property.1⟩
  refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
  obtain ⟨n, hn⟩ := mem_iUnion.1 hx
  exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.1 (hL n hn)) <|
    subset_iUnion (fun n ↦ (L n).val) (n + 1)
