/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.ContinuousOn

/-!
# Gluing continuity on two relatively closed sets

Mathlib's `ContinuousOn.union_of_isClosed` glues continuity on two closed sets. Here the two
sets `s` and `t` need only be closed relative to `s ∪ t`: continuity on each gives continuity on
`s ∪ t`. The proof is that of `ContinuousOn.union_of_isClosed`, splitting at each point of the
union according to whether it lies in the closure of each set. A special case is that of the
traces `s ∩ u` and `t ∩ u` of closed sets `s` and `t` on an arbitrary set `u`.

## Main results

* `ContinuousOn.union_of_closure_inter_subset`: the gluing on two sets, each closed relative to
  their union.
* `ContinuousOn.union_inter_of_isClosed`: the gluing on the traces of `s` and `t` on `u`.
* `ContinuousOn.union_prod_of_isClosed`: its form for products `s ×ˢ u` and `t ×ˢ u`, with `s`
  and `t` closed.
-/

public section

open Set Topology

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- A function continuous on `s` and on `t` is continuous on `s ∪ t` when each of `s` and `t` is
closed relative to `s ∪ t`, that is, when `closure s ∩ t ⊆ s` and `closure t ∩ s ⊆ t`. -/
theorem ContinuousOn.union_of_closure_inter_subset {f : α → β} {s t : Set α}
    (hfs : ContinuousOn f s) (hft : ContinuousOn f t) (hst : closure s ∩ t ⊆ s)
    (hts : closure t ∩ s ⊆ t) : ContinuousOn f (s ∪ t) := by
  classical
  intro x hx
  refine .union ?_ ?_
  · exact if h : x ∈ s then hfs x h else continuousWithinAt_of_notMem_closure
      fun hc ↦ h (hst ⟨hc, hx.resolve_left h⟩)
  · exact if h : x ∈ t then hft x h else continuousWithinAt_of_notMem_closure
      fun hc ↦ h (hts ⟨hc, hx.resolve_right h⟩)

/-- If `s` and `t` are closed, a function continuous on `s ∩ u` and on `t ∩ u` is continuous on
`(s ∪ t) ∩ u`. -/
theorem ContinuousOn.union_inter_of_isClosed {f : α → β} {s t u : Set α}
    (hfs : ContinuousOn f (s ∩ u)) (hft : ContinuousOn f (t ∩ u)) (hs : IsClosed s)
    (ht : IsClosed t) : ContinuousOn f ((s ∪ t) ∩ u) := by
  rw [union_inter_distrib_right]
  refine hfs.union_of_closure_inter_subset hft ?_ ?_ <;> rintro x ⟨hc, -, hu⟩
  · exact ⟨hs.closure_subset (closure_mono inter_subset_left hc), hu⟩
  · exact ⟨ht.closure_subset (closure_mono inter_subset_left hc), hu⟩

/-- If `s` and `t` are closed, a function continuous on `s ×ˢ u` and on `t ×ˢ u` is continuous
on `(s ∪ t) ×ˢ u`. -/
theorem ContinuousOn.union_prod_of_isClosed {f : α × β → γ} {s t : Set α} {u : Set β}
    (hfs : ContinuousOn f (s ×ˢ u)) (hft : ContinuousOn f (t ×ˢ u)) (hs : IsClosed s)
    (ht : IsClosed t) : ContinuousOn f ((s ∪ t) ×ˢ u) := by
  rw [prod_eq] at hfs hft ⊢
  rw [preimage_union]
  exact hfs.union_inter_of_isClosed hft (hs.preimage continuous_fst)
    (ht.preimage continuous_fst)

end
