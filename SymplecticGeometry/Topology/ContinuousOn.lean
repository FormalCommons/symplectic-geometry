/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.ContinuousOn

/-!
# Gluing continuity on the traces of two closed sets

Mathlib's `ContinuousOn.union_of_isClosed` glues continuity on two closed sets. Here the two
pieces are the traces `s ∩ u` and `t ∩ u` of closed sets `s` and `t` on an arbitrary set `u`:
continuity on each gives continuity on `(s ∪ t) ∩ u`. The proof is that of
`ContinuousOn.union_of_isClosed`, using that the closure of `s ∩ u` lies in `s`.

## Main results

* `ContinuousOn.union_inter_of_isClosed`: the gluing on the traces of `s` and `t` on `u`.
* `ContinuousOn.union_prod_of_isClosed`: its form for products `s ×ˢ u` and `t ×ˢ u`, with `s`
  and `t` closed.
-/

public section

open Set Topology

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- If `s` and `t` are closed, a function continuous on `s ∩ u` and on `t ∩ u` is continuous on
`(s ∪ t) ∩ u`. -/
theorem ContinuousOn.union_inter_of_isClosed {f : α → β} {s t u : Set α}
    (hfs : ContinuousOn f (s ∩ u)) (hft : ContinuousOn f (t ∩ u)) (hs : IsClosed s)
    (ht : IsClosed t) : ContinuousOn f ((s ∪ t) ∩ u) := by
  classical
  intro x hx
  rw [union_inter_distrib_right]
  refine .union ?_ ?_
  · exact if h : x ∈ s then hfs x ⟨h, hx.2⟩ else continuousWithinAt_of_notMem_closure
      fun hc ↦ h (hs.closure_subset (closure_mono inter_subset_left hc))
  · exact if h : x ∈ t then hft x ⟨h, hx.2⟩ else continuousWithinAt_of_notMem_closure
      fun hc ↦ h (ht.closure_subset (closure_mono inter_subset_left hc))

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
