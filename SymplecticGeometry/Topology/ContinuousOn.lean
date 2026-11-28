/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.ContinuousOn

/-!
# Gluing continuity on pieces that are closed inside an open set

Mathlib's `ContinuousOn.union_of_isClosed` glues continuity on two closed sets. Here the two
pieces `s ∩ u` and `t ∩ u` need only be closed relative to an open set `u`, as `s` and `t` are
closed: continuity on each gives continuity on `(s ∪ t) ∩ u`. The proof is that of
`ContinuousOn.union_of_isClosed`, after `continuousWithinAt_inter` removes `u` near each point.

## Main results

* `ContinuousOn.union_inter_of_isClosed`: the gluing within an open set `u`.
* `ContinuousOn.union_prod_of_isClosed`: its form for products `s ×ˢ u` and `t ×ˢ u`, with `s`
  and `t` closed and `u` open.
-/

public section

open Set Topology

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- If `s` and `t` are closed and `u` is open, a function continuous on `s ∩ u` and on `t ∩ u`
is continuous on `(s ∪ t) ∩ u`. -/
theorem ContinuousOn.union_inter_of_isClosed {f : α → β} {s t u : Set α}
    (hfs : ContinuousOn f (s ∩ u)) (hft : ContinuousOn f (t ∩ u)) (hs : IsClosed s)
    (ht : IsClosed t) (hu : IsOpen u) : ContinuousOn f ((s ∪ t) ∩ u) := by
  classical
  intro x hx
  have hux : u ∈ 𝓝 x := hu.mem_nhds hx.2
  rw [continuousWithinAt_inter hux]
  refine .union ?_ ?_
  · refine if h : x ∈ s then (continuousWithinAt_inter hux).1 (hfs x ⟨h, hx.2⟩)
      else continuousWithinAt_of_notMem_closure ?_
    rwa [hs.closure_eq]
  · refine if h : x ∈ t then (continuousWithinAt_inter hux).1 (hft x ⟨h, hx.2⟩)
      else continuousWithinAt_of_notMem_closure ?_
    rwa [ht.closure_eq]

/-- If `s` and `t` are closed and `u` is open, a function continuous on `s ×ˢ u` and on
`t ×ˢ u` is continuous on `(s ∪ t) ×ˢ u`. -/
theorem ContinuousOn.union_prod_of_isClosed {f : α × β → γ} {s t : Set α} {u : Set β}
    (hfs : ContinuousOn f (s ×ˢ u)) (hft : ContinuousOn f (t ×ˢ u)) (hs : IsClosed s)
    (ht : IsClosed t) (hu : IsOpen u) : ContinuousOn f ((s ∪ t) ×ˢ u) := by
  rw [prod_eq] at hfs hft ⊢
  rw [preimage_union]
  exact hfs.union_inter_of_isClosed hft (hs.preimage continuous_fst)
    (ht.preimage continuous_fst) (hu.preimage continuous_snd)

end
