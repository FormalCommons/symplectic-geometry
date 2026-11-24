/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Order.OrderClosed

/-!
# The frontier of an order-connected set

In a linear order with a closed order topology, the frontier of an order-connected set has at
most two points: a point of the frontier cannot have points of the set on both sides, since then
an open interval around it would lie in the set. So it is a lower or an upper bound of the set
lying in its closure, that is, the least or the greatest point of the closure.

* `Set.OrdConnected.frontier_subset`: the frontier of an order-connected set consists of points of
  its closure that are lower or upper bounds of the set.
* `Set.OrdConnected.encard_frontier_le_two`: the frontier of an order-connected set has at most
  two points, so it is finite (`Set.OrdConnected.finite_frontier`).

By `isPreconnected_iff_ordConnected`, this applies to the connected subsets of `ℝ`.
-/

public section

open Set

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] {s : Set α}

namespace Set

/-- Each point of the closure of a set that is a lower bound of the set is the least point of the
closure, so there is at most one. -/
theorem subsingleton_closure_inter_lowerBounds (s : Set α) :
    (closure s ∩ lowerBounds s).Subsingleton := fun _ hx _ hy ↦
  le_antisymm (closure_minimal (fun _ hz ↦ hx.2 hz) isClosed_Ici hy.1)
    (closure_minimal (fun _ hz ↦ hy.2 hz) isClosed_Ici hx.1)

/-- Each point of the closure of a set that is an upper bound of the set is the greatest point of
the closure, so there is at most one. -/
theorem subsingleton_closure_inter_upperBounds (s : Set α) :
    (closure s ∩ upperBounds s).Subsingleton :=
  subsingleton_closure_inter_lowerBounds (α := αᵒᵈ) s

/-- A point of the frontier of an order-connected set lies in its closure and is a lower or an
upper bound of the set. -/
theorem OrdConnected.frontier_subset (hs : s.OrdConnected) :
    frontier s ⊆ closure s ∩ lowerBounds s ∪ closure s ∩ upperBounds s := by
  intro x hx
  rw [← inter_union_distrib_left]
  refine ⟨hx.1, ?_⟩
  by_contra h
  simp only [mem_union, mem_lowerBounds, mem_upperBounds, not_or, not_forall, not_le] at h
  obtain ⟨⟨a, ha, hax⟩, ⟨b, hb, hxb⟩⟩ := h
  exact hx.2 <| mem_interior.2
    ⟨Ioo a b, Ioo_subset_Icc_self.trans (hs.out ha hb), isOpen_Ioo, hax, hxb⟩

/-- The frontier of an order-connected set has at most two points. -/
theorem OrdConnected.encard_frontier_le_two (hs : s.OrdConnected) : (frontier s).encard ≤ 2 :=
  calc (frontier s).encard
      ≤ (closure s ∩ lowerBounds s ∪ closure s ∩ upperBounds s).encard :=
        encard_le_encard hs.frontier_subset
    _ ≤ (closure s ∩ lowerBounds s).encard + (closure s ∩ upperBounds s).encard :=
        encard_union_le _ _
    _ ≤ 1 + 1 := add_le_add
        (encard_le_one_iff_subsingleton.2 (subsingleton_closure_inter_lowerBounds s))
        (encard_le_one_iff_subsingleton.2 (subsingleton_closure_inter_upperBounds s))
    _ = 2 := one_add_one_eq_two

/-- The frontier of an order-connected set is finite. -/
theorem OrdConnected.finite_frontier (hs : s.OrdConnected) : (frontier s).Finite :=
  finite_of_encard_le_coe hs.encard_frontier_le_two

end Set

end
