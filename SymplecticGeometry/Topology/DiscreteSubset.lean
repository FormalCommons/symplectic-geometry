/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.DiscreteSubset

/-!
# Finiteness of isolated points of a closed set in a compact set

If `s` is closed and each point of `s` lying in a compact set `K` has a punctured neighbourhood
missing `s`, then `s ∩ K` is finite (`IsClosed.finite_inter_of_forall_eventually_notMem`): this
intersection is compact, and it is discrete by Mathlib's `isDiscrete_iff_nhdsNE`, so
`IsCompact.finite` applies. These are the steps of the proof of Tau Ceti's
`TauCeti.finite_criticalPoints_inter_of_forall_isManifoldNondegenerateCriticalPoint`, here for
any closed set.
-/

public section

open Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X] {s K : Set X}

/-- If `s` is closed, `K` is compact, and every point of `s ∩ K` has a punctured neighbourhood
disjoint from `s`, then `s ∩ K` is finite. Nothing is assumed about the points of `s` outside
`K`. -/
theorem IsClosed.finite_inter_of_forall_eventually_notMem (hs : IsClosed s) (hK : IsCompact K)
    (h : ∀ x ∈ s ∩ K, ∀ᶠ y in 𝓝[≠] x, y ∉ s) : (s ∩ K).Finite :=
  (hK.inter_left hs).finite <| isDiscrete_iff_nhdsNE.2 fun x hx ↦
    inf_principal_eq_bot.2 ((h x hx).mono fun _ hy hyK ↦ hy hyK.1)

end
