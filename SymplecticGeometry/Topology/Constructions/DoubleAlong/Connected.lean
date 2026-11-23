/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Constructions.DoubleAlong.Basic

/-!
# Connectedness of a double

Tau Ceti's `TauCeti.DoubleAlong A` glues two copies of a space `X` by the identity along a subset
`A`. When `X` is connected and `A` is nonempty, the double is connected: it is the union of the
two copies of `X`, each connected as a continuous image of `X`, and they meet at the points of
`A`.

## Main results

* `TauCeti.DoubleAlong.connectedSpace`: the double of a connected space along a nonempty subset
  is connected.
-/

public section

open Set

namespace TauCeti.DoubleAlong

variable {X : Type*} [TopologicalSpace X] (A : Set X)

/-- The two copies of `X` cover the double. -/
theorem range_inl_union_range_inr : range (inl A) ∪ range (inr A) = univ :=
  eq_univ_of_forall fun z ↦ (exists_inl_or_inr A z).imp (fun h ↦ h) fun h ↦ h

/-- The double of a connected space along a nonempty subset is connected. -/
instance connectedSpace [ConnectedSpace X] [Nonempty A] : ConnectedSpace (DoubleAlong A) := by
  obtain ⟨a⟩ := ‹Nonempty A›
  rw [connectedSpace_iff_univ, ← range_inl_union_range_inr]
  exact (isConnected_range (inl A).continuous).union
    ⟨inr A a, ⟨a, inl_coe_eq_inr A a⟩, ⟨a, rfl⟩⟩ (isConnected_range (inr A).continuous)

end TauCeti.DoubleAlong

end
