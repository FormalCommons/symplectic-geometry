/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.ConnectedMap.Basic

/-!
# Path-connectedness under `n`-connected maps

An `n`-connected map `f : X → Y` (Tau Ceti's `ContinuousMap.IsNConnected`) with `1 ≤ n`, from a
nonempty space, is a bijection on path components, so `X` is path-connected exactly when `Y` is:
`ContinuousMap.IsNConnected.pathConnectedSpace_iff`. This is the degree-zero counterpart of Tau
Ceti's `ContinuousMap.IsNConnected.simplyConnectedSpace_iff`.
-/

public section

namespace ContinuousMap.IsNConnected

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)} {n : ℕ}

/-- If `f : X → Y` is `n`-connected with `1 ≤ n` and `X` is nonempty, then `X` is path-connected
exactly when `Y` is. -/
theorem pathConnectedSpace_iff [Nonempty X] (hf : f.IsNConnected n) (hn : 1 ≤ n) :
    PathConnectedSpace X ↔ PathConnectedSpace Y := by
  refine ⟨fun _ ↦ ⟨⟨f (Classical.arbitrary X)⟩, fun y y' ↦ ?_⟩,
    fun _ ↦ ⟨inferInstance, fun a b ↦ ?_⟩⟩
  · obtain ⟨x, hx⟩ := hf.exists_joined y
    obtain ⟨x', hx'⟩ := hf.exists_joined y'
    exact hx.symm.trans (((PathConnectedSpace.joined x x').map f.continuous).trans hx')
  · exact (joined_iff_of_injective_homotopyGroupMap f (hf.injective 0 hn a)).1
      (PathConnectedSpace.joined _ _)

end ContinuousMap.IsNConnected

end
