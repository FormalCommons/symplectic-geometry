/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.ConnectedMap.Basic

/-!
# Path-connectedness under `n`-connected maps

An `n`-connected map `f : X → Y` (Tau Ceti's `ContinuousMap.IsNConnected`) with `1 ≤ n` is a
bijection on path components, so `X` is path-connected exactly when `Y` is:
`ContinuousMap.IsNConnected.pathConnectedSpace_iff`. This is the degree-zero counterpart of Tau
Ceti's `ContinuousMap.IsNConnected.simplyConnectedSpace_iff`. Its statement and proof adapt Tau
Ceti's `ContinuousMap.IsWeakHomotopyEquivalence.pathConnectedSpace_iff` from weak homotopy
equivalences to `n`-connected maps.
-/

public section

namespace ContinuousMap.IsNConnected

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)} {n : ℕ}

/-- If `f : X → Y` is `n`-connected with `1 ≤ n`, then `X` is path-connected exactly when `Y`
is. -/
theorem pathConnectedSpace_iff (hf : f.IsNConnected n) (hn : 1 ≤ n) :
    PathConnectedSpace X ↔ PathConnectedSpace Y := by
  refine ⟨fun _ ↦ ⟨⟨f (Classical.arbitrary X)⟩, fun y y' ↦ ?_⟩, fun _ ↦ ?_⟩
  · -- Both points are joined to points of the image, which are joined to each other.
    obtain ⟨x, hx⟩ := hf.exists_joined y
    obtain ⟨x', hx'⟩ := hf.exists_joined y'
    exact hx.symm.trans (((PathConnectedSpace.joined x x').map f.continuous).trans hx')
  · -- Every point of `Y` is joined to a point of the image, so `X` is nonempty.
    obtain ⟨a, -⟩ := hf.exists_joined (Classical.arbitrary Y)
    exact ⟨⟨a⟩, fun a b ↦ (joined_iff_of_injective_homotopyGroupMap f (hf.injective 0 hn a)).1
      (PathConnectedSpace.joined _ _)⟩

end ContinuousMap.IsNConnected

end
