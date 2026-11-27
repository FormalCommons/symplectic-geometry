/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Connectedness and second countability of a universe lift

The lift `ULift X` of a topological space carries the topology induced by `ULift.down`, and
`Homeomorph.ulift` identifies it with `X`. Mathlib gives the separation and compactness
instances of `ULift X`; this file adds those for connectedness and second countability, each
transported along `Homeomorph.ulift`, and the lemmas that compute `Homeomorph.ulift`.

## Main results

* `Homeomorph.coe_ulift`, `Homeomorph.coe_ulift_symm`: `Homeomorph.ulift` is `ULift.down`, and
  its inverse is `ULift.up`.
* `ULift.instConnectedSpace`: the lift of a connected space is connected.
* `ULift.instSecondCountableTopology`: the lift of a second countable space is second countable.
-/

public section

universe u v

variable {X : Type u} [TopologicalSpace X]

namespace Homeomorph

/-- The homeomorphism `Homeomorph.ulift : ULift X ≃ₜ X` is `ULift.down`. -/
@[simp]
theorem coe_ulift : ⇑(Homeomorph.ulift : ULift.{v} X ≃ₜ X) = ULift.down :=
  (rfl)

/-- The inverse of `Homeomorph.ulift : ULift X ≃ₜ X` is `ULift.up`. -/
@[simp]
theorem coe_ulift_symm : ⇑(Homeomorph.ulift : ULift.{v} X ≃ₜ X).symm = ULift.up :=
  (rfl)

end Homeomorph

namespace ULift

/-- The universe lift of a connected space is connected. -/
instance instConnectedSpace [ConnectedSpace X] : ConnectedSpace (ULift.{v} X) :=
  Homeomorph.ulift.connectedSpace_iff.2 ‹_›

/-- The universe lift of a second countable space is second countable. -/
instance instSecondCountableTopology [SecondCountableTopology X] :
    SecondCountableTopology (ULift.{v} X) :=
  Homeomorph.ulift.secondCountableTopology

end ULift

end
