/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Basic

/-!
# Orientations read in the identity trivialization of a trivial bundle

A complement to Tau Ceti's `TauCeti/Topology/VectorBundle/Orientation/Basic.lean`. The identity
trivialization `Bundle.Trivial.trivialization B F` of the trivial bundle `B × F` reads an
orientation of a fibre, which is `F`, as itself
(`Bundle.Trivial.mapOrientation_trivialization`).

## Main results

* `Bundle.Trivial.mapOrientation_trivialization`: `Bundle.Trivialization.mapOrientation` of the
  identity trivialization is the identity.
-/

public section

namespace Bundle.Trivial

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*}

/-- The identity trivialization of `B × F` reads every orientation of the fibre `F` as itself. -/
@[simp]
theorem mapOrientation_trivialization {x : B}
    (hx : x ∈ (Bundle.Trivial.trivialization B F).baseSet) (ω : Orientation ℝ F ι) :
    (Bundle.Trivial.trivialization B F).mapOrientation ι hx ω = ω := by
  rw [Trivialization.mapOrientation_apply]
  have hrefl : Trivialization.linearEquivAt ℝ (Bundle.Trivial.trivialization B F) x hx =
      LinearEquiv.refl ℝ F :=
    LinearEquiv.ext fun v ↦ by simp [Trivialization.linearEquivAt_apply]
  rw [hrefl, Orientation.map_refl, Equiv.refl_apply]

end Bundle.Trivial
