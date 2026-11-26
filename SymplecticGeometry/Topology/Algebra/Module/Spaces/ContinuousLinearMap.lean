/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import SymplecticGeometry.Topology.Algebra.Module.Equiv.Basic

/-!
# Conjugation of continuous endomorphisms by an automorphism

Lemmas about `ContinuousLinearEquiv.conjContinuousAlgEquiv` that Mathlib does not state at the
pinned version, kept in its namespace so that they can move upstream unchanged.

## Main results

* `ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_eq_mul`: for an automorphism `e` of a
  space, the algebra automorphism `e.conjContinuousAlgEquiv` of its continuous endomorphisms is
  the conjugation `f ↦ u * f * u⁻¹` by the unit `u = e.toUnit` of that ring.
-/

public section

namespace ContinuousLinearEquiv

variable {𝕜 : Type*} [NormedField 𝕜] {G : Type*} [AddCommGroup G] [Module 𝕜 G]
  [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

/-- Conjugating a continuous endomorphism `f` by an automorphism `e` is multiplying it by the unit
`e.toUnit` on the left and by its inverse on the right, in the ring of continuous
endomorphisms. -/
theorem conjContinuousAlgEquiv_apply_eq_mul (e : G ≃L[𝕜] G) (f : G →L[𝕜] G) :
    e.conjContinuousAlgEquiv f = ↑e.toUnit * f * ↑e.toUnit⁻¹ := by
  ext
  simp

end ContinuousLinearEquiv

end
