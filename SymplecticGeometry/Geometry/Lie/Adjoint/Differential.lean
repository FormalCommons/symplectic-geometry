/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic

/-!
# The adjoint action as the differential of conjugation

Tau Ceti defines the adjoint action `Ad_g` of a Lie group `G` on its Lie algebra as the
differential at `1` of the diffeomorphism `TauCeti.Lie.conjDiffeomorph g`. This file states the
same facts for the plain function `x ↦ g * x * g⁻¹`, so that a map written with conjugation can be
differentiated without passing to the diffeomorphism.

## Main results

* `TauCeti.Lie.mdifferentiable_conj`: conjugation by `g` is differentiable.
* `TauCeti.Lie.mfderiv_conj_one_apply`: its differential at `1` is `Ad_g`.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.Lie

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I 1 G]

/-- Conjugation `x ↦ g * x * g⁻¹` by an element `g` of a `C¹` Lie group is differentiable. -/
theorem mdifferentiable_conj (g : G) : MDifferentiable I I (fun x : G ↦ g * x * g⁻¹) :=
  ((contMDiff_const.mul contMDiff_id).mul contMDiff_const).mdifferentiable one_ne_zero

/-- The differential at `1` of conjugation `x ↦ g * x * g⁻¹` is the adjoint action `Ad_g`. -/
theorem mfderiv_conj_one_apply (g : G) (X : GroupLieAlgebra I G) :
    mfderiv I I (fun x : G ↦ g * x * g⁻¹) 1 X = adjointRepresentation 𝕜 I G g X := by
  rw [adjointRepresentation_apply, adjointContinuousLinearMap_apply]
  congr 2
  exact funext fun x ↦ (conjDiffeomorph_apply g x).symm

end TauCeti.Lie

end
