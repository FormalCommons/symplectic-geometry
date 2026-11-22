/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Module.Hom

/-!
# Complex linear maps

General facts about real-linear maps that intertwine two linear complex structures, Tau Ceti's
`TauCeti.IsComplexLinearMap`. They belong next to Tau Ceti's
`TauCeti/Geometry/Symplectic/Complex/Module/Hom.lean`.

## Main results

* `TauCeti.IsComplexLinearMap.symm_linearEquiv`: the inverse of a complex linear isomorphism is
  complex linear.
* `TauCeti.IsComplexLinearMap.exists_leftInverse_of_injective`: an injective complex linear map
  has a complex linear left inverse.
* `TauCeti.AlmostComplexStructure.isComplexLinearMap_self_iff_commute`: an endomorphism is complex
  linear for `J` exactly when it commutes with `J`.
-/

public section

namespace TauCeti

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The inverse of a linear isomorphism that is complex linear from `J` to `J'` is complex
linear from `J'` to `J`. -/
theorem IsComplexLinearMap.symm_linearEquiv {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {e : V ≃ₗ[ℝ] W} (h : IsComplexLinearMap J J' e.toLinearMap) :
    IsComplexLinearMap J' J e.symm.toLinearMap :=
  (isComplexLinearMap_iff_isComplexLinear _ _ _).2
    ((isComplexLinearMap_iff_isComplexLinear _ _ _).1 h).symm

/-- An injective real-linear map that is complex linear from `J` to `J'` has a left inverse that
is complex linear from `J'` to `J`. -/
theorem IsComplexLinearMap.exists_leftInverse_of_injective {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {F : V →ₗ[ℝ] W} (hF : IsComplexLinearMap J J' F)
    (hinj : Function.Injective F) :
    ∃ G : W →ₗ[ℝ] V, IsComplexLinearMap J' J G ∧ G ∘ₗ F = LinearMap.id := by
  let := J.complexModule
  let := J'.complexModule
  let := J.complexModule_isScalarTower
  let := J'.complexModule_isScalarTower
  -- A `ℂ`-linear left inverse of `F`, for the complex module structures of `J` and `J'`.
  obtain ⟨G, hG⟩ := hF.toComplexLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hinj)
  exact ⟨G.restrictScalars ℝ, isComplexLinearMap_restrictScalars J' J G,
    LinearMap.ext fun v ↦ LinearMap.congr_fun hG v⟩

/-- An endomorphism of `V` is complex linear for `J` exactly when it commutes with `J`. -/
theorem AlmostComplexStructure.isComplexLinearMap_self_iff_commute (J : AlmostComplexStructure V)
    (f : Module.End ℝ V) : IsComplexLinearMap J J f ↔ Commute f J.toLinearMap := by
  rw [IsComplexLinearMap, Commute, SemiconjBy, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    eq_comm]

end TauCeti

end
