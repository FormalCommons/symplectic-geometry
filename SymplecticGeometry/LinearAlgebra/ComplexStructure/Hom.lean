/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# Complex linear maps

General facts about real-linear maps that intertwine two linear complex structures, Tau Ceti's
`TauCeti.IsComplexLinearMap`. They belong next to Tau Ceti's
`TauCeti/Geometry/Symplectic/Complex/Module/Hom.lean`.

## Main results

* `TauCeti.IsComplexLinearMap.symm_linearEquiv`: the inverse of a complex linear isomorphism is
  complex linear.
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

/-- An endomorphism of `V` is complex linear for `J` exactly when it commutes with `J`. -/
theorem AlmostComplexStructure.isComplexLinearMap_self_iff_commute (J : AlmostComplexStructure V)
    (f : Module.End ℝ V) : IsComplexLinearMap J J f ↔ Commute f J.toLinearMap := by
  rw [IsComplexLinearMap, Commute, SemiconjBy, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    eq_comm]

end TauCeti

end
