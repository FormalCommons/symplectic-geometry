/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Normed.Operator.Perturbation
public import TauCeti.Geometry.Symplectic.Orientation

/-!
# Maps with dominant complex-linear part

Let `J`, `J'` be almost complex structures on finite-dimensional real normed spaces `V`, `W`, let
`A : V ≃L[ℝ] W` be complex-linear, and let `B : V →L[ℝ] W` satisfy `‖B‖ * ‖A⁻¹‖ < 1`. Then
`A + B` is an isomorphism (`ContinuousLinearEquiv.addOfNormLt`) that carries the complex
orientation of `J` to that of `J'`. No hypothesis on `B` beyond its norm is needed; in the
applications `B` is the antilinear part.

## Main results

* `TauCeti.AlmostComplexStructure.orientation_map_add_of_norm_lt`: if `A` is complex-linear, then
  `A + B` carries the complex orientation of `J` to that of `J'`.

The proof combines `Orientation.map_addOfNormLt`, from
`SymplecticGeometry.Analysis.Normed.Operator.Perturbation`, with Tau Ceti's
`TauCeti.AlmostComplexStructure.map_orientation`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4.
* [S. K. Donaldson, *Lefschetz pencils on symplectic manifolds*][Donaldson1999].
-/

public section

noncomputable section

open Module

namespace TauCeti.AlmostComplexStructure

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {k : ℕ}

/-- **Maps with dominant complex-linear part preserve the complex orientation.** Let `J`, `J'` be
almost complex structures on `V`, `W`, let `A : V ≃L[ℝ] W` be complex-linear, and let
`B : V →L[ℝ] W` satisfy `‖B‖ * ‖A⁻¹‖ < 1`. Then the isomorphism `A + B`
(`ContinuousLinearEquiv.addOfNormLt`) carries the complex orientation of `J` to that of `J'`. -/
theorem orientation_map_add_of_norm_lt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {A : V ≃L[ℝ] W}
    (hA : IsComplexLinear J.toLinearMap J'.toLinearMap (A : V →ₗ[ℝ] W)) {B : V →L[ℝ] W}
    (h : ‖B‖ * ‖(A.symm : W →L[ℝ] V)‖ < 1) (hk : finrank ℝ V = k) (hk' : finrank ℝ W = k) :
    Orientation.map (Fin k) (A.addOfNormLt B h).toLinearEquiv (J.orientation hk) =
      J'.orientation hk' := by
  rw [Orientation.map_addOfNormLt _ ((Fintype.card_fin k).trans hk.symm),
    map_orientation ((isComplexLinearMap_iff_isComplexLinear _ _ _).2 hA) hk]

end TauCeti.AlmostComplexStructure
