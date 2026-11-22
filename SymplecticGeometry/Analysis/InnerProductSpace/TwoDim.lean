/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.InnerProductSpace.TwoDim
import TauCeti.Analysis.InnerProductSpace.TwoDim

/-!
# Maps of an oriented Euclidean plane that turn the rotation into multiplication by `i`

Let `E` be an oriented real inner product space of dimension two, with its rotation by a right
angle `J = o.rightAngleRotation`. A real-linear map `f` from `E` to a complex normed space that
carries `J` to multiplication by `i` is, read through an orientation-preserving isometry
`ℂ ≃ₗᵢ[ℝ] E`, complex linear. So if it is not zero it is conformal
(`Orientation.isConformalMap_of_map_rightAngleRotation`). When the target is an inner product space,
Mathlib's `isConformalMap_iff` restates this: `f` multiplies inner products by a positive constant.

## Main results

* `Orientation.isConformalMap_of_map_rightAngleRotation`: a nonzero real-linear map from an
  oriented Euclidean plane to a complex normed space that carries the rotation by a right angle to
  multiplication by `i` is conformal.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Exercise 4.2.8.
-/

public section

open Module Complex

namespace Orientation

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]
  [NormedAddCommGroup F] [NormedSpace ℂ F] (o : Orientation ℝ E (Fin 2))

/-- A nonzero real-linear map `f` from an oriented Euclidean plane to a complex normed space with
`f (J x) = i • f x`, where `J` is the rotation by a right angle, is conformal. -/
theorem isConformalMap_of_map_rightAngleRotation {f : E →L[ℝ] F}
    (hf : ∀ x, f (o.rightAngleRotation x) = I • f x) (h0 : f ≠ 0) : IsConformalMap f := by
  -- An orientation-preserving isometry `φ : ℂ ≃ₗᵢ[ℝ] E`, which carries `i` to the rotation.
  let b := o.finOrthonormalBasis two_pos Fact.out
  let φ : ℂ ≃ₗᵢ[ℝ] E := Complex.isometryOfOrthonormal b
  have hφo : Orientation.map (Fin 2) φ.symm.toLinearEquiv o = Complex.orientation := by
    conv_lhs => rw [← o.finOrthonormalBasis_orientation two_pos Fact.out]
    exact Complex.map_isometryOfOrthonormal_symm_orientation b
  have hφ (z : ℂ) : φ (I * z) = o.rightAngleRotation (φ z) := by
    apply φ.symm.injective
    rw [o.rightAngleRotation_map_complex φ.symm hφo, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.symm_apply_apply]
  -- `f ∘ φ` commutes with multiplication by `i`, so it is complex linear.
  let ℓ := f.comp φ.toLinearIsometry.toContinuousLinearMap
  let g := ℓ.complexOfReal (by simpa [ℓ, ← hf] using congrArg f (hφ 1))
  have hf' : f = (g.restrictScalars ℝ).comp φ.symm.toLinearIsometry.toContinuousLinearMap := by
    ext x; simp [g, ℓ]
  have hg0 : g ≠ 0 := fun h ↦ h0 (by rw [hf', h]; simp)
  rw [hf']
  exact (isConformalMap_complex_linear hg0).comp φ.symm.toLinearIsometry.isConformalMap

end Orientation

end
