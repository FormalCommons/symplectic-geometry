/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Geometry.Manifold.Orientation.Preserving

/-!
# The coordinate of the half-line preserves orientation

Orient the half-line `EuclideanHalfSpace 1` by the standard basis of `ℝ¹`, as a constant
orientation of the model (`TauCeti.Manifold.Orientation.model`), and `ℝ` by its standard
orientation `TauCeti.Manifold.Orientation.real`. This file shows that the coordinate `t ↦ t 0`
preserves orientation at every point, the boundary point `0` included: its derivative is the
projection `EuclideanSpace.proj 0`, which sends the standard basis vector of `ℝ¹` to `1`.

## Main results

* `TauCeti.EuclideanHalfSpace.isOrientationPreservingAt_val_zero`: the coordinate of the half-line
  preserves orientation, to the standard orientation of `ℝ`.
-/

public section

open Manifold

namespace TauCeti.EuclideanHalfSpace

/-- The coordinate `s ↦ s 0` of the one-dimensional half-space model preserves orientation at
every point, from the orientation of its standard basis to the standard orientation of `ℝ`. -/
theorem isOrientationPreservingAt_val_zero (t : EuclideanHalfSpace 1) :
    Manifold.Orientation.IsOrientationPreservingAt
      (Manifold.Orientation.model (I := 𝓡∂ 1)
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation (by simp))
      Manifold.Orientation.real (fun s : EuclideanHalfSpace 1 ↦ s.val 0) t := by
  have hf : EuclideanSpace.proj (0 : Fin 1) ∘ (𝓡∂ 1) = fun s : EuclideanHalfSpace 1 ↦ s.val 0 := by
    funext s
    simp [modelWithCornersEuclideanHalfSpace_apply]
  have hp := (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).mdifferentiableAt
    (x := (𝓡∂ 1) t)
  have hm : mfderiv (𝓡∂ 1) 𝓘(ℝ) (EuclideanSpace.proj (0 : Fin 1) ∘ (𝓡∂ 1)) t =
      EuclideanSpace.proj 0 := by
    rw [mfderiv_comp _ hp (𝓡∂ 1).hasMFDerivAt.mdifferentiableAt, (𝓡∂ 1).hasMFDerivAt.mfderiv,
      ContinuousLinearMap.mfderiv_eq]
    exact ContinuousLinearMap.comp_id _
  rw [← hf]
  refine (Manifold.Orientation.isOrientationPreservingAt_iff_of_basis
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis (Module.Basis.singleton (Fin 1) ℝ)
    (fun i ↦ ?_)).2 (iff_of_true ?_ ?_)
  · rw [hm]
    fin_cases i
    have h : EuclideanSpace.proj (0 : Fin 1) ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis 0) =
        Module.Basis.singleton (Fin 1) ℝ 0 := by
      simp
    -- This is `h`, with the tangent spaces read as `EuclideanSpace ℝ (Fin 1)` and `ℝ`.
    exact h
  · exact (Manifold.Orientation.orientationAt_model _ _ _).symm
  · exact (Manifold.Orientation.orientationAt_real _).symm

end TauCeti.EuclideanHalfSpace

end
