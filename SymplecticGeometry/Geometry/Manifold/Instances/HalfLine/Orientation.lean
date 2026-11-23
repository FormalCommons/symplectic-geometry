/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
public import TauCeti.Geometry.Manifold.Orientation.OpenSubset
public import TauCeti.Geometry.Manifold.Orientation.Preserving
import SymplecticGeometry.Geometry.Manifold.Orientation.OpenSubset

/-!
# The orientation of the half-line and of its initial segments

Orient the half-line `EuclideanHalfSpace 1` by the standard basis of `ℝ¹`, as a constant
orientation of the model (`TauCeti.Manifold.Orientation.model`), and `ℝ` by its standard
orientation `TauCeti.Manifold.Orientation.real`. This file shows that the coordinate `t ↦ t 0`
preserves orientation at every point, the boundary point `0` included: its derivative is the
projection `EuclideanSpace.proj 0`, which sends the standard basis vector of `ℝ¹` to `1`.

It also orients the open initial segment `[0, ε)` of the half-line, Tau Ceti's
`TauCeti.EuclideanHalfSpace.normalIioOpens ε`, by restricting this orientation, and shows that
the coordinate preserves orientation there too.

## Main definitions

* `TauCeti.EuclideanHalfSpace.normalIioOpensOrientation`: the standard orientation of the
  initial segment `[0, ε)` of the one-dimensional half-space model.

## Main results

* `TauCeti.EuclideanHalfSpace.isOrientationPreservingAt_val_zero`: the coordinate of the half-line
  preserves orientation, to the standard orientation of `ℝ`.
* `TauCeti.EuclideanHalfSpace.isOrientationPreservingAt_normalIioOpens_val_zero`: the coordinate
  `t ↦ t 0` of `[0, ε)` preserves orientation, to the standard orientation of `ℝ`, by
  restricting `TauCeti.EuclideanHalfSpace.isOrientationPreservingAt_val_zero`.
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

/-- The standard orientation of the initial segment `[0, ε)` of the one-dimensional half-space
model: the restriction of the constant orientation of the standard basis. -/
noncomputable def normalIioOpensOrientation (ε : ℝ) :
    Manifold.Orientation (𝓡∂ 1) (normalIioOpens ε) (Fin 1) :=
  (Manifold.Orientation.model (I := 𝓡∂ 1)
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation (by simp)).restrict _

theorem normalIioOpensOrientation_def (ε : ℝ) :
    normalIioOpensOrientation ε =
      (Manifold.Orientation.model (I := 𝓡∂ 1)
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation (by simp)).restrict
          (normalIioOpens ε) :=
  (rfl)

/-- At every point, the standard orientation of `[0, ε)` is that of the standard basis. -/
@[simp]
theorem orientationAt_normalIioOpensOrientation {ε : ℝ} (t : normalIioOpens ε) :
    (normalIioOpensOrientation ε).orientationAt t =
      (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation := by
  rw [normalIioOpensOrientation_def, Manifold.Orientation.orientationAt_restrict,
    Manifold.Orientation.orientationAt_model]

/-- The coordinate `t ↦ t 0` of `[0, ε)` preserves orientation at every point, from the standard
orientation of `[0, ε)` to the standard orientation of `ℝ`. -/
theorem isOrientationPreservingAt_normalIioOpens_val_zero {ε : ℝ} (t : normalIioOpens ε) :
    Manifold.Orientation.IsOrientationPreservingAt (normalIioOpensOrientation ε)
      Manifold.Orientation.real (fun s : normalIioOpens ε ↦ (s : EuclideanHalfSpace 1).val 0)
      t :=
  (isOrientationPreservingAt_val_zero t).comp
    (Manifold.Orientation.isOrientationPreservingAt_restrict _ _ t)

end TauCeti.EuclideanHalfSpace

end
