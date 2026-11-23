/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The coordinate of the half-line

The half-line `EuclideanHalfSpace 1` is the set of points `t` of `ℝ¹` with `0 ≤ t 0`. This file
shows that its coordinate `t ↦ t 0`, a map to `ℝ`, is an immersion at every point, the boundary
point `0` included, and a local diffeomorphism at every point where it is positive. Both proofs
identify `ℝ¹` with `ℝ` by Mathlib's `PiLp.equivOfUnique`.

That the coordinate preserves orientation is in
`SymplecticGeometry.Geometry.Manifold.Instances.HalfLine.Orientation`.

## Main results

* `TauCeti.EuclideanHalfSpace.isImmersionAt_val_zero`: the coordinate of the half-line is an
  immersion into `ℝ`, the boundary point included.
* `TauCeti.EuclideanHalfSpace.isLocalDiffeomorphAt_val_zero`: the coordinate of the half-line is a
  local diffeomorphism to `ℝ` where it is positive.
-/

public section

open Manifold

namespace TauCeti.EuclideanHalfSpace

variable {n : WithTop ℕ∞}

/-- The coordinate `t ↦ t 0` of the half-line is a `C^n` immersion into `ℝ` at every point, the
boundary point `0` included. -/
theorem isImmersionAt_val_zero (t : EuclideanHalfSpace 1) :
    IsImmersionAt (𝓡∂ 1) 𝓘(ℝ) n (fun s : EuclideanHalfSpace 1 ↦ s.val 0) t := by
  refine (IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt (F := PUnit.{1})
    (by fun_prop) ((ContinuousLinearEquiv.prodUnique ℝ _ _).trans
      (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ)) ?_).isImmersionAt
  intro u hu
  have h0 : 0 ≤ u 0 := by
    have := (extChartAt_target_subset_range (I := 𝓡∂ 1) t) hu
    rwa [range_modelWithCornersEuclideanHalfSpace] at this
  simp [modelWithCornersEuclideanHalfSpace_symm_apply_of_le h0]

/-- The coordinate `t ↦ t 0` of the half-line `EuclideanHalfSpace 1` is a `C^n` local
diffeomorphism to `ℝ` at every point where it is positive. -/
theorem isLocalDiffeomorphAt_val_zero {t : EuclideanHalfSpace 1} (ht : 0 < t.val 0) :
    IsLocalDiffeomorphAt (𝓡∂ 1) 𝓘(ℝ) n (fun s : EuclideanHalfSpace 1 ↦ s.val 0) t := by
  have h := ((𝓡∂ 1).isLocalDiffeomorphAt_coe (n := n) (x := t) (by
    rwa [interior_range_modelWithCornersEuclideanHalfSpace])).comp
    (hg := (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ).isLocalDiffeomorph ((𝓡∂ 1) t))
  convert h using 1
  funext s
  simp

end TauCeti.EuclideanHalfSpace

end
