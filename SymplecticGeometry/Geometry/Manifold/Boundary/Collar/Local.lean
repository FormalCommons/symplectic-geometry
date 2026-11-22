/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Smoothness of the normal ray of the half-line

This file extends Tau Ceti's `TauCeti.Geometry.Manifold.Boundary.Collar.Local`. Tau Ceti's normal
ray `TauCeti.EuclideanHalfSpace.normalRay : ℝ → EuclideanHalfSpace 1` sends `r` to the point at
normal distance `max r 0` from the boundary, and is continuous. On `[0, ∞)` it is the inverse of
the model with corners of the half-line, composed with a linear map, so it is smooth there, up to
the boundary point `0`.

## Main results

* `TauCeti.EuclideanHalfSpace.contMDiffOn_normalRay`: the normal ray is smooth on `[0, ∞)`.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti.EuclideanHalfSpace

/-- The normal ray of the half-line is `C^n` on `[0, ∞)`, for every `n`. -/
theorem contMDiffOn_normalRay {n : WithTop ℕ∞} :
    ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) n normalRay (Ici 0) := by
  let e : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 1) ℝ).symm
  have he (r : ℝ) : e r 0 = r := rfl
  refine ((𝓡∂ 1).contMDiffOn_symm.comp (s := Ici 0) e.contDiff.contMDiff.contMDiffOn
    fun r (hr : 0 ≤ r) ↦ ?_).congr fun r _ ↦ ?_
  · rw [mem_preimage, range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq, he]
    exact hr
  · rw [normalRay_eq_symm, Function.comp_apply]
    congr 1

end TauCeti.EuclideanHalfSpace

end
