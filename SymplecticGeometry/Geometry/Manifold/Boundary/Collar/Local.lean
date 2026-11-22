/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Smoothness of the normal ray of the half-line

This file extends Tau Ceti's `TauCeti.Geometry.Manifold.Boundary.Collar.Local`. Tau Ceti's normal
ray `TauCeti.EuclideanHalfSpace.normalRay : ℝ → EuclideanHalfSpace 1` sends `r` to the point at
normal distance `max r 0` from the boundary, and is continuous. On `[0, ∞)` it is the inverse of
the model with corners of the half-line, composed with a linear map, so it is smooth there, up to
the boundary point `0`. Restricted to `(-∞, 1)`, the ray takes values in the open segment
`normalIioOpens 1`, the normal factor of a collar; this gives the depth map
`TauCeti.EuclideanHalfSpace.normalIioRay`.

## Main definitions

* `TauCeti.EuclideanHalfSpace.normalIioRay`: the normal ray on `(-∞, 1)`, as a map into
  `normalIioOpens 1`.

## Main results

* `TauCeti.EuclideanHalfSpace.contMDiffOn_normalRay`: the normal ray is smooth on `[0, ∞)`.
* `TauCeti.EuclideanHalfSpace.normalRay_mem_normalIioOpens`: the normal ray at `r` lies in
  `normalIioOpens ε`, for `ε > 0`, exactly when `r < ε`.
* `TauCeti.EuclideanHalfSpace.continuous_normalIioRay` and
  `ContMDiffAt.normalIioRay`: the depth map is continuous, and smooth at positive depth.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti.EuclideanHalfSpace

/-- The normal ray of the half-line is `C^n` on `[0, ∞)`, for every `n`. -/
theorem contMDiffOn_normalRay {n : WithTop ℕ∞} :
    ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) n normalRay (Ici 0) :=
  ((𝓡∂ 1).contMDiffOn_symm.comp (s := Ici 0)
    (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ).symm.contDiff.contMDiff.contMDiffOn
    fun r (hr : 0 ≤ r) ↦ by simpa [range_modelWithCornersEuclideanHalfSpace] using hr).congr
    fun r _ ↦ normalRay_eq_symm r

/-- For `ε > 0`, the normal ray at `r` lies in the open segment `[0, ε)` exactly when `r < ε`. -/
theorem normalRay_mem_normalIioOpens {ε r : ℝ} (hε : 0 < ε) :
    normalRay r ∈ normalIioOpens ε ↔ r < ε := by
  rw [mem_normalIioOpens, normalRay_coe_apply, max_lt_iff, and_iff_left hε]

/-- The normal ray on `(-∞, 1)`, as a map into the open segment `normalIioOpens 1`: the point of
`[0, 1)` at depth `max r 0`. -/
noncomputable def normalIioRay (r : Iio (1 : ℝ)) : normalIioOpens 1 :=
  ⟨normalRay r, (normalRay_mem_normalIioOpens one_pos).2 r.property⟩

/-- The point `normalIioRay r` of `[0, 1)` is the normal ray at `r`. -/
@[simp]
theorem coe_normalIioRay (r : Iio (1 : ℝ)) :
    (normalIioRay r : EuclideanHalfSpace 1) = normalRay r := (rfl)

/-- The depth of `normalIioRay r` is `max r 0`. -/
theorem normalIioRay_coe_apply (r : Iio (1 : ℝ)) :
    (normalIioRay r : EuclideanHalfSpace 1).val 0 = max (r : ℝ) 0 :=
  normalRay_coe_apply r

/-- The depth map starts at the origin. -/
@[simp]
theorem normalIioRay_zero :
    normalIioRay ⟨0, one_pos⟩ = normalIioOpensZero one_pos :=
  Subtype.ext (by simp [coe_normalIioOpensZero])

/-- The depth map is continuous. -/
theorem continuous_normalIioRay : Continuous normalIioRay :=
  (continuous_normalRay.comp continuous_subtypeVal).subtype_mk _

end TauCeti.EuclideanHalfSpace

namespace ContMDiffAt

open TauCeti.EuclideanHalfSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The depth map composed with a `C^n` real function `f < 1` is `C^n` at a point where `f` is
positive. -/
theorem normalIioRay {n : WithTop ℕ∞} {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) n f x)
    (h1 : ∀ y, f y < 1) (hx : 0 < f x) :
    ContMDiffAt I (𝓡∂ 1) n (fun y ↦ normalIioRay ⟨f y, h1 y⟩) x :=
  (TauCeti.ContMDiffAt.subtypeVal_comp_iff _ _ _).1
    ((contMDiffOn_normalRay.contMDiffAt (Ici_mem_nhds hx)).comp x hf)

end ContMDiffAt

end
