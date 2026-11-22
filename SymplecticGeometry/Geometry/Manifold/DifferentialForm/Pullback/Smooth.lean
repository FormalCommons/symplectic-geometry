/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Pullback of smooth forms along a constant map

The differential of a constant map is zero, so pulling a smooth form of positive degree back
along a constant map gives the zero form (`TauCeti.SmoothForm.mpullback_const`).

## Main results

* `TauCeti.SmoothForm.mpullback_const`: the pullback of a smooth `(k + 1)`-form along a constant
  map is `0`.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothForm

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [IsManifold I 1 M] [IsManifold I' 1 M'] {k : ℕ}

/-- The pullback of a smooth form of positive degree along a constant map is zero. -/
@[simp]
theorem mpullback_const (c : M') (hc : ContMDiff I I' ∞ fun _ : M ↦ c)
    (φ : SmoothForm I' M' F (k + 1)) : mpullback (fun _ : M ↦ c) hc φ = 0 := by
  refine Subtype.ext (funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
  rw [mpullback_apply, mfderiv_const]
  exact (φ.val c).map_coord_zero 0 rfl

end SmoothForm

end TauCeti
