/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Pullback of forms: negation and constant maps

Pulling a form back commutes with negation (`TauCeti.mpullback_neg`), as Tau Ceti's
`TauCeti.mpullback_sub` says for subtraction.

The differential of a constant map is zero, so pulling a smooth form of positive degree back
along a constant map gives the zero form (`TauCeti.SmoothForm.mpullback_const`).

## Main results

* `TauCeti.mpullback_neg`: the pullback of `-φ` is minus the pullback of `φ`.
* `TauCeti.SmoothForm.mpullback_const`: the pullback of a smooth `(k + 1)`-form along a constant
  map is `0`.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Pullback commutes with negation. -/
@[simp]
theorem mpullback_neg (f : M → M') (φ : RoughForm I' M' F k) :
    mpullback I I' f (-φ) = -mpullback I I' f φ := by
  funext x
  ext v
  simp [mpullback_apply]

namespace SmoothForm

variable [IsManifold I 1 M] [IsManifold I' 1 M']

/-- The pullback of a smooth form of positive degree along a constant map is zero. -/
@[simp]
theorem mpullback_const (c : M') (hc : ContMDiff I I' ∞ fun _ : M ↦ c)
    (φ : SmoothForm I' M' F (k + 1)) : mpullback (fun _ : M ↦ c) hc φ = 0 := by
  refine Subtype.ext (funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
  rw [mpullback_apply, mfderiv_const]
  exact (φ.val c).map_coord_zero 0 rfl

end SmoothForm

end TauCeti
