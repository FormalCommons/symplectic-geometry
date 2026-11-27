/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Topology.Path

import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Circles as loops, and the lower half of a circle

The circle `circleMap z₀ r`, run once counterclockwise from a given angle, is a loop in `ℂ`.

Between the angles `π` and `2π`, the circle `circleMap z₀ r` of radius `r ≥ 0` runs in the
closed half-plane below its centre. This goes with Tau Ceti's `TauCeti.im_le_circleMap_im_iff`,
which says that between `0` and `π` it runs in the closed half-plane above it.

## Main definitions

* `circlePath z₀ r θ`: the circle `circleMap z₀ r`, run once counterclockwise from the
  angle `θ`.

## Main results

* `circlePath_apply`: `circlePath z₀ r θ t = circleMap z₀ r (θ + 2πt)`.
* `circleMap_im_le_im`: for `θ ∈ [π, 2π]`, `(circleMap z₀ r θ).im ≤ z₀.im`.
-/

public section

open Real Set

/-- The circle `circleMap z₀ r` about `z₀` of radius `r`, run once counterclockwise from the
angle `θ`: the loop `t ↦ circleMap z₀ r (θ + 2πt)` based at `circleMap z₀ r θ`. -/
noncomputable def circlePath (z₀ : ℂ) (r θ : ℝ) :
    Path (circleMap z₀ r θ) (circleMap z₀ r θ) where
  toFun t := circleMap z₀ r (θ + 2 * π * t)
  continuous_toFun :=
    (TauCeti.continuous_circleMap_uncurry z₀).comp
      (f := fun t : unitInterval ↦ (r, θ + 2 * π * t))
      (by fun_prop)
  source' := by simp
  target' := by simpa using periodic_circleMap z₀ r θ

@[simp]
theorem circlePath_apply (z₀ : ℂ) (r θ : ℝ) (t : unitInterval) :
    circlePath z₀ r θ t = circleMap z₀ r (θ + 2 * π * t) :=
  (rfl)

/-- Between the angles `π` and `2π`, a circle of radius `r ≥ 0` lies on or below its centre. -/
theorem circleMap_im_le_im {z₀ : ℂ} {r θ : ℝ} (hr : 0 ≤ r) (hθ : θ ∈ Icc π (2 * π)) :
    (circleMap z₀ r θ).im ≤ z₀.im := by
  rw [TauCeti.circleMap_im, add_le_iff_nonpos_right, ← sin_sub_two_pi]
  exact mul_nonpos_of_nonneg_of_nonpos hr
    (sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [hθ.2]) (by linarith [hθ.1]))

end
