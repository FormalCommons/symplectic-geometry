/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# The lower half of a circle

Between the angles `π` and `2π`, the circle `circleMap z₀ r` of radius `r ≥ 0` runs in the
closed half-plane below its centre. This goes with Tau Ceti's `TauCeti.im_le_circleMap_im_iff`,
which says that between `0` and `π` it runs in the closed half-plane above it.

## Main results

* `circleMap_im_le_im`: for `θ ∈ [π, 2π]`, `(circleMap z₀ r θ).im ≤ z₀.im`.
-/

public section

open Real Set

/-- Between the angles `π` and `2π`, a circle of radius `r ≥ 0` lies on or below its centre. -/
theorem circleMap_im_le_im {z₀ : ℂ} {r θ : ℝ} (hr : 0 ≤ r) (hθ : θ ∈ Icc π (2 * π)) :
    (circleMap z₀ r θ).im ≤ z₀.im := by
  rw [TauCeti.circleMap_im, add_le_iff_nonpos_right, ← sin_sub_two_pi]
  exact mul_nonpos_of_nonneg_of_nonpos hr
    (sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [hθ.2]) (by linarith [hθ.1]))

end
