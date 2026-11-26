/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Scaling balls about the origin

A complement to Mathlib's `Mathlib.Analysis.Normed.Module.Ball.Pointwise`: in a normed space
over a normed field, scaling by `c⁻¹` sends the ball of radius `‖c‖ * r` about `0` onto the ball
of radius `r` about `0`, stated pointwise. It is kept in the root namespace, next to Mathlib's
`smul_ball`, so that it can move upstream unchanged.

## Main results

* `inv_smul_mem_ball_zero_iff`: for `c ≠ 0`, `c⁻¹ • z` lies in `ball 0 r` exactly when `z` lies in
  `ball 0 (‖c‖ * r)`.
-/

public section

open Metric

variable {𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- For `c ≠ 0`, the point `c⁻¹ • z` lies in the ball of radius `r` about `0` if and only if `z`
lies in the ball of radius `‖c‖ * r` about `0`. -/
theorem inv_smul_mem_ball_zero_iff {c : 𝕜} (hc : c ≠ 0) {z : E} {r : ℝ} :
    c⁻¹ • z ∈ ball (0 : E) r ↔ z ∈ ball (0 : E) (‖c‖ * r) := by
  simp [norm_smul, inv_mul_lt_iff₀ (norm_pos_iff.2 hc)]

end
