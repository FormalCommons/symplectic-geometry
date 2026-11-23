/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Inner products on balls

Facts about real inner product spaces that complement Mathlib's
`Mathlib.Analysis.InnerProductSpace.Basic`.

* `mul_norm_le_of_abs_inner_add_le`: if the affine function `z ↦ ⟪z, w⟫ + c` is bounded in
  absolute value by `R` on the closed ball of radius `r ≥ 0` about `0`, then `r ‖w‖ ≤ R`.
  This is the bound that the points `±r w / ‖w‖` of the ball give.
-/

public section

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If `|⟪z, w⟫ + c| ≤ R` for every `z` in the closed ball of radius `r ≥ 0` about `0`, then
`r ‖w‖ ≤ R`. -/
theorem mul_norm_le_of_abs_inner_add_le {w : E} {c r R : ℝ} (hr : 0 ≤ r)
    (h : ∀ z ∈ Metric.closedBall (0 : E) r, |inner ℝ z w + c| ≤ R) :
    r * ‖w‖ ≤ R := by
  have h0 := h 0 (Metric.mem_closedBall_self hr)
  by_cases hw : w = 0
  · rw [hw, norm_zero, mul_zero]
    exact (abs_nonneg _).trans h0
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  set z := (r / ‖w‖) • w
  have hz : z ∈ Metric.closedBall (0 : E) r := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ hw'.ne']
  have hzw : inner ℝ z w = r * ‖w‖ := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have h₁ := h z hz
  have h₂ := h (-z) (by rwa [Metric.mem_closedBall, dist_zero_right, norm_neg,
    ← dist_zero_right])
  rw [hzw] at h₁
  rw [inner_neg_left, hzw] at h₂
  linarith [(abs_le.1 h₁).2, (abs_le.1 h₂).1]

end SymplecticGeometry

end
