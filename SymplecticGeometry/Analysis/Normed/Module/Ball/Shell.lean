/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Closed shells around a sphere

In a proper real normed space, every open set `V` that contains the sphere of radius `r > 0`
about the origin contains a closed shell `{y | |‖y‖ - r| ≤ w}` for some `0 < w < r`
(`Metric.exists_abs_norm_sub_le_subset_of_sphere_subset`). The sphere is compact, so `V`
contains one of its thickenings (`IsCompact.exists_thickening_subset_open`), and a point `y ≠ 0`
is at distance `|‖y‖ - r|` from the point `(r / ‖y‖) • y` of the sphere. In a proper normed
group such a shell is compact (`Metric.isCompact_setOfPred_abs_norm_sub_le`): it is closed and lies
in a closed ball.
-/

public section

open Set

namespace Metric

variable {E : Type*} [NormedAddCommGroup E]

/-- In a proper normed group, the closed shell `{y | |‖y‖ - r| ≤ w}` is compact. -/
theorem isCompact_setOfPred_abs_norm_sub_le [ProperSpace E] (r w : ℝ) :
    IsCompact {y : E | |‖y‖ - r| ≤ w} := by
  refine (isCompact_closedBall (0 : E) (r + w)).of_isClosed_subset
    (isClosed_le (by fun_prop) continuous_const) fun y hy ↦ ?_
  rw [mem_closedBall_zero_iff]
  rw [mem_ofPred_eq, abs_le] at hy
  linarith [hy.2]

variable [NormedSpace ℝ E]

/-- A nonzero vector `y` is at distance `|‖y‖ - r|` from `(r / ‖y‖) • y`. For `r > 0` this is the
point of the sphere of radius `r` on the ray through `y`. -/
theorem dist_div_norm_smul_self {y : E} (hy : y ≠ 0) (r : ℝ) :
    dist y ((r / ‖y‖) • y) = |‖y‖ - r| := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have : y - (r / ‖y‖) • y = (1 - r / ‖y‖) • y := by rw [sub_smul, one_smul]
  rw [dist_eq_norm, this, norm_smul, Real.norm_eq_abs, ← abs_of_pos hn, ← abs_mul, abs_of_pos hn]
  congr 1
  field_simp

variable [ProperSpace E]

/-- In a proper real normed space, an open set containing the sphere of radius `r > 0` about the
origin contains a closed shell `{y | |‖y‖ - r| ≤ w}` around it, for some `0 < w < r`. -/
theorem exists_abs_norm_sub_le_subset_of_sphere_subset {r : ℝ} (hr : 0 < r) {V : Set E}
    (hV : IsOpen V) (hS : sphere (0 : E) r ⊆ V) :
    ∃ w, 0 < w ∧ w < r ∧ {y : E | |‖y‖ - r| ≤ w} ⊆ V := by
  obtain ⟨δ, hδ, hδV⟩ := (isCompact_sphere (0 : E) r).exists_thickening_subset_open hV hS
  have hmin := min_le_left δ r
  have hmin' := min_le_right δ r
  refine ⟨min δ r / 2, by positivity, by linarith, fun y (hy : |‖y‖ - r| ≤ min δ r / 2) ↦ ?_⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [norm_zero, zero_sub, abs_neg, abs_of_pos hr] at hy
    linarith
  refine hδV (mem_thickening_iff.2 ⟨(r / ‖y‖) • y, ?_, ?_⟩)
  · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_div, abs_norm, abs_of_pos hr,
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hy0)]
  · rw [dist_div_norm_smul_self hy0 r]
    linarith

end Metric

end
