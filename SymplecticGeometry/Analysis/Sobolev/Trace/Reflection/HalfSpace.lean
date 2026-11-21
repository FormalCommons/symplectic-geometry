/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Reflection.HalfSpace

/-!
# Time dilations

Two facts about Tau Ceti's time dilations `TauCeti.HalfSpaceExtension.timeScale`: the bound
`norm_timeScale_le` on their operator norm, and `timeScale_of_fst_eq_zero`, that they fix the
points of time `0`.
-/

public section

namespace TauCeti.HalfSpaceExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The time dilation by `a` has operator norm at most `max |a| 1`. -/
theorem norm_timeScale_le (a : ℝ) : ‖timeScale (E := E) a‖ ≤ max |a| 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z ↦ ?_
  rw [timeScale_apply, Prod.norm_def, Prod.norm_def, norm_mul, Real.norm_eq_abs]
  refine max_le ?_ ?_
  · exact mul_le_mul (le_max_left _ _) (le_max_left _ _) (norm_nonneg _) (by positivity)
  · calc ‖z.2‖ = 1 * ‖z.2‖ := (one_mul _).symm
      _ ≤ _ := mul_le_mul (le_max_right _ _) (le_max_right _ _) (norm_nonneg _) (by positivity)

/-- The time dilations fix the points of time `0`. -/
theorem timeScale_of_fst_eq_zero {z : ℝ × E} (hz : z.1 = 0) (a : ℝ) :
    timeScale a z = z := by
  ext <;> simp [hz]

end TauCeti.HalfSpaceExtension

end
