/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Elementary estimates for integral curves

This file adds facts about Mathlib's integral curves `IsIntegralCurveOn γ v s` of a
time-dependent vector field `v : ℝ → E → E` on a real normed space.

## Main results

* `IsIntegralCurveOn.norm_sub_le_mul`: an integral curve on `[a, b]` along which the field has
  norm at most `C` moves by at most `C (b - a)`. It is the mean value inequality
  `norm_image_sub_le_of_norm_deriv_le_segment'`.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An integral curve of `v` on `[a, b]`, along which `v` has norm at most `C` at the times of
`[a, b)`, satisfies `‖γ b - γ a‖ ≤ C * (b - a)`. -/
theorem IsIntegralCurveOn.norm_sub_le_mul {γ : ℝ → E} {v : ℝ → E → E} {a b C : ℝ}
    (hγ : IsIntegralCurveOn γ v (Set.Icc a b)) (hC : ∀ t ∈ Set.Ico a b, ‖v t (γ t)‖ ≤ C)
    (hab : a ≤ b) : ‖γ b - γ a‖ ≤ C * (b - a) :=
  norm_image_sub_le_of_norm_deriv_le_segment' hγ hC b ⟨hab, le_rfl⟩

end
