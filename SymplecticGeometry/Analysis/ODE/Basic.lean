/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Elementary estimates for integral curves

This file adds facts about Mathlib's integral curves `IsIntegralCurveOn γ v s` of a
time-dependent vector field `v : ℝ → E → E` on a real normed space.

## Main results

* `IsIntegralCurveOn.norm_sub_le_mul`: an integral curve on `[a, b]` along which the field has
  norm at most `C` moves by at most `C (b - a)`. It is the mean value inequality
  `norm_image_sub_le_of_norm_deriv_le_segment'`.
* `IsIntegralCurveOn.map_eq_of_map_eq_zero`: if a continuous linear map `L` kills the field along
  an integral curve on `[a, b]`, then `L ∘ γ` takes the same value at `a` and `b`. For the
  quotient map `E → E ⧸ ℝ ∙ e`, this says that a curve whose velocity is everywhere a multiple
  of `e` stays on the line through its starting point in the direction `e`.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An integral curve of `v` on `[a, b]`, along which `v` has norm at most `C` at the times of
`[a, b)`, satisfies `‖γ b - γ a‖ ≤ C * (b - a)`. -/
theorem IsIntegralCurveOn.norm_sub_le_mul {γ : ℝ → E} {v : ℝ → E → E} {a b C : ℝ}
    (hγ : IsIntegralCurveOn γ v (Set.Icc a b)) (hC : ∀ t ∈ Set.Ico a b, ‖v t (γ t)‖ ≤ C)
    (hab : a ≤ b) : ‖γ b - γ a‖ ≤ C * (b - a) :=
  norm_image_sub_le_of_norm_deriv_le_segment' hγ hC b ⟨hab, le_rfl⟩

/-- If `γ` is an integral curve of `v` on `[a, b]` and a continuous linear map `L` kills `v` along
`γ` at the times of `[a, b)`, then `L (γ b) = L (γ a)`. -/
theorem IsIntegralCurveOn.map_eq_of_map_eq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {γ : ℝ → E} {v : ℝ → E → E} {a b : ℝ}
    (hγ : IsIntegralCurveOn γ v (Set.Icc a b)) (L : E →L[ℝ] F)
    (hL : ∀ t ∈ Set.Ico a b, L (v t (γ t)) = 0) (hab : a ≤ b) : L (γ b) = L (γ a) := by
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t ↦ L (γ t)) (C := 0)
    (f' := fun t ↦ L (v t (γ t))) (fun t ht ↦ L.hasFDerivAt.comp_hasDerivWithinAt t (hγ t ht))
    (fun t ht ↦ by simp [hL t ht]) b ⟨hab, le_rfl⟩
  rwa [zero_mul, norm_le_zero_iff, sub_eq_zero] at this

end
