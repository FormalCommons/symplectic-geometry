/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Interval integrals of monotone functions

## Main results

* `MonotoneOn.intervalIntegral_le_sub_mul`: for `a ≤ b` and `f` monotone on `[a, b]`, the
  integral of `f` over `[a, b]` is at most `(b - a) * f b`. Such an `f` is interval integrable
  (Mathlib's `MonotoneOn.intervalIntegrable`), so this is the monotonicity of the integral,
  `intervalIntegral.integral_mono_on`, against the constant `f b`.
-/

public section

open Set

/-- If `a ≤ b` and `f` is monotone on `[a, b]`, then `∫ x in a..b, f x ≤ (b - a) * f b`. -/
theorem MonotoneOn.intervalIntegral_le_sub_mul {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b)) : ∫ x in a..b, f x ≤ (b - a) * f b := by
  calc ∫ x in a..b, f x ≤ ∫ _ in a..b, f b :=
        intervalIntegral.integral_mono_on hab
          ((uIcc_of_le hab).symm ▸ hf).intervalIntegrable intervalIntegrable_const
          fun x hx ↦ hf hx (right_mem_Icc.2 hab) hx.2
    _ = (b - a) * f b := by rw [intervalIntegral.integral_const, smul_eq_mul]

end
