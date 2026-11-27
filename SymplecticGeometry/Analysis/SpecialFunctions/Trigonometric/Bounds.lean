/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# A lower bound for the sine

The sine is at least `1 / 2` on `[π / 6, 5 π / 6]`, and `sign x * sin x` is at least `1 / 2`
where `π / 6 ≤ |x| ≤ 5 π / 6`. Both follow from `Real.sin_pi_div_six` and the monotonicity of the
sine on `[-π / 2, π / 2]`.
-/

public section

open scoped Real

namespace Real

/-- The sine is at least `1 / 2` on `[π / 6, 5 π / 6]`. -/
theorem one_half_le_sin {x : ℝ} (h₁ : π / 6 ≤ x) (h₂ : x ≤ 5 * π / 6) : 1 / 2 ≤ sin x := by
  have hπ := pi_pos
  rw [← sin_pi_div_six]
  rcases le_total x (π / 2) with hx | hx
  · exact sin_le_sin_of_le_of_le_pi_div_two (by linarith) hx h₁
  · rw [← sin_pi_sub x]
    exact sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

/-- Where `π / 6 ≤ |x| ≤ 5 π / 6`, the sine has the sign of `x` and absolute value at least
`1 / 2`. -/
theorem one_half_le_sign_mul_sin {x : ℝ} (h₁ : π / 6 ≤ |x|) (h₂ : |x| ≤ 5 * π / 6) :
    1 / 2 ≤ (SignType.sign x : ℝ) * sin x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [abs_of_neg hx] at h₁ h₂
    rw [_root_.sign_neg hx, SignType.coe_neg_one, neg_one_mul, ← sin_neg]
    exact one_half_le_sin h₁ h₂
  · rw [abs_zero] at h₁
    linarith [pi_pos]
  · rw [abs_of_pos hx] at h₁ h₂
    rw [_root_.sign_pos hx, SignType.coe_one, one_mul]
    exact one_half_le_sin h₁ h₂

/-- Where `π / 6 ≤ |x| ≤ 5 π / 6`, the value `sin (x + i π) = (-1) ^ i sin x` has the sign
`(-1) ^ i sign x` and absolute value at least `1 / 2`. -/
theorem one_half_le_neg_one_pow_mul_sign_mul_sin_add_nat_mul_pi {x : ℝ} (h₁ : π / 6 ≤ |x|)
    (h₂ : |x| ≤ 5 * π / 6) (i : ℕ) :
    1 / 2 ≤ (-1) ^ i * (SignType.sign x : ℝ) * sin (x + i * π) := by
  have hsq : ((-1 : ℝ) ^ i) * (-1) ^ i = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have key : (-1 : ℝ) ^ i * (SignType.sign x : ℝ) * ((-1) ^ i * sin x) =
      (SignType.sign x : ℝ) * sin x := by
    linear_combination ((SignType.sign x : ℝ) * sin x) * hsq
  rw [sin_add_nat_mul_pi, key]
  exact one_half_le_sign_mul_sin h₁ h₂

end Real

end
