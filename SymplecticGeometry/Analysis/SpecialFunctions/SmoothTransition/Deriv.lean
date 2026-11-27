/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# The derivative of the smooth transition function

Mathlib's `Real.smoothTransition` is `0` on `(-∞, 0]`, `1` on `[1, ∞)`, and the quotient
`f x / (f x + f (1 - x))` in between, with `f = expNegInvGlue`. Tau Ceti shows that its derivative
vanishes outside `[0, 1]`. By the quotient rule, with `τ = Real.smoothTransition`, this file
shows `τ' = τ (1 - τ) (x⁻² + (1 - x)⁻²)` (`Real.smoothTransition.deriv_eq_mul_one_sub_mul`).
Hence the derivative is positive on the open interval `(0, 1)` (`Real.smoothTransition.deriv_pos`),
and that of the rescaled transition `x ↦ τ((x - p) / (q - p))` on `(p, q)`
(`Real.smoothTransition.deriv_comp_sub_div_pos`),
and `8 τ (1 - τ) ≤ τ'`, since `x⁻² + (1 - x)⁻² ≥ 8` on `(0, 1)`
(`Real.smoothTransition.eight_mul_mul_one_sub_le_deriv`). Since `τ'` vanishes outside `[0, 1]`,
also `|x τ'(x)| ≤ τ'(x)` (`Real.smoothTransition.abs_mul_deriv_le_deriv`), and `x τ''(x)` is bounded
(`Real.smoothTransition.exists_forall_norm_mul_deriv_deriv_le`).
-/

public section

namespace Real.smoothTransition

/-- The derivative of the smooth transition function `τ` is
`τ(x) (1 - τ(x)) (x⁻² + (1 - x)⁻²)`: on `(0, 1)` this says that the derivative of the logit
`log (τ / (1 - τ))` of `τ` is `x⁻² + (1 - x)⁻²`, and outside `(0, 1)` both sides vanish. -/
theorem deriv_eq_mul_one_sub_mul (x : ℝ) :
    deriv smoothTransition x =
      smoothTransition x * (1 - smoothTransition x) * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) := by
  have hD := (pos_denom x).ne'
  have hd₂ : HasDerivAt (fun y ↦ expNegInvGlue (1 - y))
      ((1 - x)⁻¹ ^ 2 * expNegInvGlue (1 - x) * (-1)) x :=
    (expNegInvGlue.hasDerivAt (1 - x)).comp x ((hasDerivAt_id x).const_sub 1)
  have hd := (expNegInvGlue.hasDerivAt x).div ((expNegInvGlue.hasDerivAt x).add hd₂) hD
  -- `smoothTransition` is, by definition, the quotient that `hd` differentiates.
  have hτ : smoothTransition = expNegInvGlue / (expNegInvGlue + fun y ↦ expNegInvGlue (1 - y)) :=
    rfl
  rw [hτ, hd.deriv]
  simp only [Pi.div_apply, Pi.add_apply]
  -- Treat the four values as independent, so that `field_simp` clears only the denominator.
  generalize x⁻¹ = u, (1 - x)⁻¹ = v, expNegInvGlue x = a, expNegInvGlue (1 - x) = b at *
  field_simp
  ring

/-- The smooth transition function has positive derivative on the open interval `(0, 1)`. -/
theorem deriv_pos {x : ℝ} (h₀ : 0 < x) (h₁ : x < 1) : 0 < deriv smoothTransition x := by
  have := sub_pos.2 (lt_one_of_lt_one h₁)
  have := pos_of_pos h₀
  rw [deriv_eq_mul_one_sub_mul]
  positivity

/-- For `p < q`, the rescaled smooth transition `x ↦ smoothTransition ((x - p) / (q - p))`, which
is `0` on `(-∞, p]` and `1` on `[q, ∞)`, has positive derivative on `(p, q)`. -/
theorem deriv_comp_sub_div_pos {p q x : ℝ} (hx : x ∈ Set.Ioo p q) :
    0 < deriv (fun y ↦ smoothTransition ((y - p) / (q - p))) x := by
  have hpq : 0 < q - p := sub_pos.2 (hx.1.trans hx.2)
  rw [(((hasDerivAt_id' x).sub_const p).div_const (q - p)).smoothTransition.deriv]
  refine mul_pos (deriv_pos (div_pos (sub_pos.2 hx.1) hpq) ?_) (div_pos one_pos hpq)
  exact (div_lt_one hpq).2 (by linarith [hx.2])

/-- The derivative of the smooth transition function `τ` is at least `8 τ (1 - τ)`, since
`x⁻² + (1 - x)⁻² ≥ 8` on `(0, 1)` and `τ (1 - τ)` vanishes outside it. -/
theorem eight_mul_mul_one_sub_le_deriv (x : ℝ) :
    8 * (smoothTransition x * (1 - smoothTransition x)) ≤ deriv smoothTransition x := by
  rw [deriv_eq_mul_one_sub_mul]
  rcases le_or_gt x 0 with hx | hx
  · simp [zero_of_nonpos hx]
  rcases le_or_gt 1 x with hx' | hx'
  · simp [one_of_one_le hx']
  have hp : 0 < x * (1 - x) := mul_pos hx (sub_pos.2 hx')
  have hp' : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * x - 1)]
  have h8 : 8 ≤ x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2 := by
    have : x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2 - 8 =
        (1 - 4 * (x * (1 - x))) * (1 + 2 * (x * (1 - x))) / (x * (1 - x)) ^ 2 := by
      field_simp [hx.ne', (sub_pos.2 hx').ne']
      ring
    have : 0 ≤ x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2 - 8 := by
      rw [this]
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
    linarith
  rw [mul_comm 8]
  exact mul_le_mul_of_nonneg_left h8
    (mul_nonneg (smoothTransition.nonneg x) (sub_nonneg.2 (smoothTransition.le_one x)))

/-- The product `x τ'(x)` of the argument and the derivative of the smooth transition function
`τ` is at most `τ'(x)` in absolute value, since `τ'` vanishes outside `[0, 1]`. -/
theorem abs_mul_deriv_le_deriv (x : ℝ) :
    |x * deriv smoothTransition x| ≤ deriv smoothTransition x := by
  rw [abs_of_nonneg (mul_deriv_nonneg x)]
  exact mul_deriv_le_deriv x

/-- The product `x τ''(x)` of the argument and the second derivative of the smooth transition
function `τ` is bounded, since `τ''` is continuous with compact support. -/
theorem exists_forall_norm_mul_deriv_deriv_le :
    ∃ M : ℝ, ∀ x, ‖x * deriv (deriv smoothTransition) x‖ ≤ M :=
  (continuous_id.mul (smoothTransition.contDiff.iterate_deriv 2).continuous
    ).bounded_above_of_compact_support hasCompactSupport_deriv.deriv.mul_left

end Real.smoothTransition

end
