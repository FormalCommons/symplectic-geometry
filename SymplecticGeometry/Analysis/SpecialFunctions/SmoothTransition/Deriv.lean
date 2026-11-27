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
vanishes outside `[0, 1]`. This file shows that the derivative is positive on the open interval
`(0, 1)` (`Real.smoothTransition.deriv_pos`): by the quotient rule it is
`(f' x f (1 - x) + f x f' (1 - x)) / (f x + f (1 - x)) ^ 2`, and `f` and `f'` are positive on
`(0, ∞)`. Since the derivative `τ'` vanishes outside `[0, 1]`, also `|x τ'(x)| ≤ τ'(x)`
(`Real.smoothTransition.abs_mul_deriv_le_deriv`), and `x τ''(x)` is bounded
(`Real.smoothTransition.exists_forall_norm_mul_deriv_deriv_le`).
For `a > 0`, the points where `Real.smoothTransition` takes values in `[a, 1 - a]` form a
compact subset of `(0, 1)`, so the derivative has a positive lower bound on them
(`Real.smoothTransition.exists_pos_le_deriv`).
-/

public section

namespace Real.smoothTransition

/-- The smooth transition function has positive derivative on the open interval `(0, 1)`. -/
theorem deriv_pos {x : ℝ} (h₀ : 0 < x) (h₁ : x < 1) : 0 < deriv smoothTransition x := by
  set f := expNegInvGlue
  have hx : 0 < f x := expNegInvGlue.pos_of_pos h₀
  have hy : 0 < f (1 - x) := expNegInvGlue.pos_of_pos (sub_pos.2 h₁)
  have hd₁ := expNegInvGlue.hasDerivAt x
  have hd₂ : HasDerivAt (fun y ↦ f (1 - y)) ((1 - x)⁻¹ ^ 2 * f (1 - x) * (-1)) x :=
    (expNegInvGlue.hasDerivAt (1 - x)).comp x ((hasDerivAt_id x).const_sub 1)
  have hd := hd₁.div (hd₁.add hd₂) (pos_denom x).ne'
  -- `smoothTransition` is, by definition, the quotient that `hd` differentiates.
  rw [show smoothTransition = f / (f + fun y ↦ f (1 - y)) from rfl, hd.deriv, Pi.add_apply]
  refine div_pos ?_ (pow_pos (pos_denom x) 2)
  have key : x⁻¹ ^ 2 * f x * (f x + f (1 - x)) -
      f x * (x⁻¹ ^ 2 * f x + (1 - x)⁻¹ ^ 2 * f (1 - x) * (-1)) =
      x⁻¹ ^ 2 * f x * f (1 - x) + f x * ((1 - x)⁻¹ ^ 2 * f (1 - x)) := by ring
  rw [key]
  positivity

/-- For `a > 0`, the derivative of the smooth transition function has a positive lower bound on
the set of points where its value lies in `[a, 1 - a]`. -/
theorem exists_pos_le_deriv {a : ℝ} (ha : 0 < a) :
    ∃ c > 0, ∀ u, smoothTransition u ∈ Set.Icc a (1 - a) → c ≤ deriv smoothTransition u := by
  -- Such points lie in `(0, 1)`, where the derivative is positive, and form a compact set.
  have hmem {u : ℝ} (hu : smoothTransition u ∈ Set.Icc a (1 - a)) : 0 < u ∧ u < 1 := by
    refine ⟨lt_of_not_ge fun h ↦ ?_, lt_of_not_ge fun h ↦ ?_⟩
    · linarith [hu.1, zero_of_nonpos h]
    · linarith [hu.2, one_of_one_le h]
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ∩ smoothTransition ⁻¹' Set.Icc a (1 - a)) :=
    isCompact_Icc.inter_right (isClosed_Icc.preimage smoothTransition.continuous)
  obtain ⟨c, hc, hcK⟩ := hK.exists_forall_le' differentiable_deriv.continuous.continuousOn
    fun u hu ↦ deriv_pos (hmem hu.2).1 (hmem hu.2).2
  exact ⟨c, hc, fun u hu ↦ hcK u ⟨⟨(hmem hu).1.le, (hmem hu).2.le⟩, hu⟩⟩

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
