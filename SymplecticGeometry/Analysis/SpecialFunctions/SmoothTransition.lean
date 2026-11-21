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
`(0, ∞)`.
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

end Real.smoothTransition

end
