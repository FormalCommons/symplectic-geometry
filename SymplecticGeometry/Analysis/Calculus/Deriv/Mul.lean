/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Convex combinations of functions with positive derivative

* `deriv_mul_add_one_sub_mul_pos`: a combination `c * f + (1 - c) * g` with `c ∈ [0, 1]` of two
  real functions with positive derivative at `x` has positive derivative at `x`. The derivative
  is computed by Mathlib's `deriv_const_mul`; the differentiability of `f` and `g` at `x` follows
  from their derivatives being nonzero (`differentiableAt_of_deriv_ne_zero`).
-/

public section

/-- A combination `c * f + (1 - c) * g`, with `0 ≤ c ≤ 1`, of two real functions with positive
derivatives at `x` has positive derivative at `x`. -/
theorem deriv_mul_add_one_sub_mul_pos {f g : ℝ → ℝ} {x c : ℝ} (hf : 0 < deriv f x)
    (hg : 0 < deriv g x) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    0 < deriv (fun y ↦ c * f y + (1 - c) * g y) x := by
  have hfd := differentiableAt_of_deriv_ne_zero hf.ne'
  have hgd := differentiableAt_of_deriv_ne_zero hg.ne'
  rw [deriv_fun_add (hfd.const_mul c) (hgd.const_mul (1 - c)), deriv_const_mul _ hfd,
    deriv_const_mul _ hgd]
  rcases hc₀.eq_or_lt with rfl | hc₀
  · simpa using hg
  · nlinarith

end
