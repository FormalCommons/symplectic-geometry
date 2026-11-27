/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The derivative of the rescaling `x ↦ c f (x / c)`

`deriv_const_mul_comp_div_const`: for `c ≠ 0`, the rescaling `x ↦ c f (x / c)` of a function
`f : 𝕜 → 𝕜` has at `x` the derivative of `f` at `x / c`, for every `f`, differentiable or not.
It follows from Mathlib's `deriv_comp_mul_left` and `deriv_const_mul_field`.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The derivative at `x` of the rescaling `x ↦ c f (x / c)` of `f` by `c ≠ 0` is the derivative
of `f` at `x / c`, with no differentiability assumption on `f`. -/
theorem deriv_const_mul_comp_div_const {c : 𝕜} (hc : c ≠ 0) (f : 𝕜 → 𝕜) (x : 𝕜) :
    deriv (fun x ↦ c * f (x / c)) x = deriv f (x / c) := by
  simp only [div_eq_inv_mul]
  rw [deriv_const_mul_field, deriv_comp_mul_left, smul_eq_mul, mul_inv_cancel_left₀ hc]

end
