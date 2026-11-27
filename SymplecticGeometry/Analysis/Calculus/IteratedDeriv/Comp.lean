/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import TauCeti.Analysis.Calculus.Deriv.Second

/-!
# Iterated derivatives of `x ↦ f (x / c)`

`iteratedDeriv_comp_div_const`: the `n`-th iterated derivative of `x ↦ f (x / c)` is
`x ↦ c⁻¹ ^ n • iteratedDeriv n f (x / c)`, for every `f`, differentiable or not. It is the case
`c⁻¹` of Tau Ceti's `TauCeti.iteratedDeriv_comp_mul_left`; Mathlib's
`iteratedDeriv_comp_const_mul` asks `f` to be `Cⁿ`.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]

/-- The `n`-th iterated derivative of `x ↦ f (x / c)` is `x ↦ c⁻¹ ^ n • iteratedDeriv n f (x / c)`,
with no differentiability assumption on `f`. -/
theorem iteratedDeriv_comp_div_const (n : ℕ) (c : 𝕜) (f : 𝕜 → F) :
    iteratedDeriv n (fun x ↦ f (x / c)) = fun x ↦ c⁻¹ ^ n • iteratedDeriv n f (x / c) := by
  simpa [div_eq_inv_mul] using TauCeti.iteratedDeriv_comp_mul_left n c⁻¹ f

end
