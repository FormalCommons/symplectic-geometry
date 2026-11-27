/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# The second iterated derivative

The second iterated derivative of a function of one variable is the derivative of its
derivative (`iteratedDeriv_two`), the case `n = 2` next to Mathlib's `iteratedDeriv_one`.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {f : 𝕜 → F}

/-- The second iterated derivative of `f` is the derivative of the derivative of `f`. -/
theorem iteratedDeriv_two : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

end
