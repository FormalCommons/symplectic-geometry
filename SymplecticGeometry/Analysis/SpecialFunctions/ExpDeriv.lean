/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Iterated derivatives of the real exponential

Mathlib states that every iterate of `deriv` fixes `Real.exp` (`Real.iter_deriv_exp`). This file
gives the same fact for `iteratedDeriv`.

## Main declarations

* `Real.iteratedDeriv_exp`: `iteratedDeriv n Real.exp = Real.exp` for every `n`.
-/

public section

/-- Every iterated derivative of the real exponential is the exponential itself. -/
@[simp]
theorem Real.iteratedDeriv_exp (n : ℕ) : iteratedDeriv n Real.exp = Real.exp := by
  simp [iteratedDeriv_eq_iterate]

end
