/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Bounds for the square root of a sum of squares

A real number `x` is at most `√(x ^ 2 + y ^ 2)`, and strictly less for `y ≠ 0`. The radius
`√(l ^ 2 + ε ^ 2)` of the ball removed in the blowup of weight `l` is of this form.
-/

public section

namespace Real

/-- A real number is at most the square root of the sum of its square and another square. -/
theorem le_sqrt_sq_add_sq (x y : ℝ) : x ≤ √(x ^ 2 + y ^ 2) :=
  le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg y))

/-- A real number is less than the square root of the sum of its square and a nonzero square. -/
theorem lt_sqrt_sq_add_sq (x : ℝ) {y : ℝ} (hy : y ≠ 0) : x < √(x ^ 2 + y ^ 2) :=
  lt_sqrt_of_sq_lt (lt_add_of_pos_right _ (sq_pos_of_ne_zero hy))

end Real

end
