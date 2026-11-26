/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs

/-!
# A lower bound by the negative part in a linearly ordered ring

A supplement to `Mathlib.Algebra.Order.Ring.Defs`: if `0 ≤ b ≤ c`, then `a * b` is bounded below
by `min a 0 * c`, the negative part of `a` times the upper bound `c`
(`min_zero_mul_le_mul`). It bounds a term `a * b` whose coefficient `a` may have either sign,
when only an upper bound for `b ≥ 0` is known.
-/

public section

namespace SymplecticGeometry

/-- If `0 ≤ b ≤ c`, then `min a 0 * c ≤ a * b`. -/
theorem min_zero_mul_le_mul {α : Type*} [Ring α] [LinearOrder α] [IsOrderedRing α] {a b c : α}
    (hb : 0 ≤ b) (hbc : b ≤ c) : min a 0 * c ≤ a * b := by
  rcases le_total 0 a with ha | ha
  · rw [min_eq_right ha, zero_mul]
    exact mul_nonneg ha hb
  · rw [min_eq_left ha]
    exact mul_le_mul_of_nonpos_left hbc ha

end SymplecticGeometry

end
