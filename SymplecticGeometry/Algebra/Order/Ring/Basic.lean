/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two inequalities in linearly ordered rings

Supplements to `Mathlib.Algebra.Order.Ring.Defs`.

* `SymplecticGeometry.min_zero_mul_le_mul`: if `0 ≤ b ≤ c`, then `a * b` is bounded below
  by `min a 0 * c`, the negative part of `a` times the upper bound `c`. It bounds a term `a * b`
  whose coefficient `a` may have either sign, when only an upper bound for `b ≥ 0` is known.
* `SymplecticGeometry.mul_pow_three_add_mul_pow_three_sub_pow_three_le`: for `0 ≤ w ≤ 1` and
  `x, y ≥ 0`, the cube of `w x + (1 - w) y` falls short of `w x³ + (1 - w) y³` by at most
  `2 w (1 - w) (x - y)² (x + y)`.
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

/-- The cube of a convex combination of two nonnegative numbers falls short of the combination of
their cubes by at most `2 w (1 - w) (x - y)² (x + y)`. -/
theorem mul_pow_three_add_mul_pow_three_sub_pow_three_le {α : Type*} [CommRing α]
    [LinearOrder α] [IsStrictOrderedRing α] {w x y : α} (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    w * x ^ 3 + (1 - w) * y ^ 3 - (w * x + (1 - w) * y) ^ 3 ≤
      2 * (w * (1 - w)) * ((x - y) ^ 2 * (x + y)) := by
  have e : w * x ^ 3 + (1 - w) * y ^ 3 - (w * x + (1 - w) * y) ^ 3 =
      w * (1 - w) * (x - y) ^ 2 * ((1 + w) * x + (2 - w) * y) := by ring
  rw [e]
  have h₃ : (1 + w) * x + (2 - w) * y ≤ 2 * (x + y) := by nlinarith
  have : 0 ≤ w * (1 - w) * (x - y) ^ 2 := by
    have := sub_nonneg.2 hw₁
    positivity
  nlinarith [mul_le_mul_of_nonneg_left h₃ this]

end SymplecticGeometry

end
