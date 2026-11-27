/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Inequalities in linearly ordered rings

Supplements to `Mathlib.Algebra.Order.Ring.Defs`.

* `SymplecticGeometry.min_zero_mul_le_mul`: if `0 ≤ b ≤ c`, then `a * b` is bounded below
  by `min a 0 * c`, the negative part of `a` times the upper bound `c`. It bounds a term `a * b`
  whose coefficient `a` may have either sign, when only an upper bound for `b ≥ 0` is known.
* `SymplecticGeometry.abs_mul_pow_three_add_mul_pow_three_sub_pow_three_le`: for `0 ≤ w ≤ 1`,
  the cube of `w x + (1 - w) y` differs from `w x³ + (1 - w) y³` by at most
  `2 w (1 - w) (x - y)² (|x| + |y|)`.
* `SymplecticGeometry.mul_pow_three_add_mul_pow_three_sub_pow_three_le`: its case `x, y ≥ 0`,
  where the cube falls short by at most `2 w (1 - w) (x - y)² (x + y)`.
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

/-- The cube of a convex combination of two numbers of any sign differs from the combination of
their cubes by at most `2 w (1 - w) (x - y)² (|x| + |y|)`. -/
theorem abs_mul_pow_three_add_mul_pow_three_sub_pow_three_le {α : Type*} [CommRing α]
    [LinearOrder α] [IsStrictOrderedRing α] {w x y : α} (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
    |w * x ^ 3 + (1 - w) * y ^ 3 - (w * x + (1 - w) * y) ^ 3| ≤
      2 * (w * (1 - w)) * ((x - y) ^ 2 * (|x| + |y|)) := by
  have e : w * x ^ 3 + (1 - w) * y ^ 3 - (w * x + (1 - w) * y) ^ 3 =
      w * (1 - w) * (x - y) ^ 2 * ((1 + w) * x + (2 - w) * y) := by ring
  have h₀ : 0 ≤ w * (1 - w) * (x - y) ^ 2 := by
    have := sub_nonneg.2 hw₁
    positivity
  rw [e, abs_mul, abs_of_nonneg h₀]
  have h₃ : |(1 + w) * x + (2 - w) * y| ≤ 2 * (|x| + |y|) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : α) ≤ 1 + w),
      abs_of_nonneg (by linarith : (0 : α) ≤ 2 - w)]
    nlinarith [abs_nonneg x, abs_nonneg y]
  nlinarith [mul_le_mul_of_nonneg_left h₃ h₀]

/-- The cube of a convex combination of two nonnegative numbers falls short of the combination of
their cubes by at most `2 w (1 - w) (x - y)² (x + y)`. -/
theorem mul_pow_three_add_mul_pow_three_sub_pow_three_le {α : Type*} [CommRing α]
    [LinearOrder α] [IsStrictOrderedRing α] {w x y : α} (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    w * x ^ 3 + (1 - w) * y ^ 3 - (w * x + (1 - w) * y) ^ 3 ≤
      2 * (w * (1 - w)) * ((x - y) ^ 2 * (x + y)) := by
  simpa [abs_of_nonneg hx, abs_of_nonneg hy] using
    (le_abs_self _).trans
      (abs_mul_pow_three_add_mul_pow_three_sub_pow_three_le (x := x) (y := y) hw₀ hw₁)

end SymplecticGeometry

end
