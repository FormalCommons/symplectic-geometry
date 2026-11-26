/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith

/-!
# An upper bound for `(1 + t) ^ n` on `[0, 1]`

A companion to Bernoulli's inequality `one_add_mul_le_pow` of `Mathlib.Algebra.Order.Ring.Pow`,
which bounds `(1 + t) ^ n` from below: for `0 ≤ t ≤ 1`, convexity of `t ↦ (1 + t) ^ n` gives
`(1 + t) ^ n ≤ 1 + (2 ^ n - 1) * t` (`one_add_pow_le_one_add_two_pow_sub_one_mul`), the chord
between `t = 0` and `t = 1`.
-/

public section

namespace SymplecticGeometry

/-- For `0 ≤ t ≤ 1`, `(1 + t) ^ n ≤ 1 + (2 ^ n - 1) * t`: on `[0, 1]` the graph of the convex
function `t ↦ (1 + t) ^ n` lies below its chord. -/
theorem one_add_pow_le_one_add_two_pow_sub_one_mul {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {t : R} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (n : ℕ) :
    (1 + t) ^ n ≤ 1 + (2 ^ n - 1) * t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : (1 : R) ≤ 2 ^ n := one_le_pow₀ one_le_two
    rw [pow_succ, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right ih (by linarith : (0 : R) ≤ 1 + t),
      mul_le_mul_of_nonneg_left ht₁ (by nlinarith : (0 : R) ≤ (2 ^ n - 1) * t)]

end SymplecticGeometry

end
