/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.NatCast

/-!
# Order of numerals in an `AddMonoidWithOne`

A supplement to `Mathlib.Algebra.Order.Monoid.NatCast`: in an `AddMonoidWithOne` in which adding
on the right is monotone, `1 ≤ a` gives `2 ≤ a + 1` (`two_le_add_one_of_one_le`). Smoothness
indices in `ℕ∞ω` use it to pass from a `C^n` hypothesis with `1 ≤ n` to a `C^2` one for a map of
class `C^(n+1)`.
-/

public section

namespace SymplecticGeometry

variable {α : Type*} [AddMonoidWithOne α] [LE α] [AddRightMono α]

/-- If `1 ≤ a`, then `2 ≤ a + 1`. -/
theorem two_le_add_one_of_one_le {a : α} (h : 1 ≤ a) : (2 : α) ≤ a + 1 := by
  rw [← one_add_one_eq_two]
  exact add_le_add_left h 1

end SymplecticGeometry

end
