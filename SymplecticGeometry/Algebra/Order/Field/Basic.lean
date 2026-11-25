/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An estimate in a linearly ordered field

A supplement to `Mathlib.Algebra.Order.Field.Basic`: for `0 < b` and nonnegative `G`, `N`,
scaling `b ^ 2 * G + N` by `min b b⁻¹` gives at most `b * (G + N)`
(`min_inv_mul_sq_mul_add_le`). Gradient-like vector fields use it to rescale their constant
when the field or the function is multiplied by a positive factor.
-/

public section

namespace SymplecticGeometry

/-- If `0 < b`, `0 ≤ G` and `0 ≤ N`, then `min b b⁻¹ * (b ^ 2 * G + N) ≤ b * (G + N)`. -/
theorem min_inv_mul_sq_mul_add_le {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {b G N : α} (hb : 0 < b) (hG : 0 ≤ G) (hN : 0 ≤ N) :
    min b b⁻¹ * (b ^ 2 * G + N) ≤ b * (G + N) := by
  have hm₁ : min b b⁻¹ * b ≤ 1 :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hb.le).trans_eq (inv_mul_cancel₀ hb.ne')
  have hm₂ : min b b⁻¹ ≤ b := min_le_left _ _
  calc min b b⁻¹ * (b ^ 2 * G + N) = min b b⁻¹ * b * (b * G) + min b b⁻¹ * N := by ring
    _ ≤ 1 * (b * G) + b * N := by gcongr
    _ = b * (G + N) := by ring

end SymplecticGeometry

end
