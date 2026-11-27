/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# An inequality for the real inner product of `ℂ`

For complex numbers `p`, `a`, `b`, the quantity
`‖p‖² (‖a‖² + ‖b‖²) - 2 (⟪p, a⟫² + ⟪p, b⟫²)` is `-Re ((a² + b²) p̄²)`, so it is at most
`‖p‖² ‖a² + b²‖` (`Complex.norm_sq_mul_add_sub_inner_sq_le`). Here `⟪·, ·⟫` is the inner product
of `ℂ` as a real inner product space.
-/

public section

namespace Complex

/-- For complex numbers `p`, `a`, `b`,
`‖p‖² (‖a‖² + ‖b‖²) - 2 (⟪p, a⟫² + ⟪p, b⟫²) ≤ ‖p‖² ‖a² + b²‖`, for the real inner product of
`ℂ`: the left side is `-Re ((a² + b²) p̄²)`. -/
theorem norm_sq_mul_add_sub_inner_sq_le (p a b : ℂ) :
    ‖p‖ ^ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) - 2 * (inner ℝ p a ^ 2 + inner ℝ p b ^ 2) ≤
      ‖p‖ ^ 2 * ‖a ^ 2 + b ^ 2‖ := by
  have h : ‖p‖ ^ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) - 2 * (inner ℝ p a ^ 2 + inner ℝ p b ^ 2) =
      -((a ^ 2 + b ^ 2) * (starRingEnd ℂ p) ^ 2).re := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.inner, sq]
    simp
    ring
  rw [h, ← Complex.neg_re]
  calc (-((a ^ 2 + b ^ 2) * (starRingEnd ℂ p) ^ 2)).re
      ≤ ‖-((a ^ 2 + b ^ 2) * (starRingEnd ℂ p) ^ 2)‖ := Complex.re_le_norm _
    _ = ‖p‖ ^ 2 * ‖a ^ 2 + b ^ 2‖ := by simp [mul_comm]

end Complex

end
