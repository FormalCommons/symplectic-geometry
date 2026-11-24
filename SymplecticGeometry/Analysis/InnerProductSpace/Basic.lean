/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import TauCeti.Analysis.Normed.Module.Dual.Basic

/-!
# Inner products on balls

Facts about real inner product spaces that complement Mathlib's
`Mathlib.Analysis.InnerProductSpace.Basic`.

* `mul_norm_le_of_abs_inner_add_le`: if the affine function `z ↦ ⟪z, w⟫ + c` is bounded in
  absolute value by `R` on the closed ball of radius `r ≥ 0` about `0`, then `r ‖w‖ ≤ R`.
  It follows from Tau Ceti's `StrongDual.re_apply_add_mul_norm_le_iff`, applied to the
  functionals `⟪·, w⟫` and `⟪·, -w⟫`, whose norms are `‖w‖`.
-/

public section

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If `|⟪z, w⟫ + c| ≤ R` for every `z` in the closed ball of radius `r ≥ 0` about `0`, then
`r ‖w‖ ≤ R`. -/
theorem mul_norm_le_of_abs_inner_add_le {w : E} {c r R : ℝ} (hr : 0 ≤ r)
    (h : ∀ z ∈ Metric.closedBall (0 : E) r, |inner ℝ z w + c| ≤ R) :
    r * ‖w‖ ≤ R := by
  have h1 := (StrongDual.re_apply_add_mul_norm_le_iff (𝕜 := ℝ) (f := innerSL ℝ w) (x := 0)
    (u := R - c) hr).2 fun y hy ↦ by
      simpa [real_inner_comm] using
        (by linarith [(abs_le.1 (h y hy)).2] : inner ℝ y w ≤ R - c)
  have h2 := (StrongDual.re_apply_add_mul_norm_le_iff (𝕜 := ℝ) (f := innerSL ℝ (-w)) (x := 0)
    (u := R + c) hr).2 fun y hy ↦ by
      simpa [real_inner_comm, inner_neg_right] using
        (by linarith [(abs_le.1 (h y hy)).1] : -inner ℝ y w ≤ R + c)
  simp at h1 h2
  linarith

end SymplecticGeometry

end
