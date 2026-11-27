/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The Cauchy–Schwarz inequality with square roots

For a symmetric bilinear form `B` on a real vector space with `0 ≤ B v v` for all `v`, Mathlib's
`LinearMap.BilinForm.apply_sq_le_of_symm` states the Cauchy–Schwarz inequality in squared form,
`B v w ^ 2 ≤ B v v * B w w`. Taking square roots gives the form
`|B v w| ≤ √(B v v) * √(B w w)` of `LinearMap.BilinForm.abs_apply_le_sqrt_mul_sqrt`, which for an
inner product is `abs_real_inner_le_norm`.
-/

public section

namespace LinearMap.BilinForm

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {B : LinearMap.BilinForm ℝ M}

/-- **The Cauchy–Schwarz inequality** for a symmetric nonnegative real bilinear form `B`:
`|B v w| ≤ √(B v v) * √(B w w)`. -/
theorem abs_apply_le_sqrt_mul_sqrt (hBs : B.IsSymm) (hpos : B.IsNonneg) (v w : M) :
    |B v w| ≤ √(B v v) * √(B w w) := by
  rw [← Real.sqrt_mul (hpos.nonneg v)]
  exact Real.abs_le_sqrt (B.apply_sq_le_of_symm hpos.nonneg (isSymm_iff.1 hBs) v w)

end LinearMap.BilinForm

end
