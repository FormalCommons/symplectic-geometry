/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions

/-!
# The sum of the squared norms of the components of a pair

A nonzero pair `v = (v₁, v₂)` in a product of normed groups has `0 < ‖v₁‖² + ‖v₂‖²`
(`Prod.norm_fst_sq_add_norm_snd_sq_pos`): the right side is the square of the `L²` norm of `v`,
whereas Mathlib's norm on `E × F` is the sup norm.
-/

public section

/-- A nonzero pair `v` has `0 < ‖v.1‖² + ‖v.2‖²`. -/
theorem Prod.norm_fst_sq_add_norm_snd_sq_pos {E F : Type*} [NormedAddGroup E] [NormedAddGroup F]
    {v : E × F} (hv : v ≠ 0) : 0 < ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 := by
  by_contra! h
  have h₁ : ‖v.1‖ = 0 := by nlinarith [sq_nonneg ‖v.1‖, sq_nonneg ‖v.2‖, norm_nonneg v.1]
  have h₂ : ‖v.2‖ = 0 := by nlinarith [sq_nonneg ‖v.1‖, sq_nonneg ‖v.2‖, norm_nonneg v.2]
  exact hv (Prod.ext (norm_eq_zero.1 h₁) (norm_eq_zero.1 h₂))

end
