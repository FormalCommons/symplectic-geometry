/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Lower bounds for the sup norm on a finite product

Mathlib bounds the sup norm of a finite product from above by its coordinates
(`pi_norm_le_iff_of_nonneg`). This file adds a lower bound in the same spirit: if each coordinate
of `b` has norm at least `min ‖a i‖ c`, then `‖b‖ ≥ min ‖a‖ c`
(`min_norm_le_pi_norm_of_forall`).
-/

public section

/-- A coordinatewise lower bound `min ‖a i‖ c ≤ ‖b i‖` gives the same lower bound
`min ‖a‖ c ≤ ‖b‖` for the sup norms. -/
theorem min_norm_le_pi_norm_of_forall {ι : Type*} [Fintype ι] {E F : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] [∀ i, SeminormedAddGroup (F i)] {a : ∀ i, E i}
    {b : ∀ i, F i} {c : ℝ} (h : ∀ i, min ‖a i‖ c ≤ ‖b i‖) : min ‖a‖ c ≤ ‖b‖ := by
  by_contra! hb
  -- Every coordinate of `b` is below `c`, so it bounds that of `a`, and then `‖a‖ ≤ ‖b‖`.
  have : ‖a‖ ≤ ‖b‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg b)).2 fun i ↦ by
    have hi := (norm_le_pi_norm b i).trans_lt (hb.trans_le (min_le_right _ _))
    have := h i
    rw [min_le_iff] at this
    rcases this with h' | h'
    · exact h'.trans (norm_le_pi_norm b i)
    · exact absurd hi h'.not_gt
  exact this.not_gt (hb.trans_le (min_le_left _ _))

end
