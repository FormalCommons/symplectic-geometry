/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Sequences that grow by at least one at each step

A sequence `f : ℕ → ℝ` with `f k + 1 ≤ f (k + 1)` for every `k` grows at least linearly,
`f 0 + k ≤ f k` (`add_natCast_le_of_add_one_le`), and so tends to `+∞`
(`tendsto_atTop_of_add_one_le`). This is how the cut parameters and the levels of a ray grown in
stages are shown to go to infinity.
-/

public section

open Filter

/-- A sequence of reals that grows by at least one at each step grows at least linearly. -/
theorem add_natCast_le_of_add_one_le {f : ℕ → ℝ} (hf : ∀ k, f k + 1 ≤ f (k + 1)) (k : ℕ) :
    f 0 + k ≤ f k := by
  induction k with
  | zero => simp
  | succ k ih => push_cast; linarith [hf k]

/-- A sequence of reals that grows by at least one at each step tends to `+∞`. -/
theorem tendsto_atTop_of_add_one_le {f : ℕ → ℝ} (hf : ∀ k, f k + 1 ≤ f (k + 1)) :
    Tendsto f atTop atTop :=
  tendsto_atTop_mono (add_natCast_le_of_add_one_le hf)
    (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)

end
