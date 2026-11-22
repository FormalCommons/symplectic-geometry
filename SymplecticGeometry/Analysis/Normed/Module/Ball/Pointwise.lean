/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Enlarging a closed ball inside an open set

In a proper real normed space, an open set `U` that contains the closed ball `closedBall x r₀`
contains a ball of some radius `r > r₀`, open or closed. The closed ball is compact, so some
thickening of it lies in `U` (`IsCompact.exists_thickening_subset_open`), and the thickening of a
closed ball is a ball (`thickening_closedBall`). The file is named like Mathlib's
`Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`, where `thickening_closedBall` is.

## Main results

* `Metric.exists_lt_ball_subset_of_closedBall_subset`: an open set containing `closedBall x r₀`
  contains `ball x r` for some `r > r₀`.
* `Metric.exists_lt_closedBall_subset_of_closedBall_subset`: it also contains `closedBall x r`
  for some `r > r₀`.
-/

public section

open Set

namespace Metric

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {x : E} {r₀ : ℝ} {U : Set E}

/-- In a proper real normed space, an open set that contains the closed ball of radius `r₀`
about `x` contains the open ball about `x` of some radius `r > r₀`. -/
theorem exists_lt_ball_subset_of_closedBall_subset (hU : IsOpen U)
    (h : closedBall x r₀ ⊆ U) : ∃ r, r₀ < r ∧ ball x r ⊆ U := by
  rcases lt_or_ge r₀ 0 with hr₀ | hr₀
  · exact ⟨r₀ / 2, by linarith, by simp [ball_eq_empty.2 (by linarith : r₀ / 2 ≤ 0)]⟩
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall x r₀).exists_thickening_subset_open hU h
  rw [thickening_closedBall hδ hr₀] at hδU
  exact ⟨δ + r₀, by linarith, hδU⟩

/-- In a proper real normed space, an open set that contains the closed ball of radius `r₀`
about `x` contains the closed ball about `x` of some radius `r > r₀`. -/
theorem exists_lt_closedBall_subset_of_closedBall_subset (hU : IsOpen U)
    (h : closedBall x r₀ ⊆ U) : ∃ r, r₀ < r ∧ closedBall x r ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := exists_lt_ball_subset_of_closedBall_subset hU h
  exact ⟨(r₀ + r) / 2, by linarith, (closedBall_subset_ball (by linarith)).trans hrU⟩

end Metric

end
