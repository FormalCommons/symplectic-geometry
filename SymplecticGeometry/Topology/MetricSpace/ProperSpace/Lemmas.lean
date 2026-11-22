/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Enlarging a closed ball inside an open set

In a proper pseudometric space, an open set `U` that contains the closed ball `closedBall x r₀`
contains a ball of some radius `r > r₀`, open or closed. These results enlarge a ball, where
Mathlib's `exists_lt_subset_ball` and `exists_pos_lt_subset_ball` shrink one, and the file is
named like Mathlib's `Mathlib/Topology/MetricSpace/ProperSpace/Lemmas.lean`, which holds those.

The proof takes the compact set `closedBall x (r₀ + 1) \ U`: if it is nonempty, the distance to
`x` attains a minimum on it, and that minimum is larger than `r₀`.

## Main results

* `Metric.exists_lt_ball_subset_of_closedBall_subset`: an open set containing `closedBall x r₀`
  contains `ball x r` for some `r > r₀`.
* `Metric.exists_lt_closedBall_subset_of_closedBall_subset`: it also contains `closedBall x r`
  for some `r > r₀`.
-/

public section

open Set

namespace Metric

variable {α : Type*} [PseudoMetricSpace α] [ProperSpace α] {x : α} {r₀ : ℝ} {U : Set α}

/-- In a proper pseudometric space, an open set that contains the closed ball of radius `r₀`
about `x` contains the open ball about `x` of some radius `r > r₀`. -/
theorem exists_lt_ball_subset_of_closedBall_subset (hU : IsOpen U)
    (h : closedBall x r₀ ⊆ U) : ∃ r, r₀ < r ∧ ball x r ⊆ U := by
  set K := closedBall x (r₀ + 1) \ U
  have hK : IsCompact K := (isCompact_closedBall x _).diff hU
  rcases K.eq_empty_or_nonempty with hK₀ | hK₀
  · refine ⟨r₀ + 1, by linarith, fun z hz ↦ ?_⟩
    by_contra hzU
    exact hK₀.subset ⟨ball_subset_closedBall hz, hzU⟩
  obtain ⟨y, hyK, hy⟩ := hK.exists_isMinOn hK₀ (continuous_id.dist continuous_const).continuousOn
  have hyr₀ : r₀ < dist y x := not_le.1 fun hle ↦ hyK.2 (h hle)
  refine ⟨min (dist y x) (r₀ + 1), lt_min hyr₀ (by linarith), fun z hz ↦ ?_⟩
  by_contra hzU
  rw [mem_ball, lt_min_iff] at hz
  exact (hy ⟨mem_closedBall.2 hz.2.le, hzU⟩).not_gt hz.1

/-- In a proper pseudometric space, an open set that contains the closed ball of radius `r₀`
about `x` contains the closed ball about `x` of some radius `r > r₀`. -/
theorem exists_lt_closedBall_subset_of_closedBall_subset (hU : IsOpen U)
    (h : closedBall x r₀ ⊆ U) : ∃ r, r₀ < r ∧ closedBall x r ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := exists_lt_ball_subset_of_closedBall_subset hU h
  exact ⟨(r₀ + r) / 2, by linarith, (closedBall_subset_ball (by linarith)).trans hrU⟩

end Metric

end
