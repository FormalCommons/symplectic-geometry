/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Enlarging a closed ball inside an open set

In a proper pseudometric space, an open set `U` that contains the closed ball `closedBall x r₀`
contains a ball of some radius `r > r₀`, open or closed. These results enlarge a ball, where
Mathlib's `exists_lt_subset_ball` and `exists_pos_lt_subset_ball` shrink one, and the file is
named like Mathlib's `Mathlib/Topology/MetricSpace/ProperSpace/Lemmas.lean`, which holds those.

The proof takes `r = infDist x Uᶜ`. Since `Uᶜ` is closed and the space is proper, some point of
`Uᶜ` is at that distance from `x` (`IsClosed.exists_infDist_eq_dist`); it lies outside
`closedBall x r₀`, so `r₀ < r`; and `ball x (infDist x Uᶜ) ⊆ U` is
`Metric.ball_infDist_compl_subset`.

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
  rcases Uᶜ.eq_empty_or_nonempty with hc | hc
  · exact ⟨r₀ + 1, by linarith, by simp [compl_empty_iff.1 hc]⟩
  obtain ⟨y, hy, hd⟩ := hU.isClosed_compl.exists_infDist_eq_dist hc x
  exact ⟨_, hd ▸ lt_of_not_ge fun hle ↦ hy (h (mem_closedBall'.2 hle)),
    ball_infDist_compl_subset⟩

/-- In a proper pseudometric space, an open set that contains the closed ball of radius `r₀`
about `x` contains the closed ball about `x` of some radius `r > r₀`. -/
theorem exists_lt_closedBall_subset_of_closedBall_subset (hU : IsOpen U)
    (h : closedBall x r₀ ⊆ U) : ∃ r, r₀ < r ∧ closedBall x r ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := exists_lt_ball_subset_of_closedBall_subset hU h
  exact ⟨(r₀ + r) / 2, by linarith, (closedBall_subset_ball (by linarith)).trans hrU⟩

end Metric

end
