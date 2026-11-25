/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# Enlarging an open ball inside an open set

In a proper pseudometric space, an open set `U` that contains the closed ball `closedBall x r₀`
contains the open ball `ball x r` for some `r > r₀`. This enlarges a ball, where Mathlib's
`exists_lt_subset_ball` and `exists_pos_lt_subset_ball` shrink one, and the file is named like
Mathlib's `Mathlib/Topology/MetricSpace/ProperSpace/Lemmas.lean`, which holds those.

The closed-ball version is Tau Ceti's `IsOpen.exists_gt_closedBall_subset`; the open-ball version
follows from it, since an open ball lies in the closed ball of the same radius.

## Main results

* `Metric.exists_lt_ball_subset_of_closedBall_subset`: an open set containing `closedBall x r₀`
  contains `ball x r` for some `r > r₀`.
-/

public section

namespace Metric

variable {α : Type*} [PseudoMetricSpace α] [ProperSpace α] {x : α} {r₀ : ℝ} {U : Set α}

/-- In a proper pseudometric space, an open set that contains the closed ball of radius `r₀`
about `x` contains the open ball about `x` of some radius `r > r₀`. -/
theorem exists_lt_ball_subset_of_closedBall_subset (hU : IsOpen U)
    (h : closedBall x r₀ ⊆ U) : ∃ r, r₀ < r ∧ ball x r ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := hU.exists_gt_closedBall_subset h
  exact ⟨r, hr, ball_subset_closedBall.trans hrU⟩

end Metric

end
