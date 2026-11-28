/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Dynamics.Flow.LevelCrossing

/-!
# The crossing time on an orbit that meets a level once

Let `φ` be a flow of `ℝ` on a topological space, `f` a real function on it and `c` a value. If
the orbit of `x` lies on the level `{f = c}` at exactly one time `t`, then Tau Ceti's crossing
time `Flow.levelCrossingTime φ f c x` is `t` (`Flow.levelCrossingTime_eq_of_subsingleton`): the
crossing time is a time on the level (`Flow.apply_flow_levelCrossingTime`), and there is only one.

The proof is that of Tau Ceti's `Flow.eq_levelCrossingTime_iff`
(`TauCeti/Dynamics/Flow/LevelCrossing.lean`), which gets the uniqueness from `f` being strictly
decreasing along the orbit; here the uniqueness is the hypothesis.

If instead `f` is monotone along the orbit of `x` and `f x < c`, the crossing time is
nonnegative (`Flow.levelCrossingTime_nonneg_of_monotone`): the orbit lies below the level at
every negative time, and the convention gives `0` when it never meets the level.

## Main results

* `Flow.levelCrossingTime_eq_of_subsingleton`: on an orbit that meets the level at most once,
  the crossing time is the time at which it meets it.
* `Flow.levelCrossingTime_nonneg_of_monotone`: a level above a point is crossed in the future.
-/

public section

namespace Flow

/-- **The crossing time on an orbit that meets the level once.** If the orbit of `x` under the
flow `φ` lies on the level `{f = c}` at the time `t`, and at no other time, then
`Flow.levelCrossingTime φ f c x = t`. Unlike `Flow.eq_levelCrossingTime_iff`, this does not ask
`f` to be strictly decreasing along the orbit. -/
theorem levelCrossingTime_eq_of_subsingleton {X : Type*} [TopologicalSpace X] {φ : Flow ℝ X}
    {f : X → ℝ} {c t : ℝ} {x : X} (hsub : {s | f (φ s x) = c}.Subsingleton)
    (ht : f (φ t x) = c) : levelCrossingTime φ f c x = t :=
  hsub (apply_flow_levelCrossingTime ⟨t, ht⟩) ht

/-- **A level above the point is crossed in the future.** If `f` is monotone along the orbit of
`x` under the flow `φ` and `f x < c`, then `0 ≤ Flow.levelCrossingTime φ f c x`. -/
theorem levelCrossingTime_nonneg_of_monotone {X : Type*} [TopologicalSpace X] {φ : Flow ℝ X}
    {f : X → ℝ} {c : ℝ} {x : X} (hmono : Monotone fun t ↦ f (φ t x)) (hx : f x < c) :
    0 ≤ levelCrossingTime φ f c x := by
  by_cases h : ∃ t, f (φ t x) = c
  · by_contra hneg
    have hle := hmono (not_le.1 hneg).le
    simp only [map_zero_apply, apply_flow_levelCrossingTime h] at hle
    exact hle.not_gt hx
  · exact (levelCrossingTime_of_forall_ne (not_exists.1 h)).ge

end Flow

end
