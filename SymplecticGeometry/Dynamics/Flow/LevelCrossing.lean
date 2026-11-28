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

## Main results

* `Flow.levelCrossingTime_eq_of_subsingleton`: on an orbit that meets the level at most once,
  the crossing time is the time at which it meets it.
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

end Flow

end
