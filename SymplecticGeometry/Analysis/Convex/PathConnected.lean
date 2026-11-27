/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Connected.PathConnected

import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Ranges of maps on a product with a ball

An open ball of positive radius in a real normed space is convex, hence path connected
(`Convex.isPathConnected`). So for a path connected space `Q`, the range of a continuous map
on `Q × ball c R` is path connected when `R > 0`.

## Main results

* `isPathConnected_range_prod_ball`: the range of a continuous map on `Q × ball c R` is path
  connected, for path connected `Q` and `R > 0`.
-/

public section

open Metric Set

/-- The range of a continuous map on `Q × ball c R`, for a path connected space `Q` and a ball
of positive radius in a real normed space, is path connected. -/
theorem isPathConnected_range_prod_ball {Q X E : Type*} [TopologicalSpace Q]
    [PathConnectedSpace Q] [TopologicalSpace X] [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {c : E} {R : ℝ} (hR : 0 < R) {f : Q × ↥(ball c R) → X} (hf : Continuous f) :
    IsPathConnected (range f) :=
  have : PathConnectedSpace ↥(ball c R) := isPathConnected_iff_pathConnectedSpace.1
    ((convex_ball c R).isPathConnected ⟨c, mem_ball_self hR⟩)
  isPathConnected_range hf

end
