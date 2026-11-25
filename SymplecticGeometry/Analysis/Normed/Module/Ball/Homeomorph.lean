/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# The values of `univBall`

Mathlib's `OpenPartialHomeomorph.univBall c ρ` is defined on the whole normed space `E`, and for
`0 < ρ` its target is the ball `ball c ρ`. This file records the pointwise form of that fact.

## Main results

* `OpenPartialHomeomorph.univBall_mem_ball`: for `0 < ρ`, `univBall c ρ x ∈ ball c ρ`.
-/

public section

open Metric

namespace OpenPartialHomeomorph

/-- For `0 < ρ`, Mathlib's map `univBall c ρ` takes its values in the ball `ball c ρ`. -/
theorem univBall_mem_ball {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [PseudoMetricSpace P] [NormedAddTorsor E P] {c : P} {ρ : ℝ} (hρ : 0 < ρ) (x : E) :
    univBall c ρ x ∈ ball c ρ :=
  univBall_target c hρ ▸ (univBall c ρ).map_source (by simp [univBall_source])

end OpenPartialHomeomorph

end
