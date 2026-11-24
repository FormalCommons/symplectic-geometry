/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Reflection.HalfSpace

/-!
# Time dilations

A fact about Tau Ceti's time dilations `TauCeti.HalfSpaceExtension.timeScale`:
`timeScale_of_fst_eq_zero`, that they fix the points of time `0`.
-/

public section

namespace TauCeti.HalfSpaceExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The time dilations fix the points of time `0`. -/
theorem timeScale_of_fst_eq_zero {z : ℝ × E} (hz : z.1 = 0) (a : ℝ) :
    timeScale a z = z := by
  ext <;> simp [hz]

end TauCeti.HalfSpaceExtension

end
