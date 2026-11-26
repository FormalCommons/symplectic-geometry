/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Continuous linear equivalences and circle integrals

A continuous linear equivalence `L` of complex normed spaces commutes with Mathlib's circle
integrals: `∮ z in C(c, R), L (f z) = L (∮ z in C(c, R), f z)`
(`ContinuousLinearEquiv.circleIntegral_comp_comm`). Unlike Tau Ceti's
`ContinuousLinearMap.circleIntegral_comp_comm`, this needs neither integrability of `f` nor
completeness of the spaces, since it follows from Mathlib's
`ContinuousLinearEquiv.integral_comp_comm`.
-/

public section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A continuous linear equivalence commutes with circle integrals. -/
theorem ContinuousLinearEquiv.circleIntegral_comp_comm (L : E ≃L[ℂ] F) (f : ℂ → E) (c : ℂ)
    (R : ℝ) : ∮ z in C(c, R), L (f z) = L (∮ z in C(c, R), f z) := by
  simp only [circleIntegral, intervalIntegral, ← L.integral_comp_comm, map_sub, map_smul]

end
