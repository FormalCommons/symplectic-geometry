/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Probability.Moments.ComplexMGF

/-!
# Moment-generating functions of continuous functions on compact spaces

Let `X` be a continuous real function on a compact space, and `μ` a measure that is finite on
compact sets.

* `ProbabilityTheory.integrableExpSet_eq_univ_of_continuous`: `e^{t X}` is integrable for every
  real `t`.
* `ProbabilityTheory.analyticOnNhd_complexMGF_of_continuous`: the complex moment-generating
  function `z ↦ ∫ e^{z X} dμ` is entire, by `ProbabilityTheory.analyticOnNhd_complexMGF`.
-/

public section

open Set MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
  [OpensMeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasureOnCompacts μ] {X : Ω → ℝ}

/-- A continuous function `X` on a compact space has `e^{t X}` integrable for every real `t`,
against a measure that is finite on compact sets. -/
theorem integrableExpSet_eq_univ_of_continuous (hX : Continuous X) :
    integrableExpSet X μ = univ :=
  eq_univ_of_forall fun _ ↦ (Real.continuous_exp.comp (continuous_const.mul hX))
    |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The complex moment-generating function `z ↦ ∫ e^{z X} dμ` of a continuous function `X` on a
compact space, against a measure that is finite on compact sets, is analytic on all of `ℂ`. -/
theorem analyticOnNhd_complexMGF_of_continuous (hX : Continuous X) :
    AnalyticOnNhd ℂ (complexMGF X μ) univ := by
  simpa [integrableExpSet_eq_univ_of_continuous hX] using
    analyticOnNhd_complexMGF (X := X) (μ := μ)

end ProbabilityTheory

end
