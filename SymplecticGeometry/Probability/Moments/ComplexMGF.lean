/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Probability.Moments.ComplexMGF
import TauCeti.Probability.Moments.IntegrableExpMul

/-!
# Moment-generating functions of bounded random variables

* `ProbabilityTheory.analyticOnNhd_complexMGF_of_mem_Icc`: for a real random variable `X` that
  lies almost surely in a compact interval, under a finite measure, the complex
  moment-generating function `z ↦ ∫ e^{z X} dμ` is analytic on all of `ℂ`. Its exponential
  moments are finite at every real rate (`TauCeti.integrableExpSet_eq_univ_of_mem_Icc`), so this
  is `ProbabilityTheory.analyticOnNhd_complexMGF`.
-/

public section

open Set MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}

/-- The complex moment-generating function `z ↦ ∫ e^{z X} dμ` of a real random variable `X` that
lies almost surely in a compact interval `[a, b]`, under a finite measure, is analytic on all
of `ℂ`. -/
theorem analyticOnNhd_complexMGF_of_mem_Icc {a b : ℝ} (hX : AEMeasurable X μ)
    (hX_mem : ∀ᵐ ω ∂μ, X ω ∈ Icc a b) :
    AnalyticOnNhd ℂ (complexMGF X μ) univ := by
  simpa [TauCeti.integrableExpSet_eq_univ_of_mem_Icc hX hX_mem] using
    analyticOnNhd_complexMGF (X := X) (μ := μ)

end ProbabilityTheory

end
