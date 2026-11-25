/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Differentiating the integral of a closed one-form along parallel segments

Let `A B : ℝ × ℝ → F`, with `A` of class `C¹`, and suppose that the partial derivative of `A` in
the first variable is the partial derivative of `B` in the second one along the segment
`{s₀} × [a, b]`. Then `s ↦ ∫ t in a..b, A (s, t)` has derivative `B (s₀, b) - B (s₀, a)` at `s₀`:
differentiate under the integral sign (Mathlib's
`intervalIntegral.hasFDerivAt_integral_of_contDiffOn`), and integrate `∂_t B` by the fundamental
theorem of calculus.

In terms of forms: if `B ds + A dt` is a closed one-form on `ℝ × ℝ`, that is `∂_t B = ∂_s A`,
its integral `∫ t in a..b, A (s, t)` along the segment from `(s, a)` to `(s, b)` has derivative
`B (s, b) - B (s, a)` in `s`.

## Main results

* `intervalIntegral.hasDerivAt_integral_of_hasDerivAt_snd`: the derivative of
  `s ↦ ∫ t in a..b, A (s, t)` at `s₀` is `B (s₀, b) - B (s₀, a)` when `∂_s A = ∂_t B` on
  `{s₀} × [a, b]`.
-/

public section

open scoped Interval

namespace intervalIntegral

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Let `A : ℝ × ℝ → F` be of class `C¹`, and let `B : ℝ × ℝ → F` be such that for each `t` in
`[a, b]` the curve `τ ↦ B (s₀, τ)` has at `t` the derivative `∂_s A (s₀, t)`. Then
`s ↦ ∫ t in a..b, A (s, t)` has derivative `B (s₀, b) - B (s₀, a)` at `s₀`. -/
theorem hasDerivAt_integral_of_hasDerivAt_snd {A B : ℝ × ℝ → F} {s₀ a b : ℝ}
    (hA : ContDiff ℝ 1 A)
    (hB : ∀ t ∈ [[a, b]], HasDerivAt (fun τ ↦ B (s₀, τ)) (fderiv ℝ A (s₀, t) (1, 0)) t) :
    HasDerivAt (fun s ↦ ∫ t in a..b, A (s, t)) (B (s₀, b) - B (s₀, a)) s₀ := by
  have hAc : Continuous fun t : ℝ ↦ fderiv ℝ A (s₀, t) :=
    (hA.continuous_fderiv one_ne_zero).comp (by fun_prop)
  -- Differentiating under the integral sign.
  have hI := (hasFDerivAt_integral_of_contDiffOn (μ := MeasureTheory.volume)
    (f := fun s t ↦ A (s, t)) (x₀ := s₀) (a := a) (b := b) Filter.univ_mem
    hA.contDiffOn).hasDerivAt
  simp only [fun t ↦ TauCeti.fderiv_slice_left (hA.differentiable one_ne_zero (s₀, t))] at hI
  rw [ContinuousLinearMap.intervalIntegral_apply
    ((hAc.clm_comp continuous_const).intervalIntegrable a b)] at hI
  -- The fundamental theorem of calculus along `t ↦ (s₀, t)`.
  rw [← integral_eq_sub_of_hasDerivAt hB ((hAc.clm_apply continuous_const).intervalIntegrable a b)]
  simpa using hI

end intervalIntegral

end
