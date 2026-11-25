/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic

/-!
# Differentiating the integral of a closed one-form along parallel segments

Let `A B : ℝ × ℝ → F`, with `A` of class `C¹` on an open set `U` that contains the segment
`{s₀} × [a, b]`, and suppose that the partial derivative of `A` in the first variable is the
partial derivative of `B` in the second one along that segment. Then
`s ↦ ∫ t in a..b, A (s, t)` has derivative `B (s₀, b) - B (s₀, a)` at `s₀`: differentiate under
the integral sign (Tau Ceti's `TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn`), and integrate
`∂_t B` by the fundamental theorem of calculus.

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

/-- Let `A : ℝ × ℝ → F` be of class `C¹` on an open set `U` that contains `{s₀} × [a, b]`, and
let `B : ℝ × ℝ → F` be such that for each `t` in `[a, b]` the curve `τ ↦ B (s₀, τ)` has at `t`
the derivative `∂_s A (s₀, t)`. Then `s ↦ ∫ t in a..b, A (s, t)` has derivative
`B (s₀, b) - B (s₀, a)` at `s₀`. -/
theorem hasDerivAt_integral_of_hasDerivAt_snd {A B : ℝ × ℝ → F} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hA : ContDiffOn ℝ 1 A U) {s₀ a b : ℝ} (hsub : {s₀} ×ˢ [[a, b]] ⊆ U)
    (hB : ∀ t ∈ [[a, b]], HasDerivAt (fun τ ↦ B (s₀, τ)) (fderiv ℝ A (s₀, t) (1, 0)) t) :
    HasDerivAt (fun s ↦ ∫ t in a..b, A (s, t)) (B (s₀, b) - B (s₀, a)) s₀ := by
  obtain ⟨hi, h⟩ := TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn hU hA hsub
  rwa [integral_eq_sub_of_hasDerivAt hB hi] at h

end intervalIntegral

end
