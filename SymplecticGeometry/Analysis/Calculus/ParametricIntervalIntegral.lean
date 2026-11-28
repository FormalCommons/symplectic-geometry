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
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic

/-!
# Differentiating parametric interval integrals

Let `A B : ℝ × ℝ → F`, with `A` of class `C¹` on an open set `U` that contains the segment
`{s₀} × [a, b]`, and suppose that the partial derivative of `A` in the first variable is the
partial derivative of `B` in the second one along that segment. Then
`s ↦ ∫ t in a..b, A (s, t)` has derivative `B (s₀, b) - B (s₀, a)` at `s₀`: differentiate under
the integral sign (Tau Ceti's `TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn`), and integrate
`∂_t B` by the fundamental theorem of calculus.

In terms of forms: if `B ds + A dt` is a closed one-form on `ℝ × ℝ`, that is `∂_t B = ∂_s A`,
its integral `∫ t in a..b, A (s, t)` along the segment from `(s, a)` to `(s, b)` has derivative
`B (s, b) - B (s, a)` in `s`.

For an iterated integral `s ↦ ∫ t in a..b, ∫ θ in c..d, G (s, t, θ)` of a `C¹` function `G`,
differentiating twice under the integral sign (Mathlib's
`intervalIntegral.hasFDerivAt_integral_of_contDiffOn`) gives the iterated integral of `∂_s G`.

## Main results

* `intervalIntegral.hasDerivAt_integral_integral_of_contDiff`: differentiation under an iterated
  integral `s ↦ ∫ t in a..b, ∫ θ in c..d, G (s, t, θ)` of a `C¹` function.
* `intervalIntegral.hasDerivAt_integral_of_hasDerivAt_snd`: the derivative of
  `s ↦ ∫ t in a..b, A (s, t)` at `s₀` is `B (s₀, b) - B (s₀, a)` when `∂_s A = ∂_t B` on
  `{s₀} × [a, b]`.
-/

public section

open scoped Interval

namespace intervalIntegral

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Differentiation under an iterated integral.** For `G : ℝ × ℝ × ℝ → F` of class `C¹`, the
iterated integral `s ↦ ∫ t in a..b, ∫ θ in c..d, G (s, t, θ)` has derivative at `s₀` the iterated
integral of the partial derivative of `G` in its first variable. -/
theorem hasDerivAt_integral_integral_of_contDiff {G : ℝ × ℝ × ℝ → F}
    (hG : ContDiff ℝ 1 G) (a b c d s₀ : ℝ) :
    HasDerivAt (fun s ↦ ∫ t in a..b, ∫ θ in c..d, G (s, t, θ))
      (∫ t in a..b, ∫ θ in c..d, fderiv ℝ G (s₀, t, θ) (1, 0, 0)) s₀ := by
  have hGd := hG.differentiable one_ne_zero
  have hGc := hG.continuous_fderiv one_ne_zero
  have hin (t : ℝ) : HasFDerivAt (fun s ↦ ∫ θ in c..d, G (s, t, θ))
      (∫ θ in c..d, fderiv ℝ (fun s ↦ G (s, t, θ)) s₀) s₀ := by
    refine intervalIntegral.hasFDerivAt_integral_of_contDiffOn (μ := MeasureTheory.volume)
      (f := fun s θ ↦ G (s, t, θ)) Filter.univ_mem ?_
    exact (hG.comp (by fun_prop)).contDiffOn
  have hcd : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ ∫ θ in c..d, G (p.1, p.2, θ)) :=
    contDiffOn_univ.mp <| ContDiffOn.parametric_intervalIntegral (μ := MeasureTheory.volume)
      (f := fun (p : ℝ × ℝ) θ ↦ G (p.1, p.2, θ)) isOpen_univ (hG.comp (by fun_prop)).contDiffOn
  have hout := intervalIntegral.hasFDerivAt_integral_of_contDiffOn (μ := MeasureTheory.volume)
      (f := fun s t ↦ ∫ θ in c..d, G (s, t, θ)) (x₀ := s₀) (a := a) (b := b) Filter.univ_mem
      (by simpa [Function.uncurry_def] using hcd.contDiffOn)
  -- The inner partial derivatives, written through the full derivative of `G`.
  have hpart (t θ : ℝ) : fderiv ℝ (fun s ↦ G (s, t, θ)) s₀ =
      (fderiv ℝ G (s₀, t, θ)).comp (ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ)) :=
    TauCeti.fderiv_slice_left (f := G) (b := (t, θ)) (hGd _)
  have hcont (t : ℝ) : Continuous fun θ ↦ fderiv ℝ (fun s ↦ G (s, t, θ)) s₀ := by
    simp only [hpart]
    exact (hGc.comp (by fun_prop)).clm_comp continuous_const
  have hcont' : Continuous fun t ↦ fderiv ℝ (fun s ↦ ∫ θ in c..d, G (s, t, θ)) s₀ := by
    simp only [fun t ↦ (hin t).fderiv]
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ c d
    simp only [Function.uncurry_def, hpart]
    exact (hGc.comp (by fun_prop)).clm_comp continuous_const
  convert hout.hasDerivAt using 1
  rw [ContinuousLinearMap.intervalIntegral_apply (hcont'.intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [(hin t).fderiv, ContinuousLinearMap.intervalIntegral_apply ((hcont t).intervalIntegrable _ _)]
  simp [hpart, Prod.mk_zero_zero]

variable [CompleteSpace F]

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
