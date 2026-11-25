/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.MeasureTheory.Integral.Dilation
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Balls as families of circles

Let `E` be a finite-dimensional complex normed space with an additive Haar measure `μ`. The ball
`Metric.ball c ρ` is the union of the circles `θ ↦ c + circleMap 0 ρ θ • v`, for `v` in the unit
ball. This file shows that the lower Lebesgue integral of a measurable `g : E → ℝ≥0∞` over the
ball is `ρ ^ finrank ℝ E` times the integral over `v ∈ Metric.ball 0 1` of the mean of `g` over
these circles (`MeasureTheory.setLIntegral_ball_eq_lintegral_circleAverage`). The mean over a
circle is the lower average `⨍⁻ θ in Ioc 0 (2 * π), …`, not Mathlib's `Real.circleAverage`,
which is a Bochner average: with lower integrals nothing needs to be integrable.

## Main results

* `MeasureTheory.Measure.lintegral_comp_complex_smul`: multiplication by a complex number of
  norm one does not change a lower integral against `μ`. It is a real linear isometry, so it
  preserves `μ` by Tau Ceti's `LinearIsometryEquiv.measurePreserving_addHaar`.
* `MeasureTheory.setLIntegral_ball_zero_one_eq_lintegral_setLAverage_circleMap`: on the unit
  ball, averaging a measurable function over the circles `θ ↦ circleMap 0 1 θ • v` does not
  change its integral. Each rotation preserves `μ` and the unit ball, and Tonelli's theorem
  exchanges the average over `θ` with the integral over `v`.
* `MeasureTheory.setLIntegral_ball_eq_lintegral_circleAverage`: the identity for any ball, from
  the unit ball by the affine change of variables `v ↦ c + ρ • v` (Tau Ceti's
  `MeasureTheory.Measure.setLIntegral_comp_add_smul`).
-/

public section

open Complex Metric Module Set
open scoped ENNReal Real

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Multiplication by a complex number of norm one does not change the lower integral against an
additive Haar measure on a finite-dimensional complex normed space. The function need not be
measurable. -/
theorem Measure.lintegral_comp_complex_smul {z : ℂ} (hz : ‖z‖ = 1) (f : E → ℝ≥0∞) :
    ∫⁻ v, f (z • v) ∂μ = ∫⁻ v, f v ∂μ := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.1 (hz.symm ▸ one_ne_zero)
  let e : E ≃ₗᵢ[ℝ] E :=
    { (LinearEquiv.smulOfNeZero ℂ E z hz0).restrictScalars ℝ with
      norm_map' := fun v => by simp [norm_smul, hz] }
  exact (e.measurePreserving_addHaar μ).lintegral_comp_emb e.toHomeomorph.measurableEmbedding f

/-- On the unit ball, averaging a measurable function over the circles `θ ↦ circleMap 0 1 θ • v`
does not change its lower integral against an additive Haar measure. -/
theorem setLIntegral_ball_zero_one_eq_lintegral_setLAverage_circleMap {h : E → ℝ≥0∞}
    (hh : Measurable h) :
    ∫⁻ v in ball (0 : E) 1, h v ∂μ =
      ∫⁻ v in ball (0 : E) 1, (⨍⁻ θ in Ioc 0 (2 * π), h (circleMap 0 1 θ • v)) ∂μ := by
  have hrot (θ : ℝ) :
      ∫⁻ v in ball (0 : E) 1, h (circleMap 0 1 θ • v) ∂μ = ∫⁻ v in ball (0 : E) 1, h v ∂μ := by
    have hz : ‖circleMap 0 1 θ‖ = 1 := by simp
    rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball,
      ← Measure.lintegral_comp_complex_smul μ hz ((ball (0 : E) 1).indicator h)]
    congr with v
    simp only [indicator, mem_ball_zero_iff, norm_smul, hz, one_mul]
  have hmeas : Measurable fun p : E × ℝ => h (circleMap 0 1 p.2 • p.1) :=
    hh.comp (by unfold circleMap; fun_prop)
  have hI0 : volume (Ioc 0 (2 * π)) ≠ 0 := by simp [Real.pi_pos]
  have hIt : volume (Ioc 0 (2 * π)) ≠ ∞ := by simp [ENNReal.mul_eq_top]
  simp_rw [setLAverage_eq, ENNReal.div_eq_inv_mul]
  rw [lintegral_const_mul _ hmeas.lintegral_prod_right',
    lintegral_lintegral_swap hmeas.aemeasurable, lintegral_congr fun θ => hrot θ,
    setLIntegral_const, mul_comm, mul_assoc, ENNReal.mul_inv_cancel hI0 hIt, mul_one]

/-- **Balls as families of circles.** For a measurable `g ≥ 0` and `ρ > 0`, the lower integral of
`g` over `Metric.ball c ρ` against an additive Haar measure is `ρ ^ finrank ℝ E` times the lower
integral, over `v` in the unit ball, of the mean of `g` over the circle
`θ ↦ c + circleMap 0 ρ θ • v`. -/
theorem setLIntegral_ball_eq_lintegral_circleAverage {g : E → ℝ≥0∞} (hg : Measurable g)
    (c : E) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ x in ball c ρ, g x ∂μ = ENNReal.ofReal (ρ ^ finrank ℝ E) *
      ∫⁻ v in ball (0 : E) 1, (⨍⁻ θ in Ioc 0 (2 * π), g (c + circleMap 0 ρ θ • v)) ∂μ := by
  have hd : 0 < ρ ^ finrank ℝ E := pow_pos hρ _
  have hpre : (fun v : E => c + ρ • v) ⁻¹' ball c ρ = ball 0 1 := by
    ext v
    simp [dist_eq_norm, norm_smul, abs_of_pos hρ, hρ]
  have hscale := Measure.setLIntegral_comp_add_smul μ g c hρ.ne' (ball c ρ)
  rw [hpre, abs_of_pos (inv_pos.2 hd)] at hscale
  have hcirc (θ : ℝ) (v : E) : ρ • circleMap 0 1 θ • v = circleMap 0 ρ θ • v := by
    rw [← Complex.coe_smul, smul_smul]
    simp [circleMap]
  calc ∫⁻ x in ball c ρ, g x ∂μ
      = ENNReal.ofReal (ρ ^ finrank ℝ E) *
          (ENNReal.ofReal (ρ ^ finrank ℝ E)⁻¹ * ∫⁻ x in ball c ρ, g x ∂μ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hd.le, mul_inv_cancel₀ hd.ne', ENNReal.ofReal_one,
          one_mul]
    _ = _ := by
        rw [← hscale, setLIntegral_ball_zero_one_eq_lintegral_setLAverage_circleMap μ
          (h := fun v => g (c + ρ • v)) (by fun_prop)]
        simp_rw [hcirc]

end MeasureTheory

end
