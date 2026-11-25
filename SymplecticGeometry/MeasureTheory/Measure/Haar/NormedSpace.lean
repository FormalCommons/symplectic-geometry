/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Haar measure under scalars of norm one

Let `E` be a finite-dimensional normed space over an `RCLike` field `𝕜`, with an additive Haar
measure `μ`. Multiplication by a scalar `z : 𝕜` with `‖z‖ = 1` preserves `μ`
(`MeasureTheory.Measure.measurePreserving_smul_of_norm_eq_one`), so it leaves lower integrals
against `μ` unchanged (`MeasureTheory.Measure.lintegral_comp_smul_of_norm_eq_one`). Over the real
numbers, `v ↦ z • v` is a linear isometry, which preserves `μ` by Tau Ceti's
`LinearIsometryEquiv.measurePreserving_addHaar`.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Multiplication by a scalar of norm one preserves an additive Haar measure on a
finite-dimensional normed space over an `RCLike` field. -/
theorem measurePreserving_smul_of_norm_eq_one {z : 𝕜} (hz : ‖z‖ = 1) :
    MeasurePreserving (z • · : E → E) μ μ := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ 𝕜 E
  have hz0 : z ≠ 0 := norm_ne_zero_iff.1 (hz.symm ▸ one_ne_zero)
  let e : E ≃ₗᵢ[ℝ] E :=
    { (LinearEquiv.smulOfNeZero 𝕜 E z hz0).restrictScalars ℝ with
      norm_map' := fun v => by simp [norm_smul, hz] }
  exact e.measurePreserving_addHaar μ

/-- Multiplication by a scalar of norm one leaves the lower integral against an additive Haar
measure unchanged. The function need not be measurable. -/
theorem lintegral_comp_smul_of_norm_eq_one {z : 𝕜} (hz : ‖z‖ = 1) (f : E → ℝ≥0∞) :
    ∫⁻ v, f (z • v) ∂μ = ∫⁻ v, f v ∂μ := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.1 (hz.symm ▸ one_ne_zero)
  exact (measurePreserving_smul_of_norm_eq_one μ hz).lintegral_comp_emb
    (Homeomorph.smulOfNeZero z hz0).measurableEmbedding f

end MeasureTheory.Measure

end
