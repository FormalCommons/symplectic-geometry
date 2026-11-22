/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The `Lᵖ` seminorm under a linear equivalence of two spaces

For additive Haar measures `μ` on `E` and `ν` on `E'` and a continuous linear equivalence
`e : E ≃L[ℝ] E'`, the image `μ.map e` is a multiple of `ν`, by the factor
`(μ.map e).addHaarScalarFactor ν`. So the `Lᵖ` seminorm of `u ∘ e` for `μ` is that of `u` for
`ν`, times the `p`-th root of this factor
(`MeasureTheory.eLpNorm_comp_continuousLinearEquiv_eq_addHaarScalarFactor_rpow_mul`).

This is the form, between two different spaces, of Tau Ceti's
`MeasureTheory.Measure.eLpNorm_comp_continuousLinearEquiv`, for a linear automorphism, whose factor
is a power of the determinant. The proof follows the same steps: the change of variables
`MeasurableEmbedding.eLpNorm_map_measure`, then `eLpNorm_smul_measure_of_ne_zero`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {E E' G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E'] [TopologicalSpace G] [ContinuousENorm G]

/-- **Linear change of variables in the `Lᵖ` seminorm, between two spaces.** For additive Haar
measures `μ` on `E` and `ν` on `E'` and a continuous linear equivalence `e : E ≃L[ℝ] E'`, the
`Lᵖ` seminorm of `u ∘ e` for `μ` is that of `u` for `ν` times `c ^ (1 / p)`, where
`c = (μ.map e).addHaarScalarFactor ν` is the factor with `μ.map e = c • ν`. The exponent is
`(1 / p).toReal`, which is `0` for `p = 0` and `p = ∞`. -/
theorem eLpNorm_comp_continuousLinearEquiv_eq_addHaarScalarFactor_rpow_mul (μ : Measure E)
    [μ.IsAddHaarMeasure] (ν : Measure E') [ν.IsAddHaarMeasure] (e : E ≃L[ℝ] E') (u : E' → G)
    (p : ℝ≥0∞) :
    eLpNorm (u ∘ e) p μ =
      ((μ.map e).addHaarScalarFactor ν : ℝ≥0∞) ^ (1 / p).toReal * eLpNorm u p ν := by
  have hc : ((μ.map e).addHaarScalarFactor ν : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  rw [← he.eLpNorm_map_measure]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (μ.map e) ν]
  rw [ENNReal.smul_def, eLpNorm_smul_measure_of_ne_zero hc, smul_eq_mul]

end MeasureTheory

end
