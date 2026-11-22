/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The `H^s` norm of a directional derivative of a Schwartz function

For a Schwartz function `u` with values in a complex Hilbert space and a vector `v`,
`‖∂_v u‖_{H^s} ≤ 2π ‖v‖ ‖u‖_{H^{s+1}}`: a directional derivative costs one order of regularity,
with an explicit constant. The `H^s` norm of a Schwartz function is the `L²` norm of its weighted
Fourier transform `⟨ξ⟩ ^ s 𝓕 u` (Tau Ceti's `SchwartzMap.norm_toBesselPotentialSpaceCLM`),
the Fourier transform of `∂_v u` is `2πi ⟪ξ, v⟫ 𝓕 u` (Tau Ceti's
`SchwartzMap.fourier_lineDerivOp_apply`), and `|⟪ξ, v⟫| ≤ ‖v‖ ⟨ξ⟩`. Mathlib's
`TemperedDistribution.MemSobolev.lineDerivOp` gives the membership `∂_v u ∈ H^s` for
`u ∈ H^{s+1}`, without the norm.

With `s = 0` (Tau Ceti's `SchwartzMap.norm_toBesselPotentialSpaceCLM_zero`), this bounds the `L²`
norm of each first derivative of `u` by its `H¹` norm.

## Main results

* `SchwartzMap.norm_toBesselPotentialSpaceCLM_lineDerivOp_le`: the bound for `∂_v u`.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3 (the Sobolev spaces `H_s` and their Fourier description).
-/

public section

open MeasureTheory FourierTransform
open scoped SchwartzMap LineDeriv Real RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace SchwartzMap

/-- **A derivative costs one order of regularity.** For a Schwartz function `u` and a vector `v`,
`‖∂_v u‖_{H^s} ≤ 2π ‖v‖ ‖u‖_{H^{s+1}}`. -/
theorem norm_toBesselPotentialSpaceCLM_lineDerivOp_le (s : ℝ) (v : E) (u : 𝓢(E, F)) :
    ‖toBesselPotentialSpaceCLM s 2 (∂_{v} u)‖ ≤
      2 * π * ‖v‖ * ‖toBesselPotentialSpaceCLM (s + 1) 2 u‖ := by
  rw [norm_toBesselPotentialSpaceCLM, norm_toBesselPotentialSpaceCLM,
    ← ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * π * ‖v‖), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (memLp_one_add_norm_sq_rpow_smul_fourier (s + 1) u 2).eLpNorm_ne_top)
    (eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (memLp_one_add_norm_sq_rpow_smul_fourier s _ 2).aestronglyMeasurable
      (.of_forall fun ξ ↦ ?_) 2)
  have h1 : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  -- `|⟪ξ, v⟫| ≤ ‖v‖ ‖ξ‖ ≤ ‖v‖ ⟨ξ⟩`, and `⟨ξ⟩ ^ (s + 1) = ⟨ξ⟩ ^ s ⟨ξ⟩`.
  have hξ : ‖ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_left zero_le_one)
  have hinner : |⟪ξ, v⟫| ≤ ‖v‖ * (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) :=
    (abs_real_inner_le_norm ξ v).trans (by rw [mul_comm]; gcongr)
  have hw : (1 + ‖ξ‖ ^ 2) ^ ((s + 1) / 2) =
      (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add h1]
    ring_nf
  rw [fourier_lineDerivOp_apply]
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_ofNat,
    Complex.norm_I, Complex.norm_real, Real.abs_pi, mul_one]
  rw [hw, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖ξ‖ ^ 2) ^ (s / 2)),
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2))]
  calc (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (2 * π * |⟪ξ, v⟫| * ‖𝓕 u ξ‖)
      ≤ (1 + ‖ξ‖ ^ 2) ^ (s / 2) *
          (2 * π * (‖v‖ * (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2)) * ‖𝓕 u ξ‖) := by gcongr
    _ = 2 * π * ‖v‖ * ((1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) * ‖𝓕 u ξ‖) := by
        ring

end SchwartzMap
