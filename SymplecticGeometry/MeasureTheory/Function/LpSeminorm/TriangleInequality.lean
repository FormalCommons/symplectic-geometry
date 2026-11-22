/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# The integral of the square of a sum of norms

For functions `f i` in `L²(μ)`, indexed by a finite set `s`, the integral of
`(∑ i ∈ s, ‖f i x‖) ^ 2` is at most `(∑ i ∈ s, ‖f i‖_{L²(μ)}) ^ 2`
(`MeasureTheory.integral_sum_norm_sq_le`): the integral is the square of the `L²` norm of the sum
of the norms, which the triangle inequality `MeasureTheory.eLpNorm_sum_le` bounds.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]

/-- For functions `f i` in `L²(μ)`, `∫ (∑ i ∈ s, ‖f i x‖) ^ 2 dμ ≤ (∑ i ∈ s, ‖f i‖_{L²(μ)}) ^ 2`. -/
theorem integral_sum_norm_sq_le {ι : Type*} (s : Finset ι) {f : ι → α → E}
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ) :
    ∫ x, (∑ i ∈ s, ‖f i x‖) ^ 2 ∂μ ≤ (∑ i ∈ s, (eLpNorm (f i) 2 μ).toReal) ^ 2 := by
  set N : α → ℝ := fun x ↦ ∑ i ∈ s, ‖f i x‖
  have hN : MemLp N 2 μ := memLp_finsetSum s fun i hi ↦ (hf i hi).norm
  have hint : ∫ x, N x ^ 2 ∂μ = (eLpNorm N 2 μ).toReal ^ 2 := by
    rw [hN.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (integral_nonneg fun x ↦ by positivity)]
    norm_num
  have hne (i : ι) (hi : i ∈ s) : eLpNorm (f i) 2 μ ≠ ∞ := (hf i hi).eLpNorm_ne_top
  have hle : eLpNorm N 2 μ ≤ ∑ i ∈ s, eLpNorm (f i) 2 μ := by
    have hfun : N = ∑ i ∈ s, fun x ↦ ‖f i x‖ := by
      ext x
      simp [N]
    rw [hfun]
    exact (eLpNorm_sum_le one_le_two).trans_eq
      (Finset.sum_congr rfl fun i hi ↦ eLpNorm_norm (f i) (hf i hi).aestronglyMeasurable)
  rw [hint, ← ENNReal.toReal_sum hne]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hne) hle) 2

end MeasureTheory

end
