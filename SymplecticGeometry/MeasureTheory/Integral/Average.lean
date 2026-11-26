/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average

/-!
# Set averages bounded through lower averages

* `MeasureTheory.sub_setAverage_le_of_setLAverage_ofReal_sub_le`: if a real function `u` is
  integrable on a set `s` of finite positive measure, then a bound
  `⨍⁻ x in s, ofReal (K - u x) ∂μ ≤ ofReal L`, with `0 ≤ L`, gives `K - ⨍ x in s, u x ∂μ ≤ L`.

Such bounds on lower averages are what one gets from a sub-mean value inequality, where the
`ofReal` keeps the integrand nonnegative; this lemma turns them into a lower bound on the average
of `u`.
-/

public section

namespace MeasureTheory

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- If `u` is integrable on a set `s` with `0 < μ s < ∞`, and `0 ≤ L`, then
`⨍⁻ x in s, ofReal (K - u x) ∂μ ≤ ofReal L` gives `K - ⨍ x in s, u x ∂μ ≤ L`. -/
theorem sub_setAverage_le_of_setLAverage_ofReal_sub_le
    {μ : Measure α} {s : Set α} {u : α → ℝ} {K L : ℝ}
    (h0 : μ s ≠ 0) (hfin : μ s ≠ ∞) (hu : IntegrableOn u s μ) (hL : 0 ≤ L)
    (h : ⨍⁻ x in s, ENNReal.ofReal (K - u x) ∂μ ≤ ENNReal.ofReal L) :
    K - ⨍ x in s, u x ∂μ ≤ L := by
  have hint : IntegrableOn (fun x => K - u x) s μ := (integrableOn_const hfin).sub hu
  have hmax : IntegrableOn (fun x => max (K - u x) 0) s μ := hint.sup integrableOn_zero
  rw [← setAverage_const h0 hfin K, ← setAverage_fun_sub (integrableOn_const hfin) hu]
  refine le_trans ?_ <| (ENNReal.ofReal_le_ofReal_iff hL).1 <|
    (ofReal_setAverage hmax (.of_forall fun _ => le_max_right _ _)).trans_le ?_
  · rw [setAverage_eq, setAverage_eq]
    exact smul_le_smul_of_nonneg_left (integral_mono hint hmax fun x => le_max_left _ _)
      (by positivity)
  · simpa [ENNReal.ofReal_max, setLAverage_eq] using h

end MeasureTheory

end
