/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Circle averages as averages over a parameter interval

Mathlib's `Real.circleAverage f c r` is an interval average of `θ ↦ f (circleMap c r θ)` over
`[0, 2 * π]`. This file writes it as the set average over `Ioc 0 (2 * π)`, and relates it to the
lower average of `ENNReal.ofReal (L - f (circleMap c r θ))` when `f ≤ L` at almost every point of
the circle.

## Main results

* `Real.setAverage_Ioc_circleMap_eq_circleAverage`: a circle average as an average over
  `Ioc 0 (2 * π)`.
* `Real.setLAverage_ofReal_sub_circleMap`: for a circle-integrable `f` bounded above by `L`
  almost everywhere on the circle, the lower average of `ofReal (L - f)` over the circle is
  `ofReal (L - circleAverage f c r)`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Real

/-- The circle average of `f` is its average, against `volume`, over the parameters
`θ ∈ Ioc 0 (2 * π)` of the circle. -/
theorem setAverage_Ioc_circleMap_eq_circleAverage (f : ℂ → ℝ) (c : ℂ) (r : ℝ) :
    ⨍ θ in Ioc 0 (2 * π), f (circleMap c r θ) = circleAverage f c r := by
  rw [circleAverage_eq_intervalAverage, interval_average_eq_div, setAverage_eq,
    intervalIntegral.integral_of_le two_pi_pos.le, volume_real_Ioc_of_le two_pi_pos.le,
    sub_zero, smul_eq_mul, inv_mul_eq_div]

/-- If `f` is circle-integrable and `f ≤ L` at almost every point of the circle of radius `r`
about `c`, then the lower average of `ENNReal.ofReal (L - f)` over that circle is
`ENNReal.ofReal (L - circleAverage f c r)`. -/
theorem setLAverage_ofReal_sub_circleMap {f : ℂ → ℝ} {c : ℂ} {r L : ℝ}
    (hf : CircleIntegrable f c r)
    (hL : ∀ᵐ θ ∂(volume.restrict (Ioc 0 (2 * π))), f (circleMap c r θ) ≤ L) :
    ⨍⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (L - f (circleMap c r θ)) =
      ENNReal.ofReal (L - circleAverage f c r) := by
  have hIoc : volume (Ioc 0 (2 * π)) ≠ ∞ := measure_Ioc_lt_top.ne
  have hint : IntegrableOn (fun θ => f (circleMap c r θ)) (Ioc 0 (2 * π)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 hf
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 (2 * π))] fun θ => L - f (circleMap c r θ) := by
    filter_upwards [hL] with θ hθ
    exact sub_nonneg.2 hθ
  have hint' : IntegrableOn (fun θ => L - f (circleMap c r θ)) (Ioc 0 (2 * π)) :=
    (integrableOn_const hIoc).sub hint
  rw [setLAverage_eq, ← ofReal_setAverage hint' hnn,
    setAverage_fun_sub (integrableOn_const hIoc) hint,
    setAverage_const (by simp [pi_pos]) hIoc, setAverage_Ioc_circleMap_eq_circleAverage]

end Real

end
