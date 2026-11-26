/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.CircleAverage
import SymplecticGeometry.MeasureTheory.Integral.Average

/-!
# Circle averages and lower averages over a parameter interval

Mathlib's `Real.circleAverage f c r` is the interval average of `θ ↦ f (circleMap c r θ)` over
`[0, 2 * π]` (`Real.circleAverage_eq_intervalAverage`). This file relates it to the lower average
of `ENNReal.ofReal (L - f (circleMap c r θ))` over `Ioc 0 (2 * π)` when `f ≤ L` at almost every
point of the circle.

## Main results

* `Real.setLAverage_ofReal_sub_circleMap`: for a circle-integrable `f` bounded above by `L`
  almost everywhere on the circle, the lower average of `ofReal (L - f)` over the circle is
  `ofReal (L - circleAverage f c r)`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Real

/-- If `f` is circle-integrable and `f ≤ L` at almost every point of the circle of radius `r`
about `c`, then the lower average of `ENNReal.ofReal (L - f)` over that circle is
`ENNReal.ofReal (L - circleAverage f c r)`. -/
theorem setLAverage_ofReal_sub_circleMap {f : ℂ → ℝ} {c : ℂ} {r L : ℝ}
    (hf : CircleIntegrable f c r)
    (hL : ∀ᵐ θ ∂(volume.restrict (Ioc 0 (2 * π))), f (circleMap c r θ) ≤ L) :
    ⨍⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (L - f (circleMap c r θ)) =
      ENNReal.ofReal (L - circleAverage f c r) := by
  rw [setLAverage_ofReal_sub_eq (by simp [pi_pos]) measure_Ioc_lt_top.ne
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 hf) hL,
    circleAverage_eq_intervalAverage, uIoc_of_le two_pi_pos.le]

end Real

end
