/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Constructions.UnitInterval
import TauCeti.MeasureTheory.Constructions.UnitInterval

/-!
# Integrals over the unit interval

An interval integral over `[0, a]` is the integral over the unit interval `unitInterval`, with
its volume measure, of the rescaled function `t ↦ a • h (a * t)`. This extends Tau Ceti's
`TauCeti.intervalIntegral_eq_integral_unitInterval`, the case `a = 1`, and lets results about
parametric integrals over a compact parameter space, such as Tau Ceti's
`TauCeti.contDiffOn_integral_smul_of_contDiffOn`, apply to integrals over `[0, a]`.
-/

public section

open MeasureTheory

namespace SymplecticGeometry

/-- An interval integral over `[0, a]` is the integral over the unit interval of the rescaled
function `t ↦ a • h (a * t)`. -/
theorem intervalIntegral_eq_integral_unitInterval_smul {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (a : ℝ) (h : ℝ → G) :
    ∫ θ in 0..a, h θ = ∫ t : unitInterval, a • h (a * t) := by
  rw [integral_smul, ← TauCeti.intervalIntegral_eq_integral_unitInterval (fun t ↦ h (a * t)),
    intervalIntegral.smul_integral_comp_mul_left, mul_zero, mul_one]

end SymplecticGeometry

end
