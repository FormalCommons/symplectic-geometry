/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Complex.Basic

/-!
# The indicator function of a disc is holomorphic off its boundary circle

The function `ℂ → ℂ` equal to `1` on the open disc `‖z‖ < ρ` and to `0` outside it is locally
constant away from the circle `‖z‖ = ρ`, hence complex differentiable there
(`Complex.differentiableOn_ite_norm_lt`). It is the holomorphic function whose functional
calculus gives, for a spectrum that misses the circle, the Riesz idempotent of
its part inside the disc.
-/

public section

/-- The function equal to `1` on the open disc `‖z‖ < ρ` and to `0` outside it is holomorphic
off the circle `‖z‖ = ρ`. -/
theorem Complex.differentiableOn_ite_norm_lt (ρ : ℝ) :
    DifferentiableOn ℂ (fun z : ℂ ↦ if ‖z‖ < ρ then (1 : ℂ) else 0) {z | ‖z‖ ≠ ρ} := by
  intro z hz
  rcases lt_or_gt_of_ne hz with hz | hz
  · refine (differentiableAt_const (1 : ℂ)).congr_of_eventuallyEq ?_ |>.differentiableWithinAt
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
    exact ite_eq_left hw
  · refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq ?_ |>.differentiableWithinAt
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    exact ite_eq_right (not_lt.mpr hw.le)

end
