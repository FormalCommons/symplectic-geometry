/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The derivative of the logarithm of a function on a manifold

For a real function `g` on a manifold, differentiable at `x` with `g x ≠ 0`, the derivative of
`y ↦ log (g y)` at `x` is `(g x)⁻¹ • dg_x` (`mvfderiv_log_comp`), by Tau Ceti's chain rule
`TauCeti.mvfderiv_scalar_comp` and `Real.deriv_log`. So `log ∘ g` and `g` have the same critical
points away from the zeros of `g` (`mvfderiv_log_comp_eq_zero_iff`), as for the squared norm of a
section of a Hermitian line bundle and its logarithm.
-/

public section

open scoped Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {g : M → ℝ} {x : M}

/-- The derivative of `y ↦ log (g y)` at a point `x` where `g` is differentiable and nonzero is
`(g x)⁻¹ • dg_x`. -/
theorem mvfderiv_log_comp (hg : MDifferentiableAt I 𝓘(ℝ) g x) (hx : g x ≠ 0) :
    mvfderiv I (fun y ↦ Real.log (g y)) x = (g x)⁻¹ • mvfderiv I g x := by
  rw [← Real.deriv_log]
  exact TauCeti.mvfderiv_scalar_comp hg (Real.differentiableAt_log hx)

/-- At a point `x` where `g` is differentiable and nonzero, `y ↦ log (g y)` is critical exactly
when `g` is. -/
theorem mvfderiv_log_comp_eq_zero_iff (hg : MDifferentiableAt I 𝓘(ℝ) g x) (hx : g x ≠ 0) :
    mvfderiv I (fun y ↦ Real.log (g y)) x = 0 ↔ mvfderiv I g x = 0 := by
  rw [mvfderiv_log_comp hg hx, smul_eq_zero, or_iff_right (inv_ne_zero hx)]

end
