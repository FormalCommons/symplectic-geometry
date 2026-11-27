/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.JetNorm
import TauCeti.Analysis.PDE.HeatKernel.Derivatives

/-!
# Jet norms of Gaussians

On a real inner product space, the jet norms of the Gaussian `z ↦ exp (-(a * ‖z‖ ^ 2))`, for
`a ≥ 0`, are at most a constant times the Gaussian `exp (-(a * ‖z‖ ^ 2) / 2)`
(`SymplecticGeometry.exists_jetNormAt_exp_neg_mul_norm_sq_le`). This sums over the orders the
bound of each derivative, Tau Ceti's `TauCeti.exists_norm_iteratedFDeriv_exp_neg_mul_norm_sq_le`.
-/

public section

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For `a ≥ 0` and every order `r`, the `r`-jet norm of the Gaussian `z ↦ exp (-(a * ‖z‖ ^ 2))`
is at most a constant times the Gaussian `exp (-(a * ‖z‖ ^ 2) / 2)`. -/
theorem exists_jetNormAt_exp_neg_mul_norm_sq_le (r : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ∃ C, ∀ z : E, jetNormAt ℝ r (fun z : E ↦ Real.exp (-(a * ‖z‖ ^ 2))) z ≤
      C * Real.exp (-(a * ‖z‖ ^ 2) / 2) := by
  choose C hC using fun j ↦ TauCeti.exists_norm_iteratedFDeriv_exp_neg_mul_norm_sq_le (E := E) j
  refine ⟨∑ j ∈ Finset.range (r + 1), C j * √a ^ j, fun z ↦ ?_⟩
  rw [jetNormAt_def, Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ ↦ hC j a ha z

end SymplecticGeometry

end
