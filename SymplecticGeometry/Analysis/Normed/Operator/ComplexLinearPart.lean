/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
import TauCeti.Analysis.Normed.Module.RCLike.Basic

/-!
# Bounds for the complex-linear and complex-antilinear parts of an operator

For a continuous real-linear operator `Ψ` between complex normed spaces, Tau Ceti's
`ContinuousLinearMap.complexLinearPart` and `ContinuousLinearMap.complexAntilinearPart` both have
operator norm at most `‖Ψ‖` (`ContinuousLinearMap.norm_complexLinearPart_le`,
`ContinuousLinearMap.norm_complexAntilinearPart_le`), with pointwise forms, and the value of the
complex-antilinear part at a fixed vector is continuous in `Ψ`
(`ContinuousLinearMap.continuous_complexAntilinearPart_apply`).

The norm bounds follow the bound in the proof of Tau Ceti's
`ContinuousLinearMap.continuous_complexAntilinearPart`.
-/

public section

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- The complex-linear part of a real-linear operator has norm at most that of the operator. -/
theorem norm_complexLinearPart_le (Ψ : E →L[ℝ] F) :
    ‖Ψ.complexLinearPart‖ ≤ ‖Ψ‖ := by
  refine opNorm_le_bound _ (norm_nonneg Ψ) fun v ↦ ?_
  have h := Ψ.le_opNorm_of_le (x := Complex.I • v) (c := ‖v‖) (by simp [norm_smul])
  rw [complexLinearPart_apply, sub_eq_add_neg]
  exact TauCeti.norm_two_inv_smul_add_le (𝕜 := ℝ) (Ψ.le_opNorm v) (by simpa [norm_smul] using h)

/-- The complex-antilinear part of a real-linear operator has norm at most that of the
operator. -/
theorem norm_complexAntilinearPart_le (Ψ : E →L[ℝ] F) :
    ‖Ψ.complexAntilinearPart‖ ≤ ‖Ψ‖ := by
  refine opNorm_le_bound _ (norm_nonneg Ψ) fun v ↦ ?_
  have h := Ψ.le_opNorm_of_le (x := Complex.I • v) (c := ‖v‖) (by simp [norm_smul])
  rw [complexAntilinearPart_apply]
  exact TauCeti.norm_two_inv_smul_add_le (𝕜 := ℝ) (Ψ.le_opNorm v) (by simpa [norm_smul] using h)

/-- Pointwise form of `ContinuousLinearMap.norm_complexLinearPart_le`. -/
theorem norm_complexLinearPart_apply_le (Ψ : E →L[ℝ] F) (v : E) :
    ‖Ψ.complexLinearPart v‖ ≤ ‖Ψ‖ * ‖v‖ :=
  (Ψ.complexLinearPart.le_opNorm v).trans (by gcongr; exact Ψ.norm_complexLinearPart_le)

/-- Pointwise form of `ContinuousLinearMap.norm_complexAntilinearPart_le`. -/
theorem norm_complexAntilinearPart_apply_le (Ψ : E →L[ℝ] F) (v : E) :
    ‖Ψ.complexAntilinearPart v‖ ≤ ‖Ψ‖ * ‖v‖ :=
  (Ψ.complexAntilinearPart.le_opNorm v).trans (by gcongr; exact Ψ.norm_complexAntilinearPart_le)

/-- The value of the complex-antilinear part at a fixed vector depends continuously on the
operator. -/
theorem continuous_complexAntilinearPart_apply (v : E) :
    Continuous fun Ψ : E →L[ℝ] F ↦ Ψ.complexAntilinearPart v := by
  simp only [complexAntilinearPart_apply]
  fun_prop

end ContinuousLinearMap

end
