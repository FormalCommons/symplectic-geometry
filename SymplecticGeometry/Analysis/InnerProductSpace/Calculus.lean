/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The derivative of the diffeomorphism onto a ball at the origin

Mathlib's `OpenPartialHomeomorph.univBall c r` maps a real inner product space `E` onto the open
ball of radius `r > 0` about `c`, by `x ↦ r • (√(1 + ‖x‖²))⁻¹ • x + c`
(`OpenPartialHomeomorph.univBall_apply_of_pos`), and is smooth
(`OpenPartialHomeomorph.contDiff_univBall`). Its derivative at `0` is `r • id`
(`OpenPartialHomeomorph.hasFDerivAt_univBall_zero`), since the scalar factor
`(√(1 + ‖x‖²))⁻¹` is `1` at `0`.
-/

public section

namespace OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For `r > 0`, `univBall c r` is `x ↦ r • (√(1 + ‖x‖²))⁻¹ • x + c`. -/
theorem univBall_apply_of_pos (c : E) {r : ℝ} (hr : 0 < r) (x : E) :
    univBall c r x = r • (√(1 + ‖x‖ ^ 2))⁻¹ • x + c := by
  simp [univBall, hr, OpenPartialHomeomorph.trans', PartialEquiv.trans', univUnitBall_apply]

/-- For `r > 0`, the derivative of `univBall c r` at `0` is `r • id`. -/
theorem hasFDerivAt_univBall_zero (c : E) {r : ℝ} (hr : 0 < r) :
    HasFDerivAt (univBall c r) (r • ContinuousLinearMap.id ℝ E) 0 := by
  have h1 : DifferentiableAt ℝ (fun x : E ↦ 1 + ‖x‖ ^ 2) 0 :=
    (differentiableAt_const _).add ((contDiff_norm_sq ℝ (n := 1)).differentiable one_ne_zero 0)
  have hs : DifferentiableAt ℝ (fun x : E ↦ (√(1 + ‖x‖ ^ 2))⁻¹) 0 :=
    (h1.sqrt (by simp)).inv (by simp)
  rw [funext (univBall_apply_of_pos c hr)]
  refine ((((hs.hasFDerivAt.smul (hasFDerivAt_id (0 : E))).const_smul r).add_const c)).congr_fderiv
    ?_
  simp

end OpenPartialHomeomorph

end
