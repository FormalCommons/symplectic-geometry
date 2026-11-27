/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The norm of the gradient

On a complete inner product space over `ℝ` or `ℂ`, the gradient of a function at a point is the
vector that the Riesz isomorphism `InnerProductSpace.toDual` sends to the Fréchet derivative there.
That isomorphism is an isometry, so the gradient and the derivative have the same norm
(`norm_gradient`).
-/

public section

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The gradient of `f` at `x` has the norm of the Fréchet derivative of `f` at `x`. -/
@[simp]
theorem norm_gradient (f : F → 𝕜) (x : F) : ‖gradient f x‖ = ‖fderiv 𝕜 f x‖ := by
  rw [← toDual_gradient, LinearIsometryEquiv.norm_map]

end
