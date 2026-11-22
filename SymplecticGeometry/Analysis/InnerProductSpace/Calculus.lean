/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Analysis.InnerProductSpace.NormPow

/-!
# The derivative of the normalization map

Calculus facts about real inner product spaces that complement Mathlib's
`Mathlib.Analysis.InnerProductSpace.Calculus`.

* `hasFDerivAt_norm_inv_smul`: away from the origin, the map `y ↦ y / ‖y‖` onto the unit sphere
  has derivative `v ↦ v / ‖x‖ - (⟪x, v⟫ / ‖x‖ ^ 3) x` at `x`. It follows from the derivative
  `‖x‖⁻¹ ⟪x, ·⟫` of the norm, Tau Ceti's `TauCeti.hasFDerivAt_norm_of_ne`.
-/

public section

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Away from the origin, the normalization map `y ↦ ‖y‖⁻¹ • y` has derivative
`v ↦ ‖x‖⁻¹ • v - (⟪x, v⟫ / ‖x‖ ^ 3) • x` at `x`. -/
theorem hasFDerivAt_norm_inv_smul {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E ↦ ‖y‖⁻¹ • y)
      (‖x‖⁻¹ • ContinuousLinearMap.id ℝ E - (‖x‖ ^ 3)⁻¹ • (innerSL ℝ x).smulRight x) x := by
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hr := (hasDerivAt_inv hx').comp_hasFDerivAt x (TauCeti.hasFDerivAt_norm_of_ne hx)
  convert hr.smul (hasFDerivAt_id x) using 1
  · ext v
    simp
  · ext v
    simp [smul_smul, sub_eq_add_neg]
    congr 1
    ring
