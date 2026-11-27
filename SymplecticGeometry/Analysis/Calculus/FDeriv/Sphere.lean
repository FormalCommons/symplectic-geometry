/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs

import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Derivatives of functions that are constant on a sphere

Let `F` be a complete real inner product space and `g : F → ℝ` be strictly differentiable at a
point `x ≠ 0`. If `g` is constant on the sphere of radius `‖x‖` about the origin, then its
derivative at `x` vanishes on the orthogonal complement of `x`, the tangent space of the sphere
at `x` (`HasStrictFDerivAt.apply_eq_zero_of_inner_eq_zero`). The point `x` is then an extremum
of `g` on the level set `{y | ‖y‖ ^ 2 = ‖x‖ ^ 2}`, and the proof is Mathlib's Lagrange multiplier
theorem `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d` for the constraint
`y ↦ ‖y‖ ^ 2`, whose derivative at `x` is `2 ⟪x, ·⟫`.
-/

public section

open ContinuousLinearMap
open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- If `g : F → ℝ` is strictly differentiable at a point `x ≠ 0` of a complete real inner
product space and constant on the sphere of radius `‖x‖` about the origin, then its derivative
at `x` vanishes on every vector orthogonal to `x`. -/
theorem HasStrictFDerivAt.apply_eq_zero_of_inner_eq_zero {g : F → ℝ} {g' : StrongDual ℝ F}
    {x : F} (hg : HasStrictFDerivAt g g' x) (hx : x ≠ 0) (hc : ∀ y, ‖y‖ = ‖x‖ → g y = g x)
    {v : F} (hv : ⟪x, v⟫_ℝ = 0) : g' v = 0 := by
  have hextr : IsLocalExtrOn g {y | ‖y‖ ^ 2 = ‖x‖ ^ 2} x :=
    .inl <| Filter.eventually_inf_principal.2 <| .of_forall fun y hy ↦
      (hc y ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hy)).ge
  obtain ⟨a, b, hab, h⟩ :=
    hextr.exists_multipliers_of_hasStrictFDerivAt_1d (hasStrictFDerivAt_norm_sq x) hg
  have hv' := congr($h v)
  have hx' := congr($h x)
  simp only [add_apply, smul_apply, zero_apply, innerSL_apply_apply, hv, real_inner_self_eq_norm_sq,
    smul_eq_mul] at hv' hx'
  rcases eq_or_ne b 0 with rfl | hb
  · have ha : a ≠ 0 := fun ha ↦ hab (by simp [ha])
    have : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    simp_all
  · simpa [hb] using hv'
