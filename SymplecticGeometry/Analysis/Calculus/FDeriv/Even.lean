/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# The derivative of an even function at the origin

Over a field `𝕜` of characteristic zero, an even function `f : E → F` (`f (-x) = f x`) has
derivative `0` at `0` (`Function.Even.fderiv_zero`): composing with `-id` changes the derivative
at `0` by a sign (Mathlib's `fderiv_comp_smul` with `c = -1`) and leaves `f` unchanged. If `f` is
not differentiable at `0`, its `fderiv` there is `0` by convention, so no hypothesis is needed.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over a field of characteristic zero, the derivative of an even function at the origin is
zero. -/
theorem Function.Even.fderiv_zero {f : E → F} (hf : f.Even) : fderiv 𝕜 f 0 = 0 := by
  have h := fderiv_comp_smul (𝕜 := 𝕜) (f := f) (x := 0) (-1)
  simp only [neg_smul, one_smul, hf _, smul_zero] at h
  have h2 : (2 : 𝕜) • fderiv 𝕜 f 0 = 0 := by
    rw [two_smul]
    nth_rw 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
