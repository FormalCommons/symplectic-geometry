/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# The derivative of an even function

For an even function `f : E → F` (`f (-x) = f x`), the derivative changes sign under `x ↦ -x`:
`fderiv 𝕜 f (-x) = -fderiv 𝕜 f x` (`Function.Even.fderiv_neg`). This is Mathlib's
`fderiv_comp_smul` with `c = -1`, and needs no differentiability, since `fderiv` is `0` where `f`
is not differentiable. It is the `fderiv` counterpart of Tau Ceti's one-variable
`TauCeti.deriv_neg_eq_neg_of_eventually_even`.

At the origin this gives `fderiv 𝕜 f 0 = 0` over a field where `2 ≠ 0`
(`Function.Even.fderiv_zero`). In characteristic two every function is even, so that hypothesis
cannot be dropped.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of an even function at `-x` is the negative of its derivative at `x`. -/
theorem Function.Even.fderiv_neg {f : E → F} (hf : f.Even) (x : E) :
    fderiv 𝕜 f (-x) = -fderiv 𝕜 f x := by
  simpa [hf _] using fderiv_comp_smul (𝕜 := 𝕜) (f := f) (x := -x) (-1)

/-- Over a field where `2 ≠ 0`, the derivative of an even function at the origin is zero. -/
theorem Function.Even.fderiv_zero [NeZero (2 : 𝕜)] {f : E → F} (hf : f.Even) :
    fderiv 𝕜 f 0 = 0 := by
  have h := hf.fderiv_neg (𝕜 := 𝕜) 0
  rw [neg_zero, eq_neg_iff_add_eq_zero, ← two_smul 𝕜] at h
  exact (smul_eq_zero.1 h).resolve_left two_ne_zero
