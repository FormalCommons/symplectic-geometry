/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Norms of the derivatives of a product

For scalar functions `f g : E → 𝕜` on a normed space, Mathlib's `fderiv_mul`
and Tau Ceti's second-order product rule `TauCeti.fderiv_fderiv_mul_apply` give the derivatives of
`f * g`. This file turns them into bounds on operator norms:

* `‖D(f * g)(x)‖ ≤ ‖f x‖ ‖Dg(x)‖ + ‖g x‖ ‖Df(x)‖`
  (`SymplecticGeometry.norm_fderiv_mul_le`);
* `‖D²(f * g)(x)‖ ≤ ‖f x‖ ‖D²g(x)‖ + ‖g x‖ ‖D²f(x)‖ + 2 ‖Df(x)‖ ‖Dg(x)‖`
  (`SymplecticGeometry.norm_fderiv_fderiv_mul_le`).
-/

public section

namespace SymplecticGeometry

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : E → 𝕜} {x : E}

/-- **The derivative of a product.** For `f` and `g` differentiable at `x`, the derivative of
`f * g` at `x` has norm at most `‖f x‖ ‖Dg(x)‖ + ‖g x‖ ‖Df(x)‖`. -/
theorem norm_fderiv_mul_le (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    ‖fderiv 𝕜 (f * g) x‖ ≤ ‖f x‖ * ‖fderiv 𝕜 g x‖ + ‖g x‖ * ‖fderiv 𝕜 f x‖ := by
  rw [fderiv_mul hf hg]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> exact (norm_smul _ _).le

/-- **The second derivative of a product.** For `f` and `g` of class `C²` at `x`, the second
derivative of `f * g` at `x` has norm at most
`‖f x‖ ‖D²g(x)‖ + ‖g x‖ ‖D²f(x)‖ + 2 ‖Df(x)‖ ‖Dg(x)‖`. -/
theorem norm_fderiv_fderiv_mul_le (hf : ContDiffAt 𝕜 2 f x) (hg : ContDiffAt 𝕜 2 g x) :
    ‖fderiv 𝕜 (fderiv 𝕜 (f * g)) x‖ ≤
      ‖f x‖ * ‖fderiv 𝕜 (fderiv 𝕜 g) x‖ + ‖g x‖ * ‖fderiv 𝕜 (fderiv 𝕜 f) x‖ +
        2 * (‖fderiv 𝕜 f x‖ * ‖fderiv 𝕜 g x‖) := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v w ↦ ?_
  rw [TauCeti.fderiv_fderiv_mul_apply hf hg]
  have h₁ : ‖f x * fderiv 𝕜 (fderiv 𝕜 g) x v w‖ ≤
      ‖f x‖ * ‖fderiv 𝕜 (fderiv 𝕜 g) x‖ * ‖v‖ * ‖w‖ := by
    rw [mul_assoc, mul_assoc]
    exact (norm_mul_le _ _).trans (by
      gcongr; rw [← mul_assoc]; exact (fderiv 𝕜 (fderiv 𝕜 g) x).le_opNorm₂ v w)
  have h₂ : ‖g x * fderiv 𝕜 (fderiv 𝕜 f) x v w‖ ≤
      ‖g x‖ * ‖fderiv 𝕜 (fderiv 𝕜 f) x‖ * ‖v‖ * ‖w‖ := by
    rw [mul_assoc, mul_assoc]
    exact (norm_mul_le _ _).trans (by
      gcongr; rw [← mul_assoc]; exact (fderiv 𝕜 (fderiv 𝕜 f) x).le_opNorm₂ v w)
  have h₃ : ‖fderiv 𝕜 f x v * fderiv 𝕜 g x w‖ ≤
      ‖fderiv 𝕜 f x‖ * ‖fderiv 𝕜 g x‖ * ‖v‖ * ‖w‖ :=
    (norm_mul_le _ _).trans ((mul_le_mul ((fderiv 𝕜 f x).le_opNorm v)
      ((fderiv 𝕜 g x).le_opNorm w) (norm_nonneg _) (by positivity)).trans_eq (by ring))
  have h₄ : ‖fderiv 𝕜 g x v * fderiv 𝕜 f x w‖ ≤
      ‖fderiv 𝕜 f x‖ * ‖fderiv 𝕜 g x‖ * ‖v‖ * ‖w‖ :=
    (norm_mul_le _ _).trans ((mul_le_mul ((fderiv 𝕜 g x).le_opNorm v)
      ((fderiv 𝕜 f x).le_opNorm w) (norm_nonneg _) (by positivity)).trans_eq (by ring))
  calc _ ≤ ‖f x * fderiv 𝕜 (fderiv 𝕜 g) x v w‖ + ‖g x * fderiv 𝕜 (fderiv 𝕜 f) x v w‖ +
        ‖fderiv 𝕜 f x v * fderiv 𝕜 g x w‖ + ‖fderiv 𝕜 g x v * fderiv 𝕜 f x w‖ :=
        norm_add₄_le
    _ ≤ _ := by linear_combination h₁ + h₂ + h₃ + h₄

end SymplecticGeometry

end
