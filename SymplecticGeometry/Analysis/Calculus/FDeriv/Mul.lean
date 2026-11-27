/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Bilinear

/-!
# Norms of the derivatives of a product

For functions `f g : E → 𝔸` from a normed space to a normed commutative algebra, this file bounds
the operator norms of the first two derivatives of `f * g` at a point:

* `‖D(f * g)(x)‖ ≤ ‖f x‖ ‖Dg(x)‖ + ‖g x‖ ‖Df(x)‖`
  (`SymplecticGeometry.norm_fderiv_mul_le`), from Mathlib's `fderiv_mul`;
* `‖D²(f * g)(x)‖ ≤ ‖f x‖ ‖D²g(x)‖ + ‖g x‖ ‖D²f(x)‖ + 2 ‖Df(x)‖ ‖Dg(x)‖`
  (`SymplecticGeometry.norm_fderiv_fderiv_mul_le`), the case `n = 2` of Tau Ceti's Leibniz bound
  at a point, `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_contDiffAt`, for the
  multiplication `ContinuousLinearMap.mul 𝕜 𝔸`, written for curried second derivatives with
  `TauCeti.norm_fderiv_fderiv`.
-/

public section

namespace SymplecticGeometry

variable {𝕜 E 𝔸 : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedCommRing 𝔸] [NormedAlgebra 𝕜 𝔸] {f g : E → 𝔸} {x : E}

/-- **The derivative of a product.** For `f` and `g` differentiable at `x`, the derivative of
`f * g` at `x` has norm at most `‖f x‖ ‖Dg(x)‖ + ‖g x‖ ‖Df(x)‖`. -/
theorem norm_fderiv_mul_le (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    ‖fderiv 𝕜 (f * g) x‖ ≤ ‖f x‖ * ‖fderiv 𝕜 g x‖ + ‖g x‖ * ‖fderiv 𝕜 f x‖ := by
  rw [fderiv_mul hf hg]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_ <;>
    rw [smul_apply, smul_eq_mul, mul_assoc] <;>
    exact (norm_mul_le _ _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)

/-- **The second derivative of a product.** For `f` and `g` of class `C²` at `x`, the second
derivative of `f * g` at `x` has norm at most
`‖f x‖ ‖D²g(x)‖ + ‖g x‖ ‖D²f(x)‖ + 2 ‖Df(x)‖ ‖Dg(x)‖`. -/
theorem norm_fderiv_fderiv_mul_le (hf : ContDiffAt 𝕜 2 f x) (hg : ContDiffAt 𝕜 2 g x) :
    ‖fderiv 𝕜 (fderiv 𝕜 (f * g)) x‖ ≤
      ‖f x‖ * ‖fderiv 𝕜 (fderiv 𝕜 g) x‖ + ‖g x‖ * ‖fderiv 𝕜 (fderiv 𝕜 f) x‖ +
        2 * (‖fderiv 𝕜 f x‖ * ‖fderiv 𝕜 g x‖) := by
  have h := (ContinuousLinearMap.mul 𝕜 𝔸).norm_iteratedFDeriv_le_of_bilinear_of_contDiffAt
    hf hg (n := 2) le_rfl
  simp only [ContinuousLinearMap.mul_apply', Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose, norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one, ← TauCeti.norm_fderiv_fderiv,
    Nat.cast_ofNat, Nat.cast_one, zero_add, one_mul, Nat.reduceAdd, Nat.reduceSub,
    Nat.sub_zero, Nat.add_one_sub_one] at h
  rw [Pi.mul_def]
  have hB := ContinuousLinearMap.opNorm_mul_le 𝕜 𝔸
  refine (h.trans (mul_le_of_le_one_left (by positivity) hB)).trans_eq ?_
  ring

end SymplecticGeometry

end
